module

public import MinCostFlow.MinRatio.PathTreeContract
public import MinCostFlow.LinkCut.SplayOps

/-!
# Numeric bounds at a lazy path-tree node

The fixed-point range from page 7 must cover both evaluated accounts
and the raw fields of a link-cut node. These bounds account for
the local reversal and lazy tag operations.
-/

public section

namespace MinCostFlow.MinRatio

open LinkCut

/-- Uniform signed magnitude bound on all raw numeric fields of a node. -/
@[expose] def PathNodeBound (B : ℤ)
    (node : SplayNode (Option PathEdgeValue) PathSummary PathTag) : Prop :=
  (∀ v, node.val = some v →
    |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B) ∧
  |node.sum.gradient| ≤ B ∧ |node.sum.length| ≤ B ∧
  (∀ z, node.sum.detector = some z → |z| ≤ B) ∧
  |node.tag.flow| ≤ B ∧ |node.tag.detector| ≤ B

private theorem fits_of_abs_le {h L : ℕ} {B z : ℤ}
    (hz : |z| ≤ B) (hroom : 2 * B < (Num.capacity h L : ℤ)) : Num.Fits h L z := by
  obtain ⟨hl, hu⟩ := abs_le.mp hz
  exact ⟨by omega, by omega⟩

/-- A uniform bound on raw node fields provides the tree contract's range premise. -/
theorem pathTreeFits_of_nodeBound {h L : ℕ} {B : ℤ} {s : PathTreeState}
    (hb : ∀ i ≤ 2 * s.n, PathNodeBound B (s.splay.nodes i))
    (hroom : 2 * B < (Num.capacity h L : ℤ)) : pathTreeFits h L s := by
  intro i hi
  obtain ⟨he, hg, hl, hd, htf, htd⟩ := hb i hi
  refine ⟨?_, ⟨fits_of_abs_le hg hroom, fits_of_abs_le hl hroom, ?_⟩,
    fits_of_abs_le htf hroom, fits_of_abs_le htd hroom⟩
  · cases hv : (s.splay.nodes i).val with
    | none => trivial
    | some v =>
      obtain ⟨h1, h2, h3, h4⟩ := he v hv
      exact ⟨fits_of_abs_le h1 hroom, fits_of_abs_le h2 hroom, fits_of_abs_le h3 hroom,
        fits_of_abs_le h4 hroom⟩
  · cases hz : (s.splay.nodes i).sum.detector with
    | none => trivial
    | some z => exact fits_of_abs_le (hd z hz) hroom

/-- Reversal preserves the uniform bound at the affected node. -/
theorem PathNodeBound.revNode {B : ℤ}
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag} {x : ℕ}
    (hb : PathNodeBound B (s.nodes x)) :
    PathNodeBound B ((s.revNode pathPayload x).nodes x) := by
  by_cases hx : x = 0
  · simpa [SplayState.revNode, hx] using hb
  rw [SplayState.revNode, ite_eq_right hx, SplayState.nodes_updateNode_self]
  obtain ⟨he, hg, hl, hd, hf, ht⟩ := hb
  refine ⟨?_, ?_, hl, hd, ?_, ht⟩
  · intro v hv
    cases hval : (s.nodes x).val with
    | none => simp [pathPayload, hval] at hv
    | some u =>
      have heq : u.reverse = v := by simpa [pathPayload, hval] using hv
      subst v
      simpa [PathEdgeValue.reverse] using he u hval
  · simpa [pathPayload, PathSummary.reverse] using hg
  · simpa [pathPayload, PathTag.reverse] using hf

/-- Applying a tag adds at most its magnitude to each affected field. -/
theorem PathNodeBound.applyTagNode {B D : ℤ}
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag} {x : ℕ} {tag : PathTag}
    (hb : PathNodeBound B (s.nodes x))
    (hf : |tag.flow| ≤ D) (hd : |tag.detector| ≤ D) :
    PathNodeBound (B + D) ((s.applyTagNode pathPayload x tag).nodes x) := by
  have hD := (abs_nonneg tag.flow).trans hf
  have hw {z : ℤ} (hz : |z| ≤ B) : |z| ≤ B + D := by omega
  have hadd {z t : ℤ} (hz : |z| ≤ B) (ht : |t| ≤ D) : |z + t| ≤ B + D :=
    (abs_add_le z t).trans (add_le_add hz ht)
  obtain ⟨he, hg, hl, hdet, htf, htd⟩ := hb
  by_cases hx : x = 0
  · rw [SplayState.applyTagNode, ite_eq_left hx]
    exact ⟨fun v hv => let h := he v hv; ⟨hw h.1, hw h.2.1, hw h.2.2.1, hw h.2.2.2⟩,
      hw hg, hw hl, fun z hz => hw (hdet z hz), hw htf, hw htd⟩
  rw [SplayState.applyTagNode, ite_eq_right hx, SplayState.nodes_updateNode_self]
  refine ⟨?_, hw hg, hw hl, ?_, ?_, ?_⟩
  · intro v hv
    cases hval : (s.nodes x).val with
    | none => simp [pathPayload, hval] at hv
    | some u =>
      have heq : u.shift tag = v := by simpa [pathPayload, hval] using hv
      subst v
      obtain ⟨h1, h2, h3, h4⟩ := he u hval
      exact ⟨hw h1, hw h2, hadd h3 hf, hadd h4 hd⟩
  · intro z hz
    cases hraw : (s.nodes x).sum.detector with
    | none => simp [pathPayload, PathSummary.shift, hraw] at hz
    | some raw =>
      have heq : raw + tag.detector = z := by
        simpa [pathPayload, PathSummary.shift, hraw] using hz
      exact heq ▸ hadd (hdet raw hraw) hd
  · exact (abs_add_le _ _).trans (add_le_add hf htf) |>.trans_eq (add_comm D B)
  · exact (abs_add_le _ _).trans (add_le_add hd htd) |>.trans_eq (add_comm D B)

/-- A lazy tag is charged by the total magnitude of its two coordinates. -/
@[expose] def pathTagMagnitude (t : PathTag) : ℤ := |t.flow| + |t.detector|

/-- Reversal leaves the charge for a pending tag unchanged. -/
theorem pathTagMagnitude_reverse (t : PathTag) :
    pathTagMagnitude t.reverse = pathTagMagnitude t := by
  simp [pathTagMagnitude, PathTag.reverse]

/-- Composing two tags charges at most the sum of their magnitudes. -/
theorem pathTagMagnitude_compose (outer inner : PathTag) :
    pathTagMagnitude (outer.compose inner) ≤
      pathTagMagnitude outer + pathTagMagnitude inner := by
  have hf := abs_add_le outer.flow inner.flow
  have hd := abs_add_le outer.detector inner.detector
  unfold pathTagMagnitude
  change |outer.flow + inner.flow| + |outer.detector + inner.detector| ≤ _
  omega

/-- Pushing a parent tag keeps its charge along a route through one child. -/
theorem pathTagMagnitude_push_le (parent child : PathTag) (remaining : ℤ) :
    pathTagMagnitude (parent.compose child) + remaining ≤
      pathTagMagnitude parent + pathTagMagnitude child + remaining :=
  add_le_add_left (pathTagMagnitude_compose parent child) remaining

/-- The physical child stores the composed tag after a lazy application. -/
theorem pathTagMagnitude_applyTagNode {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {x : ℕ} (hx : x ≠ 0) (tag : PathTag) :
    pathTagMagnitude ((s.applyTagNode pathPayload x tag).nodes x).tag ≤
      pathTagMagnitude tag + pathTagMagnitude (s.nodes x).tag := by
  rw [SplayState.applyTagNode, ite_eq_right hx, SplayState.nodes_updateNode_self]
  exact pathTagMagnitude_compose tag (s.nodes x).tag

private theorem applyTagNode_other (s : SplayState (Option PathEdgeValue) PathSummary PathTag)
    {i x : ℕ} (hne : i ≠ x) (tag : PathTag) :
    (s.applyTagNode pathPayload x tag).nodes i = s.nodes i := by
  by_cases hx : x = 0
  · rw [SplayState.applyTagNode, ite_eq_left hx]
  · rw [SplayState.applyTagNode, ite_eq_right hx, SplayState.nodes_updateNode_ne _ hne]

/-- Pushing onto the left branch does not increase the combined parent
and child tag charge. The right child is a different node or null. -/
theorem pathTagMagnitude_pushDownTag_left
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (x : ℕ)
    (hx : x ≠ 0) (hl : (s.nodes x).left ≠ 0)
    (hlx : (s.nodes x).left ≠ x) (hrx : (s.nodes x).right ≠ x)
    (hlr : (s.nodes x).left ≠ (s.nodes x).right) :
    let next := s.pushDownTag pathPayload x
    pathTagMagnitude (next.nodes x).tag +
        pathTagMagnitude (next.nodes (s.nodes x).left).tag ≤
      pathTagMagnitude (s.nodes x).tag + pathTagMagnitude (s.nodes (s.nodes x).left).tag := by
  dsimp only
  rw [SplayState.pushDownTag, ite_eq_right hx]
  dsimp only
  split
  · exact le_rfl
  · let st₀ := s.updateNode x fun cur => { cur with tag := pathPayload.idTag }
    let tag := (s.nodes x).tag
    let l := (s.nodes x).left
    let r := (s.nodes x).right
    let stL := st₀.applyTagNode pathPayload l tag
    change pathTagMagnitude ((stL.applyTagNode pathPayload r tag).nodes x).tag +
      pathTagMagnitude ((stL.applyTagNode pathPayload r tag).nodes l).tag ≤
      pathTagMagnitude tag + pathTagMagnitude (s.nodes l).tag
    rw [applyTagNode_other stL hrx.symm, applyTagNode_other stL hlr,
      applyTagNode_other st₀ hlx.symm]
    have hzero : pathTagMagnitude (st₀.nodes x).tag = 0 := by
      dsimp only [st₀]
      rw [SplayState.nodes_updateNode_self]
      simp [pathPayload, PathTag.zero, pathTagMagnitude]
    have hsame : st₀.nodes l = s.nodes l :=
      SplayState.nodes_updateNode_ne _ hlx _
    rw [hzero, zero_add]
    simpa only [hsame] using pathTagMagnitude_applyTagNode (s := st₀) (x := l) hl tag

/-- Pushing onto the right branch does not increase the combined parent
and child tag charge. The left child is a different node or null. -/
theorem pathTagMagnitude_pushDownTag_right
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (x : ℕ)
    (hx : x ≠ 0) (hr : (s.nodes x).right ≠ 0)
    (hlx : (s.nodes x).left ≠ x) (hrx : (s.nodes x).right ≠ x)
    (hlr : (s.nodes x).left ≠ (s.nodes x).right) :
    let next := s.pushDownTag pathPayload x
    pathTagMagnitude (next.nodes x).tag +
        pathTagMagnitude (next.nodes (s.nodes x).right).tag ≤
      pathTagMagnitude (s.nodes x).tag + pathTagMagnitude (s.nodes (s.nodes x).right).tag := by
  dsimp only
  rw [SplayState.pushDownTag, ite_eq_right hx]
  dsimp only
  split
  · exact le_rfl
  · let st₀ := s.updateNode x fun cur => { cur with tag := pathPayload.idTag }
    let tag := (s.nodes x).tag
    let l := (s.nodes x).left
    let r := (s.nodes x).right
    let stL := st₀.applyTagNode pathPayload l tag
    change pathTagMagnitude ((stL.applyTagNode pathPayload r tag).nodes x).tag +
      pathTagMagnitude ((stL.applyTagNode pathPayload r tag).nodes r).tag ≤
      pathTagMagnitude tag + pathTagMagnitude (s.nodes r).tag
    rw [applyTagNode_other stL hrx.symm, applyTagNode_other st₀ hlx.symm]
    have hzero : pathTagMagnitude (st₀.nodes x).tag = 0 := by
      dsimp only [st₀]
      rw [SplayState.nodes_updateNode_self]
      simp [pathPayload, PathTag.zero, pathTagMagnitude]
    have hsame : stL.nodes r = s.nodes r :=
      (applyTagNode_other st₀ hlr.symm tag).trans (SplayState.nodes_updateNode_ne _ hrx _)
    rw [hzero, zero_add]
    simpa only [hsame] using pathTagMagnitude_applyTagNode (s := stL) (x := r) hr tag

/-- Sum the pending tag magnitudes along a physical auxiliary-tree route. -/
@[expose] def pathTagRouteMagnitude
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (route : List ℕ) : ℤ :=
  (route.map fun x => pathTagMagnitude (s.nodes x).tag).sum

private theorem pushDownTag_other
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) {i x : ℕ}
    (hx : i ≠ x) (hl : i ≠ (s.nodes x).left) (hr : i ≠ (s.nodes x).right) :
    (s.pushDownTag pathPayload x).nodes i = s.nodes i := by
  by_cases hz : x = 0
  · rw [SplayState.pushDownTag, ite_eq_left hz]
  · rw [SplayState.pushDownTag, ite_eq_right hz]
    dsimp only
    split
    · rfl
    · rw [applyTagNode_other _ hr, applyTagNode_other _ hl,
        SplayState.nodes_updateNode_ne _ hx]

/-- A push leaves the tag charges of route nodes below the two children unchanged. -/
theorem pathTagRouteMagnitude_pushDownTag_frame
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (x : ℕ)
    (route : List ℕ)
    (hrest : ∀ i ∈ route, i ≠ x ∧ i ≠ (s.nodes x).left ∧ i ≠ (s.nodes x).right) :
    pathTagRouteMagnitude (s.pushDownTag pathPayload x) route = pathTagRouteMagnitude s route := by
  unfold pathTagRouteMagnitude
  congr 1
  apply List.map_congr_left
  intro i hi
  obtain ⟨hx, hl, hr⟩ := hrest i hi
  rw [pushDownTag_other s hx hl hr]

/-- Pushing a tag down does not raise the cumulative charge along either
branch of a route. The route suffix is unchanged by the push. -/
theorem pathTagRouteMagnitude_pushDownTag_le
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (x child : ℕ)
    (route : List ℕ)
    (hx : x ≠ 0) (hc : child ≠ 0)
    (hchild : child = (s.nodes x).left ∨ child = (s.nodes x).right)
    (hlx : (s.nodes x).left ≠ x) (hrx : (s.nodes x).right ≠ x)
    (hlr : (s.nodes x).left ≠ (s.nodes x).right)
    (hrest : ∀ i ∈ route, i ≠ x ∧ i ≠ (s.nodes x).left ∧ i ≠ (s.nodes x).right) :
    pathTagRouteMagnitude (s.pushDownTag pathPayload x) (x :: child :: route) ≤
      pathTagRouteMagnitude s (x :: child :: route) := by
  have hframe := pathTagRouteMagnitude_pushDownTag_frame s x route hrest
  have hcharge : pathTagMagnitude ((s.pushDownTag pathPayload x).nodes x).tag +
      pathTagMagnitude ((s.pushDownTag pathPayload x).nodes child).tag ≤
      pathTagMagnitude (s.nodes x).tag + pathTagMagnitude (s.nodes child).tag := by
    rcases hchild with rfl | rfl
    · exact pathTagMagnitude_pushDownTag_left s x hx hc hlx hrx hlr
    · exact pathTagMagnitude_pushDownTag_right s x hx hc hlx hrx hlr
  change _ + (_ + pathTagRouteMagnitude (s.pushDownTag pathPayload x) route) ≤
    _ + (_ + pathTagRouteMagnitude s route)
  rw [hframe]
  dsimp only
  omega

private theorem tagCharge_rotateRightRoot
    (weight : ℕ → ℤ) (p x target : ℕ) (a b c : AuxTree)
    (hnd : (AuxTree.node p (.node x a b) c).toList.Nodup)
    (hp : weight p = 0) (hx : weight x = 0) :
    (((AuxTree.node x a (.node p b c)).pathTo target).map weight).sum =
      (((AuxTree.node p (.node x a b) c).pathTo target).map weight).sum := by
  obtain ⟨hl, hpl, _, hpc, hdis⟩ := AuxTree.nodup_node_unfold hnd
  obtain ⟨_, hxa, _, hxb, hab⟩ := AuxTree.nodup_node_unfold hl
  have hpx : p ≠ x := fun h => hpl (by simp [AuxTree.toList, h])
  have hpa : p ∉ a.toList := fun h => hpl (by simp [AuxTree.toList, h])
  have hpb : p ∉ b.toList := fun h => hpl (by simp [AuxTree.toList, h])
  have hxc : x ∉ c.toList := fun h => hdis _ (by simp [AuxTree.toList]) h
  by_cases htp : target = p
  · subst target
    simp [AuxTree.pathTo, AuxTree.toList, hpx, hpa, hp, hx]
  by_cases htx : target = x
  · subst target
    simp [AuxTree.pathTo, AuxTree.toList, hpx.symm, hp, hx]
  by_cases ha : target ∈ a.toList
  · simp [AuxTree.pathTo, AuxTree.toList, htp, htx, ha, hp, hx]
  by_cases hb : target ∈ b.toList
  · simp [AuxTree.pathTo, AuxTree.toList, htp, htx, ha, hb, hp, hx]
  by_cases hc : target ∈ c.toList
  · simp [AuxTree.pathTo, AuxTree.toList, htp, htx, ha, hb, hc, hx]
  · simp [AuxTree.pathTo, AuxTree.toList, htp, htx, ha, hb, hc]

private theorem tagCharge_rotateLeftRoot
    (weight : ℕ → ℤ) (p x target : ℕ) (a b c : AuxTree)
    (hnd : (AuxTree.node p a (.node x b c)).toList.Nodup)
    (hp : weight p = 0) (hx : weight x = 0) :
    (((AuxTree.node x (.node p a b) c).pathTo target).map weight).sum =
      (((AuxTree.node p a (.node x b c)).pathTo target).map weight).sum := by
  obtain ⟨_, hpa, hr, hpr, hdis⟩ := AuxTree.nodup_node_unfold hnd
  obtain ⟨_, hxb, _, hxc, _⟩ := AuxTree.nodup_node_unfold hr
  have hpx : p ≠ x := fun h => hpr (by simp [AuxTree.toList, h])
  have hpc : p ∉ c.toList := fun h => hpr (by simp [AuxTree.toList, h])
  have hxa : x ∉ a.toList := fun h => hdis _ h (by simp [AuxTree.toList])
  by_cases htp : target = p
  · subst target
    simp [AuxTree.pathTo, AuxTree.toList, hpx, hp, hx]
  by_cases htx : target = x
  · subst target
    simp [AuxTree.pathTo, AuxTree.toList, hpx.symm, hxa, hxb, hp, hx]
  by_cases ha : target ∈ a.toList
  · simp [AuxTree.pathTo, AuxTree.toList, htp, htx, ha, hp, hx]
  by_cases hb : target ∈ b.toList
  · simp [AuxTree.pathTo, AuxTree.toList, htp, htx, ha, hb, hp, hx]
  by_cases hc : target ∈ c.toList
  · simp [AuxTree.pathTo, AuxTree.toList, htp, htx, ha, hb, hc, hp]
  · simp [AuxTree.pathTo, AuxTree.toList, htp, htx, ha, hb, hc]

private theorem tagCharge_rotateAt (weight : ℕ → ℤ) (t : AuxTree) (pivot target : ℕ)
    (hnd : t.toList.Nodup) (hmem : pivot ∈ t.toList)
    (hClean : ∀ u ∈ t.pathTo pivot, weight u = 0) :
    (((t.rotateAt pivot).pathTo target).map weight).sum = ((t.pathTo target).map weight).sum := by
  induction t with
  | leaf => rfl
  | node p l r ihl ihr =>
    by_cases hpx : p = pivot
    · subst pivot
      rw [AuxTree.rotateAt_root]
    obtain ⟨hln, _, hrn, _, _⟩ := AuxTree.nodup_node_unfold hnd
    have hxp := Ne.symm hpx
    have hPivot := hClean pivot (AuxTree.self_mem_pathTo hmem)
    by_cases hl : l.hasRoot pivot
    · obtain ⟨a, b, rfl⟩ := AuxTree.hasRoot_iff.mp hl
      have hp := hClean p (by simp [AuxTree.pathTo, hxp, AuxTree.toList])
      rw [AuxTree.rotateAt, ite_eq_right hpx, ite_eq_left hl]
      exact tagCharge_rotateRightRoot weight p pivot target a b r hnd hp hPivot
    by_cases hr : r.hasRoot pivot
    · obtain ⟨b, c, rfl⟩ := AuxTree.hasRoot_iff.mp hr
      have hp := hClean p (by
        by_cases hm : pivot ∈ l.toList <;> simp [AuxTree.pathTo, hxp, hm, AuxTree.toList])
      rw [AuxTree.rotateAt, ite_eq_right hpx, ite_eq_right hl, ite_eq_left hr]
      exact tagCharge_rotateLeftRoot weight p pivot target l b c hnd hp hPivot
    rw [AuxTree.rotateAt, ite_eq_right hpx, ite_eq_right hl, ite_eq_right hr]
    by_cases hm : pivot ∈ l.toList
    · rw [ite_eq_left hm]
      have hClean' u (hu : u ∈ l.pathTo pivot) : weight u = 0 :=
        hClean u (by simp [AuxTree.pathTo, hxp, hm, hu])
      have hEq := ihl hln hm hClean'
      have hPerm := AuxTree.rotateAt_toList_perm pivot l
      simp only [AuxTree.pathTo, hPerm.mem_iff]
      split
      · rfl
      · split
        · simpa only [List.map_cons, List.sum_cons] using congrArg (weight p + ·) hEq
        · rfl
    · rw [ite_eq_right hm]
      have hmr : pivot ∈ r.toList := by simpa [AuxTree.toList, hxp, hm] using hmem
      have hClean' u (hu : u ∈ r.pathTo pivot) : weight u = 0 :=
        hClean u (by simp [AuxTree.pathTo, hxp, hm, hmr, hu])
      have hEq := ihr hrn hmr hClean'
      have hPerm := AuxTree.rotateAt_toList_perm pivot r
      simp only [AuxTree.pathTo, hPerm.mem_iff]
      split
      · rfl
      · split
        · rfl
        · split
          · simpa only [List.map_cons, List.sum_cons] using congrArg (weight p + ·) hEq
          · rfl

/-- Once the rotation's ancestor tags are cleared, every route has the
same cumulative tag magnitude before and after the rotation. -/
theorem pathTagRouteMagnitude_rotate_eq
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {t : AuxTree} {pivot target : ℕ}
    (ht : SplayState.TreeInv pathPayload s t)
    (hPivot : pivot ∈ t.toList) (hRoot : pivot ≠ t.rootId)
    (hClean : ∀ u ∈ t.pathTo pivot,
      (s.nodes u).rev = false ∧ (s.nodes u).tag = pathPayload.idTag) :
    pathTagRouteMagnitude (s.rotate pathPayload pivot) ((t.rotateAt pivot).pathTo target) =
      pathTagRouteMagnitude s (t.pathTo target) := by
  obtain ⟨_, hperm, _, _, _, htags⟩ := SplayState.rotate_preserves pathPayload_laws ht hPivot hRoot hClean
  have hSame : pathTagRouteMagnitude (s.rotate pathPayload pivot) ((t.rotateAt pivot).pathTo target) =
      pathTagRouteMagnitude s ((t.rotateAt pivot).pathTo target) := by
    unfold pathTagRouteMagnitude
    congr 1
    apply List.map_congr_left
    intro u hu
    rw [(htags u (hperm.mem_iff.mp (AuxTree.mem_pathTo hu))).2]
  rw [hSame]
  apply tagCharge_rotateAt _ _ _ _ ht.nodup hPivot
  intro u hu
  rw [(hClean u hu).2]
  simp [pathTagMagnitude, pathPayload, PathTag.zero]

/-- In particular, the charge cannot increase on a route through the pivot. -/
theorem pathTagRouteMagnitude_rotate_le
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {t : AuxTree} {target pivot : ℕ}
    (ht : SplayState.TreeInv pathPayload s t) (_hTarget : target ∈ t.toList)
    (hPivot : pivot ∈ t.toList) (hRoot : pivot ≠ t.rootId)
    (_hAnc : pivot ∈ t.pathTo target)
    (hClean : ∀ u ∈ t.pathTo pivot,
      (s.nodes u).rev = false ∧ (s.nodes u).tag = pathPayload.idTag) :
    pathTagRouteMagnitude (s.rotate pathPayload pivot) ((t.rotateAt pivot).pathTo target) ≤
      pathTagRouteMagnitude s (t.pathTo target) :=
  (pathTagRouteMagnitude_rotate_eq ht hPivot hRoot hClean).le

private theorem setLeft_tag_eq
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (x child i : ℕ) :
    ((s.setLeft x child).nodes i).tag = (s.nodes i).tag := by
  by_cases h : i = x <;> simp [SplayState.setLeft, h]

private theorem setRight_tag_eq
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (x child i : ℕ) :
    ((s.setRight x child).nodes i).tag = (s.nodes i).tag := by
  by_cases h : i = x <;> simp [SplayState.setRight, h]

theorem setPar_tag_eq
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (x parent i : ℕ) :
    ((s.setPar x parent).nodes i).tag = (s.nodes i).tag := by
  by_cases h : i = x <;> simp [SplayState.setPar, h]

private theorem setPpar_tag_eq
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (x parent i : ℕ) :
    ((s.setPpar x parent).nodes i).tag = (s.nodes i).tag := by
  by_cases h : i = x <;> simp [SplayState.setPpar, h]

theorem detachRight_tag_eq
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (x i : ℕ) :
    ((s.detachRight pathPayload x).nodes i).tag = (s.nodes i).tag := by
  by_cases hx : x = 0
  · simp [SplayState.detachRight, hx]
  by_cases hr : (s.nodes x).right = 0 <;>
    simp [SplayState.detachRight, hx, hr, SplayState.pull_tag_eq,
      setRight_tag_eq, setPar_tag_eq, setPpar_tag_eq]

theorem attachRight_tag_eq
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (x child i : ℕ) :
    ((s.attachRight pathPayload x child).nodes i).tag = (s.nodes i).tag := by
  by_cases hx : x = 0
  · simp [SplayState.attachRight, hx]
  by_cases hc : child = 0 <;>
    simp [SplayState.attachRight, hx, hc, SplayState.pull_tag_eq,
      setRight_tag_eq, setPar_tag_eq, setPpar_tag_eq]

theorem pathTagRouteMagnitude_congr
    {s t : SplayState (Option PathEdgeValue) PathSummary PathTag} (route : List ℕ)
    (htags : ∀ i, (t.nodes i).tag = (s.nodes i).tag) :
    pathTagRouteMagnitude t route = pathTagRouteMagnitude s route := by
  unfold pathTagRouteMagnitude
  congr 1
  apply List.map_congr_left
  intro i _
  rw [htags i]

/-- Detaching a clean root's right subtree preserves each route charge
within that subtree. Removing the clean root changes no charge. -/
theorem pathTagRouteMagnitude_detachRight
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag} {x target : ℕ}
    {left right : AuxTree}
    (ht : SplayState.TreeInv pathPayload s (.node x left right))
    (hClean : (s.nodes x).tag = pathPayload.idTag)
    (hTarget : target ∈ right.toList) :
    pathTagRouteMagnitude (s.detachRight pathPayload x) (right.pathTo target) =
      pathTagRouteMagnitude s ((AuxTree.node x left right).pathTo target) := by
  rw [pathTagRouteMagnitude_congr _ (detachRight_tag_eq s x)]
  obtain ⟨_, _, _, hroot, hdisj⟩ := AuxTree.nodup_node_unfold ht.nodup
  have hn : target ≠ x := fun h => hroot (h ▸ hTarget)
  have hl : target ∉ left.toList := fun h => hdisj target h hTarget
  simp [AuxTree.pathTo, hn, hl, hTarget, pathTagRouteMagnitude, hClean,
    pathTagMagnitude, pathPayload, PathTag.zero]

/-- Attaching a subtree to a clean root preserves each route charge
within the attached subtree. Adding the clean root changes no charge. -/
theorem pathTagRouteMagnitude_attachRight
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag} {x target : ℕ}
    {left right : AuxTree}
    (ht : (AuxTree.node x left right).toList.Nodup)
    (hClean : (s.nodes x).tag = pathPayload.idTag)
    (hTarget : target ∈ right.toList) :
    pathTagRouteMagnitude (s.attachRight pathPayload x right.rootId)
        ((AuxTree.node x left right).pathTo target) =
      pathTagRouteMagnitude s (right.pathTo target) := by
  rw [pathTagRouteMagnitude_congr _ (attachRight_tag_eq s x right.rootId)]
  obtain ⟨_, _, _, hroot, hdisj⟩ := AuxTree.nodup_node_unfold ht
  have hn : target ≠ x := fun h => hroot (h ▸ hTarget)
  have hl : target ∉ left.toList := fun h => hdisj target h hTarget
  simp [AuxTree.pathTo, hn, hl, hTarget, pathTagRouteMagnitude, hClean,
    pathTagMagnitude, pathPayload, PathTag.zero]

/-- The root and left subtree retain their route charges under either
right splice. -/
theorem pathTagRouteMagnitude_rightSplice_retained
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag} {x target : ℕ}
    {left right : AuxTree} (ht : target = x ∨ target ∈ left.toList) :
    pathTagRouteMagnitude (s.detachRight pathPayload x) ((AuxTree.node x left .leaf).pathTo target) =
        pathTagRouteMagnitude s ((AuxTree.node x left right).pathTo target) ∧
      pathTagRouteMagnitude (s.attachRight pathPayload x right.rootId)
        ((AuxTree.node x left right).pathTo target) =
        pathTagRouteMagnitude s ((AuxTree.node x left .leaf).pathTo target) := by
  rw [pathTagRouteMagnitude_congr _ (detachRight_tag_eq s x),
    pathTagRouteMagnitude_congr _ (attachRight_tag_eq s x right.rootId)]
  rcases ht with rfl | ht
  · simp [AuxTree.pathTo]
  · by_cases hn : target = x <;> simp [AuxTree.pathTo, hn, ht]

private theorem pathTo_root_cons {t : AuxTree} {target : ℕ} (ht : target ∈ t.toList)
    (hnd : t.toList.Nodup) :
    ∃ route, t.pathTo target = t.rootId :: route ∧ t.rootId ∉ route := by
  cases t with
  | leaf => simp [AuxTree.toList] at ht
  | node x l r =>
    obtain ⟨_, hxl, _, hxr, _⟩ := AuxTree.nodup_node_unfold hnd
    by_cases hx : target = x
    · exact ⟨[], by simp [AuxTree.pathTo, AuxTree.rootId, hx], by simp⟩
    by_cases hl : target ∈ l.toList
    · exact ⟨l.pathTo target, by simp [AuxTree.pathTo, AuxTree.rootId, hx, hl],
        fun h => hxl (AuxTree.mem_pathTo h)⟩
    · have hr : target ∈ r.toList := by simpa [AuxTree.toList, hx, hl] using ht
      exact ⟨r.pathTo target, by simp [AuxTree.pathTo, AuxTree.rootId, hx, hl, hr],
        fun h => hxr (AuxTree.mem_pathTo h)⟩

/-- A tag push at an auxiliary root does not increase any live route's
cumulative bound. Distinctness of the route nodes comes from the tree
invariant. -/
theorem pathTagRouteMagnitude_pushDownTag_root_le
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {rp x target : ℕ} {left right : AuxTree}
    (hnd : (AuxTree.node x left right).toList.Nodup)
    (hsub : SplayState.SubtreeInv pathPayload s rp (.node x left right))
    (hrev : (s.nodes x).rev = false) (ha : target ∈ (AuxTree.node x left right).toList) :
    pathTagRouteMagnitude (s.pushDownTag pathPayload x) ((AuxTree.node x left right).pathTo target) ≤
      pathTagRouteMagnitude s ((AuxTree.node x left right).pathTo target) := by
  obtain ⟨hln, hxl, hrn, hxr, hdisj⟩ := AuxTree.nodup_node_unfold hnd
  have hls := hsub.2.1
  have hrs := hsub.2.2.1
  have hx := hsub.1
  by_cases hTarget : target = x
  · subst target
    have hz := (SplayState.pushDownTag_root_preserves pathPayload_laws hnd hsub hrev).2.2.1
    simp only [AuxTree.pathTo, ite_true, pathTagRouteMagnitude, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, hz]
    simp [pathTagMagnitude, pathPayload, PathTag.zero]
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have branch (a b : AuxTree) (ha : target ∈ a.toList) (hna : a.toList.Nodup)
      (hxa : x ∉ a.toList) (hnz : ∀ i ∈ a.toList, i ≠ 0) (hab : ∀ i ∈ a.toList, i ∉ b.toList) :
      ∃ route, a.pathTo target = a.rootId :: route ∧
        (∀ i ∈ route, i ≠ x ∧ i ≠ a.rootId ∧ i ≠ b.rootId) := by
    obtain ⟨route, hpath, hn⟩ := pathTo_root_cons ha hna
    refine ⟨route, hpath, fun i hi => ?_⟩
    have hm : i ∈ a.toList := AuxTree.mem_pathTo (hpath.symm ▸ List.mem_cons_of_mem _ hi)
    refine ⟨fun h => hxa (h ▸ hm), fun h => hn (h ▸ hi), fun h => ?_⟩
    by_cases hb : b = .leaf
    · subst b
      exact hnz i hm h
    · exact hab i hm (h.symm ▸ AuxTree.rootId_mem hb)

  have hleftNZ (i : ℕ) (hi : i ∈ left.toList) : i ≠ 0 :=
    SplayState.SubtreeInv_nonZero hsub (by simp [AuxTree.toList, hi])
  have hrightNZ (i : ℕ) (hi : i ∈ right.toList) : i ≠ 0 :=
    SplayState.SubtreeInv_nonZero hsub (by simp [AuxTree.toList, hi])
  have hleftRoot : left.rootId ≠ x := by
    by_cases h : left = .leaf
    · simpa [h, AuxTree.rootId] using hx.symm
    · exact fun heq => hxl (heq ▸ AuxTree.rootId_mem h)
  have hrightRoot : right.rootId ≠ x := by
    by_cases h : right = .leaf
    · simpa [h, AuxTree.rootId] using hx.symm
    · exact fun heq => hxr (heq ▸ AuxTree.rootId_mem h)
  have hRoots (hl : left ≠ .leaf) (hr : right ≠ .leaf) : left.rootId ≠ right.rootId :=
    fun h => hdisj left.rootId (AuxTree.rootId_mem hl) (h.symm ▸ AuxTree.rootId_mem hr)
  by_cases hl : target ∈ left.toList
  · have hlne : left ≠ .leaf := by intro h; simp [h, AuxTree.toList] at hl
    have hR : left.rootId ≠ right.rootId := by
      by_cases hr : right = .leaf
      · simpa [hr, AuxTree.rootId] using hleftNZ _ (AuxTree.rootId_mem hlne)
      · exact hRoots hlne hr
    obtain ⟨route, hpath, hframe⟩ := branch left right hl hln hxl hleftNZ hdisj
    simp only [AuxTree.pathTo, hTarget, ite_false, hl, ite_true, hpath]
    exact pathTagRouteMagnitude_pushDownTag_le s x left.rootId route hx
      (hleftNZ _ (AuxTree.rootId_mem hlne)) (Or.inl hls.symm)
      (hls.symm ▸ hleftRoot) (hrs.symm ▸ hrightRoot) (hls.symm ▸ hrs.symm ▸ hR)
      (by simpa only [hls, hrs] using hframe)
  · have hr : target ∈ right.toList := by simpa [AuxTree.toList, hTarget, hl] using ha
    have hrne : right ≠ .leaf := by intro h; simp [h, AuxTree.toList] at hr
    have hR : left.rootId ≠ right.rootId := by
      by_cases hl' : left = .leaf
      · simpa [hl', AuxTree.rootId] using (hrightNZ _ (AuxTree.rootId_mem hrne)).symm
      · exact hRoots hl' hrne
    obtain ⟨route, hpath, hframe⟩ := branch right left hr hrn hxr hrightNZ
      (fun i hi h => hdisj i h hi)
    simp only [AuxTree.pathTo, hTarget, ite_false, hl, hr, ite_true, hpath]
    exact pathTagRouteMagnitude_pushDownTag_le s x right.rootId route hx
      (hrightNZ _ (AuxTree.rootId_mem hrne)) (Or.inr hrs.symm)
      (hls.symm ▸ hleftRoot) (hrs.symm ▸ hrightRoot) (hls.symm ▸ hrs.symm ▸ hR)
      (fun i hi => by
        obtain ⟨hix, hir, hil⟩ := hframe i hi
        simpa only [hls, hrs] using And.intro hix (And.intro hil hir))

private theorem revNode_tag_magnitude
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (x i : ℕ) :
    pathTagMagnitude ((s.revNode pathPayload x).nodes i).tag =
      pathTagMagnitude (s.nodes i).tag := by
  by_cases hx : x = 0
  · rw [SplayState.revNode, ite_eq_left hx]
  rw [SplayState.revNode, ite_eq_right hx]
  by_cases hi : i = x
  · subst i
    rw [SplayState.nodes_updateNode_self]
    exact pathTagMagnitude_reverse _
  · rw [SplayState.nodes_updateNode_ne _ hi]

private theorem pushDownRev_tag_magnitude
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (x i : ℕ) :
    pathTagMagnitude ((s.pushDownRev pathPayload x).nodes i).tag =
      pathTagMagnitude (s.nodes i).tag := by
  by_cases hx : x = 0
  · rw [SplayState.pushDownRev, ite_eq_left hx]
  rw [SplayState.pushDownRev, ite_eq_right hx]
  dsimp only
  split
  · rw [revNode_tag_magnitude, revNode_tag_magnitude]
    by_cases hi : i = x
    · subst i
      rw [SplayState.nodes_updateNode_self]
    · rw [SplayState.nodes_updateNode_ne _ hi]
  · rfl

/-- A full root push preserves the route bound while updating the auxiliary
tree to reflect reversed children. -/
theorem pathTagRouteMagnitude_pushDown_root_le
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {rp x target : ℕ} {left right : AuxTree}
    (hnd : (AuxTree.node x left right).toList.Nodup)
    (hsub : SplayState.SubtreeInv pathPayload s rp (.node x left right))
    (ha : target ∈ (AuxTree.node x left right).toList) :
    let left' := if (s.nodes x).rev then left.revRoot else left
    let right' := if (s.nodes x).rev then right.revRoot else right
    pathTagRouteMagnitude (s.pushDown pathPayload x) ((AuxTree.node x left' right').pathTo target) ≤
      pathTagRouteMagnitude s ((AuxTree.node x left right).pathTo target) := by
  intro left' right'
  obtain ⟨hleft, _, hright, _, _⟩ := AuxTree.nodup_node_unfold hnd
  have hl : left'.toList.Perm left.toList := by
    dsimp only [left']
    split
    · exact SplayState.revRoot_toList_perm _
    · exact List.Perm.refl _
  have hr : right'.toList.Perm right.toList := by
    dsimp only [right']
    split
    · exact SplayState.revRoot_toList_perm _
    · exact List.Perm.refl _
  have hp : (AuxTree.node x left' right').toList.Perm (AuxTree.node x left right).toList :=
    (hl.append_right [x]).append hr
  have hpLeft : left'.pathTo target = left.pathTo target := by
    dsimp only [left']
    split
    · exact SplayState.revRoot_pathTo hleft target
    · rfl
  have hpRight : right'.pathTo target = right.pathTo target := by
    dsimp only [right']
    split
    · exact SplayState.revRoot_pathTo hright target
    · rfl
  have hpath : (AuxTree.node x left' right').pathTo target = (AuxTree.node x left right).pathTo target := by
    simp only [AuxTree.pathTo, hl.mem_iff, hr.mem_iff, hpLeft, hpRight]
  obtain ⟨hsub', hrev, _⟩ := SplayState.pushDownRev_root_preserves pathPayload_laws hnd hsub
  have hcharged : pathTagRouteMagnitude (s.pushDownRev pathPayload x)
      ((AuxTree.node x left' right').pathTo target) =
      pathTagRouteMagnitude s ((AuxTree.node x left right).pathTo target) := by
    rw [hpath]
    unfold pathTagRouteMagnitude
    congr 1
    apply List.map_congr_left
    intro i _
    exact pushDownRev_tag_magnitude s x i
  rw [← hcharged]
  exact pathTagRouteMagnitude_pushDownTag_root_le (hp.nodup_iff.mpr hnd) hsub' hrev
    (hp.mem_iff.mpr ha)

/-- A push at any node preserves the bound on every live route in its
auxiliary tree. The ancestor prefix and any disjoint route are unchanged. -/
theorem pathTagRouteMagnitude_pushDown_le
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {t : AuxTree} {rp x target : ℕ}
    (hnd : t.toList.Nodup) (ht : SplayState.SubtreeInv pathPayload s rp t)
    (hx : x ∈ t.toList) (ha : target ∈ t.toList) :
    pathTagRouteMagnitude (s.pushDown pathPayload x) (t.pathTo target) ≤
      pathTagRouteMagnitude s (t.pathTo target) := by
  induction t generalizing rp with
  | leaf => simp [AuxTree.toList] at hx
  | node id l r ihl ihr =>
    by_cases hroot : id = x
    · subst id
      have h := pathTagRouteMagnitude_pushDown_root_le hnd ht ha
      have hpath := (SplayState.pushDown_preserves_SubtreeInv pathPayload_laws hnd ht hx).2.2.2.2.1 target
      cases hr : (s.nodes x).rev
      · simpa only [hr, Bool.false_eq_true, ite_false] using h
      · have hEq : SplayState.pushDownTree s x (.node x l r) = .node x l.revRoot r.revRoot := by
          simp [SplayState.pushDownTree, hr, AuxTree.findSubtree, AuxTree.replaceSubtree]
        rw [hEq] at hpath
        simpa only [hr, ite_true, hpath] using h
    obtain ⟨hl, hnl, hr, hnr, hdis⟩ := AuxTree.nodup_node_unfold hnd
    have ht' := ht
    obtain ⟨_, _, _, _, _, _, _, htL, htR⟩ := ht
    have hframe := (SplayState.pushDown_preserves_SubtreeInv pathPayload_laws hnd ht' hx).2.2.2.2.2.2.2.2.1
    have frameRoute (route : List ℕ)
        (hm : ∀ u ∈ route, u ∉ ((AuxTree.node id l r).findSubtree x).toList) :
        pathTagRouteMagnitude (s.pushDown pathPayload x) route = pathTagRouteMagnitude s route := by
      unfold pathTagRouteMagnitude
      congr 1
      apply List.map_congr_left
      intro u hu
      rw [hframe u (hm u hu)]
    by_cases hxL : x ∈ l.toList
    · have hfind : (AuxTree.node id l r).findSubtree x = l.findSubtree x := by
        simp [AuxTree.findSubtree, hroot, hxL]
      have hid := hframe id (by rw [hfind]; exact fun h => hnl (AuxTree.findSubtree_subset h))
      by_cases htar : target = id
      · simp [AuxTree.pathTo, htar, pathTagRouteMagnitude, hid]
      by_cases hL : target ∈ l.toList
      · have h := ihl hl htL hxL hL
        simp only [AuxTree.pathTo, htar, ite_false, hL, ite_true]
        change pathTagMagnitude ((s.pushDown pathPayload x).nodes id).tag +
            pathTagRouteMagnitude (s.pushDown pathPayload x) (l.pathTo target) ≤
          pathTagMagnitude (s.nodes id).tag + pathTagRouteMagnitude s (l.pathTo target)
        rw [hid]
        exact add_le_add_right h _
      · apply le_of_eq (frameRoute _ ?_)
        intro u hu
        rw [hfind]
        intro hm
        have hR : target ∈ r.toList := by simpa [AuxTree.toList, htar, hL] using ha
        simp only [AuxTree.pathTo, htar, ite_false, hL, hR, ite_true, List.mem_cons] at hu
        exact hu.elim (fun h => hnl (h ▸ AuxTree.findSubtree_subset hm))
          (fun h => hdis u (AuxTree.findSubtree_subset hm) (AuxTree.mem_pathTo h))
    · have hxR : x ∈ r.toList := by simpa [AuxTree.toList, Ne.symm hroot, hxL] using hx
      have hfind : (AuxTree.node id l r).findSubtree x = r.findSubtree x := by
        simp [AuxTree.findSubtree, hroot, hxL]
      have hid := hframe id (by rw [hfind]; exact fun h => hnr (AuxTree.findSubtree_subset h))
      by_cases htar : target = id
      · simp [AuxTree.pathTo, htar, pathTagRouteMagnitude, hid]
      by_cases hL : target ∈ l.toList
      · apply le_of_eq (frameRoute _ ?_)
        intro u hu
        rw [hfind]
        intro hm
        simp only [AuxTree.pathTo, htar, ite_false, hL, ite_true, List.mem_cons] at hu
        exact hu.elim (fun h => hnr (h ▸ AuxTree.findSubtree_subset hm))
          (fun h => hdis u (AuxTree.mem_pathTo h) (AuxTree.findSubtree_subset hm))
      · have hR : target ∈ r.toList := by simpa [AuxTree.toList, htar, hL] using ha
        have h := ihr hr htR hxR hR
        simp only [AuxTree.pathTo, htar, ite_false, hL, hR, ite_true]
        change pathTagMagnitude ((s.pushDown pathPayload x).nodes id).tag +
            pathTagRouteMagnitude (s.pushDown pathPayload x) (r.pathTo target) ≤
          pathTagMagnitude (s.nodes id).tag + pathTagRouteMagnitude s (r.pathTo target)
        rw [hid]
        exact add_le_add_right h _

/-- Pushing the ancestors of a splay target preserves the tag bound on
every route of the original auxiliary tree. -/
theorem pathTagRouteMagnitude_pushPath_le {fuel : ℕ}
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {t : AuxTree} {pivot target : ℕ}
    (ht : SplayState.TreeInv pathPayload s t)
    (hx : pivot ∈ t.toList) (hdepth : t.depthOf pivot < fuel)
    (ha : target ∈ t.toList) :
    pathTagRouteMagnitude (s.pushPath pathPayload fuel pivot) (t.pathTo target) ≤
      pathTagRouteMagnitude s (t.pathTo target) := by
  induction fuel generalizing s t pivot with
  | zero => omega
  | succ k ih =>
    have hnz := SplayState.SubtreeInv_nonZero ht.sub hx
    have hpar := SplayState.SubtreeInv_par_eq_parentIn ht.nodup ht.sub hx
    by_cases hr : pivot = t.rootId
    · have hp0 : (s.nodes pivot).par = 0 := by
        rw [hpar, hr]
        cases t with
        | leaf => rfl
        | node id l r => simp [AuxTree.parentIn, AuxTree.rootId]
      simpa only [SplayState.pushPath, hnz, hp0, ite_false, ite_true] using
        pathTagRouteMagnitude_pushDown_le ht.nodup ht.sub hx ha
    · have hp := AuxTree.parentIn_mem_and_depth (p₀ := 0) ht.nodup hx hr
      let parent := (s.nodes pivot).par
      have hmem : parent ∈ t.toList := by
        dsimp only [parent]
        rw [hpar]
        exact hp.1
      have hdep : t.depthOf parent < k := by
        change t.depthOf (s.nodes pivot).par < k
        rw [hpar]
        omega
      have hpnz : (s.nodes pivot).par ≠ 0 := SplayState.SubtreeInv_nonZero ht.sub hmem
      have hcharge := ih ht hmem hdep ha
      obtain ⟨ts, ht', hperm, _, _, hpath, _⟩ :=
        SplayState.pushPath_preserves pathPayload_laws ht hmem hdep
      have hstep := pathTagRouteMagnitude_pushDown_le ht'.nodup ht'.sub
        (hperm.mem_iff.mpr hx) (hperm.mem_iff.mpr ha)
      rw [hpath target] at hstep
      simpa only [SplayState.pushPath, hnz, hpnz, ite_false] using hstep.trans hcharge

/-- A lazy reversal preserves the charge of each physical route. -/
theorem pathTagRouteMagnitude_revNode
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (x : ℕ) (route : List ℕ) :
    pathTagRouteMagnitude (s.revNode pathPayload x) route = pathTagRouteMagnitude s route := by
  unfold pathTagRouteMagnitude
  congr 1
  apply List.map_congr_left
  intro i _
  exact revNode_tag_magnitude s x i

/-- Applying a tag at a node charges its magnitude at most once on a simple route. -/
theorem pathTagRouteMagnitude_applyTagNode_le
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag} {x : ℕ}
    (hx : x ≠ 0) (tag : PathTag) {route : List ℕ} (hn : route.Nodup) :
    pathTagRouteMagnitude (s.applyTagNode pathPayload x tag) route ≤
      pathTagRouteMagnitude s route + pathTagMagnitude tag := by
  have frame (r : List ℕ) (hr : x ∉ r) :
      pathTagRouteMagnitude (s.applyTagNode pathPayload x tag) r = pathTagRouteMagnitude s r := by
    unfold pathTagRouteMagnitude
    congr 1
    apply List.map_congr_left
    intro y hy
    have hne : y ≠ x := fun h => hr (h ▸ hy)
    rw [applyTagNode_other s hne tag]
  induction route with
  | nil =>
    simp only [pathTagRouteMagnitude, List.map_nil, List.sum_nil, zero_add]
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  | cons y r ih =>
    obtain ⟨hyr, hr⟩ := List.nodup_cons.mp hn
    simp only [pathTagRouteMagnitude, List.map_cons, List.sum_cons]
    change _ + pathTagRouteMagnitude (s.applyTagNode pathPayload x tag) r ≤
      _ + pathTagRouteMagnitude s r + _
    by_cases hy : y = x
    · subst y
      rw [frame r hyr]
      have h := pathTagMagnitude_applyTagNode (s := s) hx tag
      omega
    · rw [applyTagNode_other s hy tag]
      have h := ih hr
      omega

/-- Detaching both children during Cut leaves the tag charge of a fixed route unchanged. -/
theorem pathTagRouteMagnitude_detachRootChildren_frame
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (x : ℕ) (route : List ℕ) :
    pathTagRouteMagnitude (s.detachRootChildren pathPayload x) route =
      pathTagRouteMagnitude s route := by
  apply pathTagRouteMagnitude_congr
  intro i
  by_cases hx : x = 0
  · simp [SplayState.detachRootChildren, hx]
  by_cases hl : (s.nodes x).left = 0 <;> by_cases hr : (s.nodes x).right = 0 <;>
    simp [SplayState.detachRootChildren, hx, hl, hr, SplayState.pull_tag_eq,
      setLeft_tag_eq, setRight_tag_eq, setPar_tag_eq, setPpar_tag_eq]

/-- Link initializes a zero-tag singleton and leaves the existing route tags intact. -/
theorem pathTagRouteMagnitude_linkSingleton
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) {edge u v : ℕ}
    (value : Option PathEdgeValue) :
    let next := (s.makeSingleton pathPayload edge value u).setPpar v edge
    pathTagRouteMagnitude next [edge] = 0 ∧
      ∀ route : List ℕ, edge ∉ route → pathTagRouteMagnitude next route =
        pathTagRouteMagnitude s route := by
  dsimp only
  constructor
  · simp [pathTagRouteMagnitude, setPpar_tag_eq, SplayState.makeSingleton,
      SplayState.setNode, pathTagMagnitude, pathPayload, PathTag.zero]
  · intro route hroute
    unfold pathTagRouteMagnitude
    congr 1
    apply List.map_congr_left
    intro i hi
    have hne : i ≠ edge := fun he => hroute (he ▸ hi)
    simp [setPpar_tag_eq, SplayState.makeSingleton, SplayState.setNode, hne]

/-- Each raw tag magnitude is at most the sum charged to a route containing it. -/
theorem pathTagMagnitude_le_route
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag)
    {x : ℕ} {route : List ℕ} (hx : x ∈ route) :
    pathTagMagnitude (s.nodes x).tag ≤ pathTagRouteMagnitude s route := by
  have hnonneg i : 0 ≤ pathTagMagnitude (s.nodes i).tag :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsum r : 0 ≤ pathTagRouteMagnitude s r := by
    unfold pathTagRouteMagnitude
    apply List.sum_nonneg
    intro z hz
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
    exact hnonneg i
  induction route with
  | nil => simp at hx
  | cons y r ih =>
    rw [List.mem_cons] at hx
    change _ ≤ pathTagMagnitude (s.nodes y).tag + pathTagRouteMagnitude s r
    rcases hx with rfl | hx
    · exact le_add_of_nonneg_right (hsum r)
    · exact (ih hx).trans (le_add_of_nonneg_left (hnonneg y))

/-- A uniform route bound controls every raw tag at an active auxiliary node. -/
theorem pathTagMagnitude_le_of_route_bound
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {t : AuxTree} {x : ℕ} {B : ℤ} (hx : x ∈ t.toList)
    (hb : pathTagRouteMagnitude s (t.pathTo x) ≤ B) :
    pathTagMagnitude (s.nodes x).tag ≤ B :=
  (pathTagMagnitude_le_route s (AuxTree.self_mem_pathTo hx)).trans hb

end MinCostFlow.MinRatio
