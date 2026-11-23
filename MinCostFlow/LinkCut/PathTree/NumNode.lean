module

public import MinCostFlow.MinRatio.PathTreeNumericBounds

/-!
# Raw node fields are bounded by the values and the tag routes

The numbers stored in a node of an auxiliary tree are not the values of the represented edges:
a value still owes the tags of its ancestors, and a summary covers a whole subtree. This file
bounds the stored numbers by two quantities that the operations control:

* `V`, a bound on the evaluated values of the tree (`ValB`);
* `R`, a bound on the tag route of every node: the sum of the tag sizes from the root down to
  the node (`pathTagRouteMagnitude`).

A stored value differs from its evaluated value by at most the tags above it
(`valB_raw_of_eval`). In the frame of a node, an evaluated value differs from the stored one by
at most the tags in between (`valB_eval_of_raw`). A summary adds at most one value per node and
takes a maximum of detectors (`sumB_listSummary`). Together (`pathNodeBound_of_tree`): every
node of a tree with at most `N` nodes meets `PathNodeBound (N * (V + 2 * R))`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathTree

open MinCostFlow.MinRatio MinCostFlow.LinkCut

/-- Every number of an edge value is at most `V` in absolute value. -/
def ValB (V : ℤ) (v : Option PathEdgeValue) : Prop :=
  ∀ e, v = some e → |e.gradient| ≤ V ∧ |e.length| ≤ V ∧ |e.flow| ≤ V ∧ |e.detector| ≤ V

/-- The sums of a summary are at most `G` and its detector is at most `D` in absolute value. -/
def SumB (G D : ℤ) (s : PathSummary) : Prop :=
  |s.gradient| ≤ G ∧ |s.length| ≤ G ∧ ∀ z, s.detector = some z → |z| ≤ D

/-- The tag route of `y` in `t`: the tag sizes from the root of `t` down to `y`. -/
abbrev route (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (t : AuxTree) (y : ℕ) :
    ℤ :=
  pathTagRouteMagnitude s (t.pathTo y)

theorem ValB.mono {V V' : ℤ} {v : Option PathEdgeValue} (h : ValB V v) (hle : V ≤ V') :
    ValB V' v := by
  intro e he
  obtain ⟨h1, h2, h3, h4⟩ := h e he
  exact ⟨h1.trans hle, h2.trans hle, h3.trans hle, h4.trans hle⟩

theorem valB_none (V : ℤ) : ValB V none := fun _ h => by cases h

theorem valB_rev {V : ℤ} {v : Option PathEdgeValue} :
    ValB V (pathPayload.revVal v) ↔ ValB V v := by
  cases v with
  | none => exact ⟨fun _ => valB_none V, fun _ => valB_none V⟩
  | some e =>
    change ValB V (some e.reverse) ↔ ValB V (some e)
    constructor
    · intro h e' he'
      cases he'
      obtain ⟨h1, h2, h3, h4⟩ := h _ rfl
      simp only [PathEdgeValue.reverse, abs_neg] at h1 h2 h3 h4
      exact ⟨h1, h2, h3, h4⟩
    · intro h e' he'
      cases he'
      obtain ⟨h1, h2, h3, h4⟩ := h _ rfl
      simp only [PathEdgeValue.reverse, abs_neg]
      exact ⟨h1, h2, h3, h4⟩

theorem pathTagMagnitude_nonneg (t : PathTag) : 0 ≤ pathTagMagnitude t :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem valB_act {V : ℤ} {v : Option PathEdgeValue} (t : PathTag) (h : ValB V v) :
    ValB (V + pathTagMagnitude t) (pathPayload.actVal t v) := by
  have hm := pathTagMagnitude_nonneg t
  have hf : |t.flow| ≤ pathTagMagnitude t := le_add_of_nonneg_right (abs_nonneg _)
  have hd : |t.detector| ≤ pathTagMagnitude t := le_add_of_nonneg_left (abs_nonneg _)
  cases v with
  | none => exact valB_none _
  | some e =>
    intro e' he'
    change some (e.shift t) = some e' at he'
    cases he'
    obtain ⟨h1, h2, h3, h4⟩ := h e rfl
    refine ⟨by simp only [PathEdgeValue.shift]; linarith, by simp only [PathEdgeValue.shift]; linarith,
      ?_, ?_⟩
    · simp only [PathEdgeValue.shift]
      exact (abs_add_le _ _).trans (by linarith)
    · simp only [PathEdgeValue.shift]
      exact (abs_add_le _ _).trans (by linarith)

theorem valB_of_act {V : ℤ} {v : Option PathEdgeValue} (t : PathTag)
    (h : ValB V (pathPayload.actVal t v)) : ValB (V + pathTagMagnitude t) v := by
  have hm := pathTagMagnitude_nonneg t
  have hf : |t.flow| ≤ pathTagMagnitude t := le_add_of_nonneg_right (abs_nonneg _)
  have hd : |t.detector| ≤ pathTagMagnitude t := le_add_of_nonneg_left (abs_nonneg _)
  cases v with
  | none => exact valB_none _
  | some e =>
    intro e' he'
    cases he'
    obtain ⟨h1, h2, h3, h4⟩ := h (e.shift t) rfl
    simp only [PathEdgeValue.shift] at h1 h2 h3 h4
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · have : e.flow = (e.flow + t.flow) + -t.flow := by ring
      rw [this]
      exact (abs_add_le _ _).trans (by rw [abs_neg]; linarith)
    · have : e.detector = (e.detector + t.detector) + -t.detector := by ring
      rw [this]
      exact (abs_add_le _ _).trans (by rw [abs_neg]; linarith)

theorem route_nonneg (s : SplayState (Option PathEdgeValue) PathSummary PathTag)
    (L : List ℕ) : 0 ≤ pathTagRouteMagnitude s L := by
  unfold pathTagRouteMagnitude
  apply List.sum_nonneg
  intro z hz
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
  exact pathTagMagnitude_nonneg _

/-- The route of a node below the root `id` is the tag of `id` plus the route in the child. -/
theorem route_node_left (s : SplayState (Option PathEdgeValue) PathSummary PathTag)
    {id y : ℕ} {l r : AuxTree} (hy : y ≠ id) (hl : y ∈ l.toList) :
    route s (.node id l r) y = pathTagMagnitude (s.nodes id).tag + route s l y := by
  simp [route, AuxTree.pathTo, hy, hl, pathTagRouteMagnitude]

theorem route_node_right (s : SplayState (Option PathEdgeValue) PathSummary PathTag)
    {id y : ℕ} {l r : AuxTree} (hy : y ≠ id) (hl : y ∉ l.toList) (hr : y ∈ r.toList) :
    route s (.node id l r) y = pathTagMagnitude (s.nodes id).tag + route s r y := by
  simp [route, AuxTree.pathTo, hy, hl, hr, pathTagRouteMagnitude]

theorem route_node_self (s : SplayState (Option PathEdgeValue) PathSummary PathTag)
    {id : ℕ} {l r : AuxTree} : route s (.node id l r) id = pathTagMagnitude (s.nodes id).tag := by
  simp [route, AuxTree.pathTo, pathTagRouteMagnitude]

theorem mag_local (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (id : ℕ)
    (flip : Bool) :
    pathTagMagnitude (if flip then pathPayload.revTag (s.nodes id).tag else (s.nodes id).tag) =
      pathTagMagnitude (s.nodes id).tag := by
  cases flip
  · rfl
  · exact pathTagMagnitude_reverse _

/-- Membership in the evaluated pairs of a node. -/
theorem mem_evalPairs_node {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {id : ℕ} {l r : AuxTree} {flip : Bool} {acc : PathTag} {p : ℕ × Option PathEdgeValue}
    (hp : p ∈ SplayState.evalPairs pathPayload s (.node id l r) flip acc) :
    let acc' := pathPayload.compTag acc
      (if flip then pathPayload.revTag (s.nodes id).tag else (s.nodes id).tag)
    let flip' := flip ^^ (s.nodes id).rev
    p = (id, pathPayload.actVal acc
      (if flip then pathPayload.revVal (s.nodes id).val else (s.nodes id).val)) ∨
      p ∈ SplayState.evalPairs pathPayload s l flip' acc' ∨
      p ∈ SplayState.evalPairs pathPayload s r flip' acc' := by
  intro acc' flip'
  unfold SplayState.evalPairs at hp
  cases flip <;> simp only [Bool.false_eq_true, ite_false, ite_true, List.mem_append,
    List.mem_singleton] at hp <;> tauto

theorem evalPairs_sub_left {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {id : ℕ} {l r : AuxTree} {flip : Bool} {acc : PathTag} {p : ℕ × Option PathEdgeValue}
    (hp : p ∈ SplayState.evalPairs pathPayload s l (flip ^^ (s.nodes id).rev)
      (pathPayload.compTag acc
        (if flip then pathPayload.revTag (s.nodes id).tag else (s.nodes id).tag))) :
    p ∈ SplayState.evalPairs pathPayload s (.node id l r) flip acc := by
  unfold SplayState.evalPairs
  cases flip <;> simp only [Bool.false_eq_true, ite_false, ite_true, Bool.false_xor,
    Bool.true_xor] at hp ⊢ <;> simp [hp]

theorem evalPairs_sub_right {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {id : ℕ} {l r : AuxTree} {flip : Bool} {acc : PathTag} {p : ℕ × Option PathEdgeValue}
    (hp : p ∈ SplayState.evalPairs pathPayload s r (flip ^^ (s.nodes id).rev)
      (pathPayload.compTag acc
        (if flip then pathPayload.revTag (s.nodes id).tag else (s.nodes id).tag))) :
    p ∈ SplayState.evalPairs pathPayload s (.node id l r) flip acc := by
  unfold SplayState.evalPairs
  cases flip <;> simp only [Bool.false_eq_true, ite_false, ite_true, Bool.false_xor,
    Bool.true_xor] at hp ⊢ <;> simp [hp]

theorem evalPairs_self {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {id : ℕ} {l r : AuxTree} {flip : Bool} {acc : PathTag} :
    (id, pathPayload.actVal acc
      (if flip then pathPayload.revVal (s.nodes id).val else (s.nodes id).val)) ∈
      SplayState.evalPairs pathPayload s (.node id l r) flip acc := by
  unfold SplayState.evalPairs
  cases flip <;> simp

theorem mag_acc' (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (id : ℕ)
    (flip : Bool) (acc : PathTag) :
    pathTagMagnitude (pathPayload.compTag acc
      (if flip then pathPayload.revTag (s.nodes id).tag else (s.nodes id).tag)) ≤
      pathTagMagnitude acc + pathTagMagnitude (s.nodes id).tag := by
  rw [← mag_local s id flip]
  exact pathTagMagnitude_compose _ _

/-- A stored value is within the tags above it of its evaluated value. -/
theorem valB_raw_of_eval (s : SplayState (Option PathEdgeValue) PathSummary PathTag) :
    ∀ (t : AuxTree) (flip : Bool) (acc : PathTag) (V : ℤ), t.toList.Nodup →
      (∀ p ∈ SplayState.evalPairs pathPayload s t flip acc, ValB V p.2) →
      ∀ y ∈ t.toList, ValB (V + pathTagMagnitude acc + route s t y) (s.nodes y).val
  | .leaf, _, _, _, _, _, y, hy => by simp [AuxTree.toList] at hy
  | .node id l r, flip, acc, V, hnd, hev, y, hy => by
    obtain ⟨hlnd, hidl, hrnd, hidr, hdis⟩ := AuxTree.nodup_node_unfold hnd
    have hacc := mag_acc' s id flip acc
    have hrt := route_nonneg s ((AuxTree.node id l r).pathTo y)
    by_cases hyi : y = id
    · subst hyi
      have h1 := valB_of_act acc (hev _ evalPairs_self)
      have h2 : ValB (V + pathTagMagnitude acc) (s.nodes y).val := by
        cases flip
        · exact h1
        · exact valB_rev.mp h1
      exact h2.mono (by linarith)
    by_cases hyl : y ∈ l.toList
    · have ih := valB_raw_of_eval s l _ _ V hlnd (fun p hp => hev p (evalPairs_sub_left hp)) y hyl
      rw [route_node_left s hyi hyl]
      exact ih.mono (by linarith)
    · have hyr : y ∈ r.toList := by
        simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hy; tauto
      have ih := valB_raw_of_eval s r _ _ V hrnd (fun p hp => hev p (evalPairs_sub_right hp)) y hyr
      rw [route_node_right s hyi hyl hyr]
      exact ih.mono (by linarith)

/-- In any frame, an evaluated value is within the tags in between of its stored value. -/
theorem valB_eval_of_raw (s : SplayState (Option PathEdgeValue) PathSummary PathTag) :
    ∀ (t : AuxTree) (flip : Bool) (acc : PathTag) (W Q : ℤ), t.toList.Nodup →
      (∀ y ∈ t.toList, ValB W (s.nodes y).val) → (∀ y ∈ t.toList, route s t y ≤ Q) →
      ∀ p ∈ SplayState.evalPairs pathPayload s t flip acc,
        ValB (W + pathTagMagnitude acc + Q) p.2
  | .leaf, _, _, _, _, _, _, _, p, hp => by simp [SplayState.evalPairs] at hp
  | .node id l r, flip, acc, W, Q, hnd, hW, hQ, p, hp => by
    obtain ⟨hlnd, hidl, hrnd, hidr, hdis⟩ := AuxTree.nodup_node_unfold hnd
    have hacc := mag_acc' s id flip acc
    have hid : id ∈ (AuxTree.node id l r).toList := by simp [AuxTree.toList]
    have hQid := hQ id hid
    rw [route_node_self] at hQid
    have hmid := pathTagMagnitude_nonneg (s.nodes id).tag
    rcases mem_evalPairs_node hp with rfl | hpl | hpr
    · have h0 : ValB W (if flip then pathPayload.revVal (s.nodes id).val else (s.nodes id).val) := by
        cases flip
        · exact hW id hid
        · exact valB_rev.mpr (hW id hid)
      exact (valB_act acc h0).mono (by linarith)
    · have hQl : ∀ y ∈ l.toList, route s l y ≤ Q - pathTagMagnitude (s.nodes id).tag := by
        intro y hy
        have hyi : y ≠ id := fun h => hidl (h ▸ hy)
        have := hQ y (by simp [AuxTree.toList, hy])
        rw [route_node_left s hyi hy] at this
        linarith
      have ih := valB_eval_of_raw s l _ _ W _ hlnd
        (fun y hy => hW y (by simp [AuxTree.toList, hy])) hQl p hpl
      exact ih.mono (by linarith)
    · have hQr : ∀ y ∈ r.toList, route s r y ≤ Q - pathTagMagnitude (s.nodes id).tag := by
        intro y hy
        have hyi : y ≠ id := fun h => hidr (h ▸ hy)
        have hyl : y ∉ l.toList := fun h => hdis y h hy
        have := hQ y (by simp [AuxTree.toList, hy])
        rw [route_node_right s hyi hyl hy] at this
        linarith
      have ih := valB_eval_of_raw s r _ _ W _ hrnd
        (fun y hy => hW y (by simp [AuxTree.toList, hy])) hQr p hpr
      exact ih.mono (by linarith)

/-- A summary of values bounded by `U` has sums at most `length * U` and detector at most `U`. -/
theorem sumB_listSummary {U : ℤ} (hU : 0 ≤ U) :
    ∀ ps : List (ℕ × Option PathEdgeValue), (∀ p ∈ ps, ValB U p.2) →
      SumB (ps.length * U) U (pathPayload.listSummary ps)
  | [], _ => by
    refine ⟨by simp [PathSummary.empty, pathPayload], by simp [PathSummary.empty, pathPayload], ?_⟩
    intro z hz
    simp [PathSummary.empty, pathPayload] at hz
  | (id, v) :: rest, h => by
    obtain ⟨ig, il, id'⟩ := sumB_listSummary hU rest (fun p hp => h p (List.mem_cons_of_mem _ hp))
    have hv := h (id, v) List.mem_cons_self
    rw [LctPayload.listSummary_cons]
    change SumB _ _ (PathSummary.combine (PathSummary.single v) _)
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    cases v with
    | none =>
      simp only [PathSummary.single, PathSummary.combine, PathSummary.empty, zero_add, detectorMax]
      exact ⟨ig.trans (by linarith), il.trans (by linarith), id'⟩
    | some e =>
      obtain ⟨h1, h2, _, h4⟩ := hv e rfl
      simp only [PathSummary.single, PathSummary.combine]
      refine ⟨(abs_add_le _ _).trans (by linarith), (abs_add_le _ _).trans (by linarith), ?_⟩
      intro z hz
      cases hd : (pathPayload.listSummary rest).detector with
      | none =>
        simp only [hd, detectorMax] at hz
        cases hz; exact h4
      | some b =>
        simp only [hd, detectorMax, Option.some.injEq] at hz
        subst hz
        have hb := id' b hd
        rw [abs_le] at h4 hb ⊢
        constructor
        · exact le_max_of_le_left h4.1
        · exact max_le h4.2 hb.2

/-- Every summary in a subtree is bounded by the stored values and the routes. -/
theorem sumB_of_subtree (s : SplayState (Option PathEdgeValue) PathSummary PathTag)
    {W Q : ℤ} (hW0 : 0 ≤ W) (hQ0 : 0 ≤ Q) :
    ∀ (t : AuxTree) (rp : ℕ), SplayState.SubtreeInv pathPayload s rp t → t.toList.Nodup →
      (∀ y ∈ t.toList, ValB W (s.nodes y).val) → (∀ y ∈ t.toList, route s t y ≤ Q) →
      ∀ y ∈ t.toList, SumB (t.countNodes * (W + Q)) (W + Q) (s.nodes y).sum
  | .leaf, _, _, _, _, _, y, hy => by simp [AuxTree.toList] at hy
  | .node id l r, rp, hsub, hnd, hW, hQ, y, hy => by
    obtain ⟨hlnd, hidl, hrnd, hidr, hdis⟩ := AuxTree.nodup_node_unfold hnd
    obtain ⟨-, -, -, -, -, -, hsum, hsl, hsr⟩ := hsub
    have hcnt : (AuxTree.node id l r).countNodes = l.countNodes + 1 + r.countNodes := by
      simp only [AuxTree.countNodes]; omega
    have hmono {G G' : ℤ} {sm : PathSummary} (h : SumB G (W + Q) sm) (hle : G ≤ G') :
        SumB G' (W + Q) sm := ⟨h.1.trans hle, h.2.1.trans hle, h.2.2⟩
    have hWQ : 0 ≤ W + Q := by linarith
    by_cases hyi : y = id
    · subst hyi
      rw [hsum]
      have hev := valB_eval_of_raw s _ false pathPayload.idTag W Q hnd hW hQ
      have h0 : pathTagMagnitude pathPayload.idTag = 0 := by
        simp [pathTagMagnitude, pathPayload, PathTag.zero]
      rw [h0, add_zero] at hev
      have := sumB_listSummary hWQ _ hev
      rw [SplayState.evalPairs_length] at this
      exact this
    have hmid := pathTagMagnitude_nonneg (s.nodes id).tag
    by_cases hyl : y ∈ l.toList
    · have hQl : ∀ z ∈ l.toList, route s l z ≤ Q := by
        intro z hz
        have hzi : z ≠ id := fun h => hidl (h ▸ hz)
        have := hQ z (by simp [AuxTree.toList, hz])
        rw [route_node_left s hzi hz] at this
        linarith
      have ih := sumB_of_subtree s hW0 hQ0 l id hsl hlnd
        (fun z hz => hW z (by simp [AuxTree.toList, hz])) hQl y hyl
      refine hmono ih ?_
      rw [hcnt]; push_cast; nlinarith
    · have hyr : y ∈ r.toList := by
        simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hy; tauto
      have hQr : ∀ z ∈ r.toList, route s r z ≤ Q := by
        intro z hz
        have hzi : z ≠ id := fun h => hidr (h ▸ hz)
        have hzl : z ∉ l.toList := fun h => hdis z h hz
        have := hQ z (by simp [AuxTree.toList, hz])
        rw [route_node_right s hzi hzl hz] at this
        linarith
      have ih := sumB_of_subtree s hW0 hQ0 r id hsr hrnd
        (fun z hz => hW z (by simp [AuxTree.toList, hz])) hQr y hyr
      refine hmono ih ?_
      rw [hcnt]; push_cast; nlinarith

/-- The tag of a node is at most its route. -/
theorem tag_le_route (s : SplayState (Option PathEdgeValue) PathSummary PathTag)
    {t : AuxTree} {y : ℕ} (hy : y ∈ t.toList) :
    pathTagMagnitude (s.nodes y).tag ≤ route s t y :=
  pathTagMagnitude_le_route s (AuxTree.self_mem_pathTo hy)

/-- The main bound: in a tree with at most `N` nodes, values bounded by `V` and routes bounded
by `R`, every node meets `PathNodeBound (N * (V + 2 * R))`. -/
theorem pathNodeBound_of_tree {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {t : AuxTree} (ht : SplayState.TreeInv pathPayload s t) {V R : ℤ} {N : ℕ}
    (hV : 0 ≤ V) (hR : 0 ≤ R) (hN : t.countNodes ≤ N) (hN1 : 1 ≤ N)
    (hev : ∀ p ∈ SplayState.evalPairs pathPayload s t false pathPayload.idTag, ValB V p.2)
    (hr : ∀ y ∈ t.toList, route s t y ≤ R) :
    ∀ y ∈ t.toList, PathNodeBound (N * (V + 2 * R)) (s.nodes y) := by
  have h0 : pathTagMagnitude pathPayload.idTag = 0 := by
    simp [pathTagMagnitude, pathPayload, PathTag.zero]
  have hraw : ∀ y ∈ t.toList, ValB (V + R) (s.nodes y).val := by
    intro y hy
    have := valB_raw_of_eval s t false pathPayload.idTag V ht.nodup hev y hy
    rw [h0, add_zero] at this
    exact this.mono (by linarith [hr y hy])
  have hsum := sumB_of_subtree s (by linarith) hR t 0 ht.sub ht.nodup hraw hr
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN1
  have hNt : (t.countNodes : ℤ) ≤ N := by exact_mod_cast hN
  have hB : V + 2 * R ≤ N * (V + 2 * R) := by nlinarith
  intro y hy
  obtain ⟨hg, hl, hd⟩ := hsum y hy
  have htag := (tag_le_route s hy).trans (hr y hy)
  have hf : |(s.nodes y).tag.flow| ≤ R := (le_add_of_nonneg_right (abs_nonneg _)).trans htag
  have hdt : |(s.nodes y).tag.detector| ≤ R := (le_add_of_nonneg_left (abs_nonneg _)).trans htag
  have hG : (t.countNodes : ℤ) * (V + R + R) ≤ N * (V + 2 * R) := by nlinarith
  refine ⟨fun v hv => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hraw y hy v hv
    exact ⟨h1.trans (by linarith), h2.trans (by linarith), h3.trans (by linarith),
      h4.trans (by linarith)⟩
  · linarith
  · linarith
  · intro z hz; exact (hd z hz).trans (by linarith)
  · linarith
  · linarith

end MinCostFlow.LinkCut.PathTree
