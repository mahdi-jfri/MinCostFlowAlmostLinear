module

public import MinCostFlow.LinkCut.PathTree.NumRoute
public import MinCostFlow.LinkCut.PathTree.AccOps
public import MinCostFlow.LinkCut.Gen.Splay
public import MinCostFlow.LinkCut.Path.Rev

/-!
# The numbers a splay computes fit

The splay program computes payload values in `K` limbs. Its precondition `SplayOk` asks that
every value it computes fits (`pathOk h K`). This file proves that from a bound on the tree
(`TreeB`): the evaluated values are at most `V`, every tag charge is at most `R`, and the tree
has at most `k` nodes. Then every stored node meets `PathNodeBound (k * (V + 2 * R))`
(`treeB_bound`), and every value a step computes is at most twice that, which fits when
`Room h K` holds for the bound.

* A push reverses (sizes stay) and adds the parent tag (at most the bound) to each child
  (`pushDownOk_of_bound`).
* A rotation writes the summaries of its two nodes in the rotated tree, which again meets the
  bound (`rotateOk_tree`).

The main result is `splayOk_tree`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathTree

open MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.SplayState
  MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.Path

variable {α σ τ : Type*}

/-- Four times the bound is below the capacity of `K` limbs. -/
def Room (h K : ℕ) (B : ℤ) : Prop := 4 * B < (Num.capacity h K : ℤ)

theorem fits_of_abs {h K : ℕ} {B z : ℤ} (hz : |z| ≤ 2 * B) (hr : Room h K B) :
    Num.Fits h K z := by
  obtain ⟨hl, hu⟩ := abs_le.mp hz
  unfold Room at hr
  exact ⟨by linarith, by linarith⟩

theorem bound_nonneg {B : ℤ} {nd : SplayNode (Option PathEdgeValue) PathSummary PathTag}
    (hb : PathNodeBound B nd) : 0 ≤ B :=
  (abs_nonneg _).trans hb.2.2.2.2.1

theorem revOk_of_bound {h K : ℕ} {B : ℤ}
    {nd : SplayNode (Option PathEdgeValue) PathSummary PathTag} (hb : PathNodeBound B nd)
    (hr : Room h K B) : RevOk (pathOk h K) pathPayload nd := by
  have hB := bound_nonneg hb
  have f {z : ℤ} (hz : |z| ≤ B) : Num.Fits h K z := fits_of_abs (by linarith) hr
  obtain ⟨hv, hg, hl, hd, htf, htd⟩ := hb
  refine ⟨?_, ⟨?_, f hl, ?_⟩, ?_, ?_⟩
  · change PathEdgeFits h K (Option.map PathEdgeValue.reverse nd.val)
    cases hval : nd.val with
    | none => trivial
    | some e =>
      obtain ⟨h1, h2, h3, h4⟩ := hv e hval
      exact ⟨f (by simpa [PathEdgeValue.reverse] using h1), f h2,
        f (by simpa [PathEdgeValue.reverse] using h3), f h4⟩
  · exact f (by simpa [pathPayload, PathSummary.reverse] using hg)
  · change match nd.sum.detector with | none => True | some z => Num.Fits h K z
    cases hz : nd.sum.detector with
    | none => trivial
    | some z => exact f (hd z hz)
  · exact f (by simpa [pathPayload, PathTag.reverse] using htf)
  · exact f htd

theorem actOk_of_bound {h K : ℕ} {B : ℤ}
    {nd : SplayNode (Option PathEdgeValue) PathSummary PathTag} (hb : PathNodeBound B nd)
    {t : PathTag} (hf : |t.flow| ≤ B) (hdt : |t.detector| ≤ B) (hr : Room h K B) :
    ActOk (pathOk h K) pathPayload t nd := by
  have hB := bound_nonneg hb
  have f {z : ℤ} (hz : |z| ≤ B) : Num.Fits h K z := fits_of_abs (by linarith) hr
  have f2 {z u : ℤ} (hz : |z| ≤ B) (hu : |u| ≤ B) : Num.Fits h K (z + u) :=
    fits_of_abs ((abs_add_le _ _).trans (by linarith)) hr
  obtain ⟨hv, hg, hl, hd, htf, htd⟩ := hb
  refine ⟨?_, ⟨f hg, f hl, ?_⟩, f2 hf htf, f2 hdt htd⟩
  · change PathEdgeFits h K (Option.map (PathEdgeValue.shift t) nd.val)
    cases hval : nd.val with
    | none => trivial
    | some e =>
      obtain ⟨h1, h2, h3, h4⟩ := hv e hval
      exact ⟨f h1, f h2, by simpa [PathEdgeValue.shift, add_comm] using f2 hf h3,
        by simpa [PathEdgeValue.shift, add_comm] using f2 hdt h4⟩
  · change match (PathSummary.shift t nd.sum).detector with
      | none => True | some z => Num.Fits h K z
    cases hz : nd.sum.detector with
    | none => simp [PathSummary.shift, hz]
    | some z =>
      simp only [PathSummary.shift, hz, Option.map_some]
      exact f2 (hd z hz) hdt

theorem revNode_other (s : SplayState (Option PathEdgeValue) PathSummary PathTag) {y z : ℕ}
    (hz : z ≠ y) : (s.revNode pathPayload y).nodes z = s.nodes z := by
  unfold SplayState.revNode
  split_ifs
  · rfl
  · exact SplayState.nodes_updateNode_ne _ hz _

theorem applyTagNode_other' (s : SplayState (Option PathEdgeValue) PathSummary PathTag)
    {y z : ℕ} (hz : z ≠ y) (t : PathTag) : (s.applyTagNode pathPayload y t).nodes z = s.nodes z := by
  unfold SplayState.applyTagNode
  split_ifs
  · rfl
  · exact SplayState.nodes_updateNode_ne _ hz _

theorem bound_revNode {B : ℤ} (s : SplayState (Option PathEdgeValue) PathSummary PathTag)
    (y z : ℕ) (h : PathNodeBound B (s.nodes z)) :
    PathNodeBound B ((s.revNode pathPayload y).nodes z) := by
  by_cases hz : z = y
  · subst hz; exact PathNodeBound.revNode h
  · rw [revNode_other s hz]; exact h

/-- The node `x` keeps its fields other than `rev` when its reversal is pushed. -/
theorem pushDownRev_self (s : SplayState (Option PathEdgeValue) PathSummary PathTag) {x : ℕ}
    (hl : (s.nodes x).left ≠ x) (hr : (s.nodes x).right ≠ x) :
    ((s.pushDownRev pathPayload x).nodes x).left = (s.nodes x).left ∧
    ((s.pushDownRev pathPayload x).nodes x).right = (s.nodes x).right ∧
    ((s.pushDownRev pathPayload x).nodes x).tag = (s.nodes x).tag ∧
    ((s.pushDownRev pathPayload x).nodes x).val = (s.nodes x).val ∧
    ((s.pushDownRev pathPayload x).nodes x).sum = (s.nodes x).sum := by
  unfold SplayState.pushDownRev
  by_cases hx : x = 0
  · simp [hx]
  cases hrev : (s.nodes x).rev
  · simp [hx, hrev]
  · simp only [hx, hrev, if_false, if_true]
    rw [revNode_other _ (Ne.symm hr), revNode_other _ (Ne.symm hl),
      SplayState.nodes_updateNode_self]
    simp

theorem bound_pushDownRev {B : ℤ} (s : SplayState (Option PathEdgeValue) PathSummary PathTag)
    (x z : ℕ) (h : PathNodeBound B (s.nodes z)) :
    PathNodeBound B ((s.pushDownRev pathPayload x).nodes z) := by
  unfold SplayState.pushDownRev
  by_cases hx : x = 0
  · simpa [hx] using h
  cases hrev : (s.nodes x).rev
  · simpa [hx, hrev] using h
  · simp only [hx, hrev, if_false, if_true]
    apply bound_revNode
    apply bound_revNode
    by_cases hz : z = x
    · subst hz
      rw [SplayState.nodes_updateNode_self]
      exact h
    · rw [SplayState.nodes_updateNode_ne _ hz]; exact h

/-- A push at `x` computes values that fit when `x` and its children meet the bound. -/
theorem pushDownOk_of_bound {h K : ℕ} {B : ℤ}
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag} {x : ℕ} (hroom : Room h K B)
    (hb : ∀ z, z ≠ 0 → (z = x ∨ z = (s.nodes x).left ∨ z = (s.nodes x).right) →
      PathNodeBound B (s.nodes z))
    (hlx : (s.nodes x).left ≠ x) (hrx : (s.nodes x).right ≠ x)
    (hlr : (s.nodes x).left ≠ 0 → (s.nodes x).left ≠ (s.nodes x).right) :
    PushDownOk (pathOk h K) pathPayload s x := by
  set l := (s.nodes x).left with hl_def
  set r := (s.nodes x).right with hr_def
  refine ⟨?_, ?_⟩
  · intro hx _
    dsimp only
    refine ⟨fun hl0 => ?_, fun hr0 => ?_⟩
    · rw [SplayState.nodes_updateNode_ne _ hlx]
      exact revOk_of_bound (hb l hl0 (Or.inr (Or.inl rfl))) hroom
    · have : (SplayState.revNode pathPayload
          (s.updateNode x fun cur => { cur with rev := false }) l).nodes r =
          s.nodes r := by
        by_cases hl0 : l = 0
        · rw [hl0]; simp [SplayState.revNode, SplayState.nodes_updateNode_ne _ hrx]
        · rw [revNode_other _ (Ne.symm (hlr hl0)), SplayState.nodes_updateNode_ne _ hrx]
      rw [this]
      exact revOk_of_bound (hb r hr0 (Or.inr (Or.inr rfl))) hroom
  · intro hx _
    obtain ⟨hl1, hr1, ht1, -, -⟩ := pushDownRev_self s hlx hrx
    set s1 := s.pushDownRev pathPayload x
    have hxb := bound_pushDownRev s x x (hb x hx (Or.inl rfl))
    have htf : |(s1.nodes x).tag.flow| ≤ B := hxb.2.2.2.2.1
    have htd : |(s1.nodes x).tag.detector| ≤ B := hxb.2.2.2.2.2
    dsimp only
    rw [hl1, hr1]
    refine ⟨fun hl0 => ?_, fun hr0 => ?_⟩
    · rw [SplayState.nodes_updateNode_ne _ hlx]
      exact actOk_of_bound (bound_pushDownRev s x l (hb l hl0 (Or.inr (Or.inl rfl)))) htf htd
        hroom
    · have : (SplayState.applyTagNode pathPayload
          (s1.updateNode x fun cur => { cur with tag := pathPayload.idTag }) l
          (s1.nodes x).tag).nodes r = s1.nodes r := by
        by_cases hl0 : l = 0
        · rw [hl0]; simp [SplayState.applyTagNode, SplayState.nodes_updateNode_ne _ hrx]
        · rw [applyTagNode_other' _ (Ne.symm (hlr hl0)), SplayState.nodes_updateNode_ne _ hrx]
      rw [this]
      exact actOk_of_bound (bound_pushDownRev s x r (hb r hr0 (Or.inr (Or.inr rfl)))) htf htd
        hroom

/-- The children of a tree node are distinct from it and from each other, and lie in the
tree. -/
theorem tree_children {P : LctPayload α σ τ} {s : SplayState α σ τ} {t : AuxTree}
    (ht : TreeInv P s t) {x : ℕ} (hx : x ∈ t.toList) :
    (s.nodes x).left ≠ x ∧ (s.nodes x).right ≠ x ∧
      ((s.nodes x).left ≠ 0 → (s.nodes x).left ≠ (s.nodes x).right) ∧
      ((s.nodes x).left ≠ 0 → (s.nodes x).left ∈ t.toList) ∧
      ((s.nodes x).right ≠ 0 → (s.nodes x).right ∈ t.toList) := by
  have hx0 : x ≠ 0 := SubtreeInv_nonZero ht.sub hx
  obtain ⟨l', r', hf⟩ := AuxTree.findSubtree_root_of_mem hx
  have hsub := SubtreeInv_findSubtree ht.nodup ht.sub hx
  have hnd := AuxTree.findSubtree_nodup (subId := x) ht.nodup
  rw [hf] at hsub hnd
  obtain ⟨-, hl, hr, -⟩ := hsub
  obtain ⟨-, hxl, -, hxr, hdis⟩ := AuxTree.nodup_node_unfold hnd
  have hcm := SubtreeInv.child_mem ht.sub hx
  refine ⟨?_, ?_, ?_, hcm.1, hcm.2⟩
  · rw [hl]
    cases l' with
    | leaf => exact Ne.symm hx0
    | node a _ _ => intro h; apply hxl; simp [AuxTree.rootId] at h; simp [AuxTree.toList, h]
  · rw [hr]
    cases r' with
    | leaf => exact Ne.symm hx0
    | node a _ _ => intro h; apply hxr; simp [AuxTree.rootId] at h; simp [AuxTree.toList, h]
  · rw [hl, hr]
    intro h0
    cases l' with
    | leaf => exact absurd rfl h0
    | node a _ _ =>
      cases r' with
      | leaf => simpa [AuxTree.rootId] using h0
      | node b _ _ =>
        intro hab
        simp only [AuxTree.rootId] at hab
        subst hab
        exact hdis a (by simp [AuxTree.toList]) (by simp [AuxTree.toList])

/-- A tree in a state with the bounds of this file. -/
structure TreeB (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (t : AuxTree)
    (k : ℕ) (V R : ℤ) : Prop where
  inv : TreeInv pathPayload s t
  val : ∀ p ∈ evalPairs pathPayload s t false pathPayload.idTag, ValB V p.2
  chg : ∀ y ∈ t.toList, charge s k y ≤ R
  size : t.countNodes ≤ k

theorem treeB_bound {s : SplayState (Option PathEdgeValue) PathSummary PathTag} {t : AuxTree}
    {k : ℕ} {V R : ℤ} (hT : TreeB s t k V R) (hV : 0 ≤ V) (hR : 0 ≤ R) (hk : 1 ≤ k) :
    ∀ y ∈ t.toList, PathNodeBound (k * (V + 2 * R)) (s.nodes y) :=
  pathNodeBound_of_tree hT.inv hV hR hT.size hk hT.val
    (fun y hy => (charge_eq_route hT.inv hy hT.size).symm ▸ hT.chg y hy)

/-- The hypotheses of the numeric lemmas. -/
structure NumCtx (h K k : ℕ) (V R : ℤ) : Prop where
  hV : 0 ≤ V
  hR : 0 ≤ R
  hk : 1 ≤ k
  room : Room h K (k * (V + 2 * R))

theorem pushDownOk_tree {h K k : ℕ} {V R : ℤ} (C : NumCtx h K k V R)
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag} {t : AuxTree}
    (hT : TreeB s t k V R) {x : ℕ} (hx : x ∈ t.toList) :
    PushDownOk (pathOk h K) pathPayload s x := by
  obtain ⟨hlx, hrx, hlr, hlm, hrm⟩ := tree_children hT.inv hx
  have hb := treeB_bound hT C.hV C.hR C.hk
  refine pushDownOk_of_bound C.room ?_ hlx hrx hlr
  rintro z hz (rfl | rfl | rfl)
  · exact hb _ hx
  · exact hb _ (hlm hz)
  · exact hb _ (hrm hz)

/-- A rotation at a node with a pushed path keeps the bounds. -/
theorem rotate_treeB {s : SplayState (Option PathEdgeValue) PathSummary PathTag} {t : AuxTree}
    {k : ℕ} {V R : ℤ} (hT : TreeB s t k V R) {a : ℕ} (ha : a ∈ t.toList) (har : a ≠ t.rootId)
    (hclean : ∀ u ∈ t.pathTo a, (s.nodes u).rev = false ∧ (s.nodes u).tag = pathPayload.idTag) :
    TreeB (rotate pathPayload s a) (t.rotateAt a) k V R := by
  obtain ⟨ht', hperm, hev, -, -, -⟩ := rotate_preserves pathPayload_laws hT.inv ha har hclean
  refine ⟨ht', hev ▸ hT.val, fun y hy => ?_, by rw [countNodes_perm hperm]; exact hT.size⟩
  have hy' := hperm.mem_iff.mp hy
  rw [rotate_charge hT.inv ha hclean hT.size y hy']
  exact hT.chg y hy'

theorem rotateOk_tree {h K k : ℕ} {V R : ℤ} (C : NumCtx h K k V R)
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag} {t : AuxTree}
    (hT : TreeB s t k V R) {a : ℕ} (ha : a ∈ t.toList)
    (hclean : ∀ u ∈ t.pathTo a, (s.nodes u).rev = false ∧ (s.nodes u).tag = pathPayload.idTag) :
    RotateOk (pathOk h K) pathPayload s a := by
  intro ha0 hp0
  have hpar := SubtreeInv_par_eq_parentIn hT.inv.nodup hT.inv.sub ha
  have har : a ≠ t.rootId := by
    intro h; apply hp0; rw [hpar, h]; exact parentIn_rootId 0
  obtain ⟨hpm, -, -⟩ := AuxTree.parentIn_mem_and_depth (p₀ := 0) hT.inv.nodup ha har
  have hT' := rotate_treeB hT ha har hclean
  obtain ⟨ht', hperm, -⟩ := rotate_preserves pathPayload_laws hT.inv ha har hclean
  have hb := treeB_bound hT' C.hV C.hR C.hk
  have hpa : (s.nodes a).par ≠ a := by
    rw [hpar]; intro h
    obtain ⟨-, hdep, -⟩ := AuxTree.parentIn_mem_and_depth (p₀ := 0) hT.inv.nodup ha har
    rw [h] at hdep; omega
  have hreq := rotate_eq (P := pathPayload) ha0 hp0
  have hbp := hb _ (hperm.mem_iff.mpr (hpar ▸ hpm))
  have hba := hb _ (hperm.mem_iff.mpr ha)
  rw [hreq, pull_nodes_ne hpa, pull_nodes_self hp0] at hbp
  rw [hreq, pull_nodes_self ha0] at hba
  have hsf {nd : SplayNode (Option PathEdgeValue) PathSummary PathTag}
      (hb : PathNodeBound (k * (V + 2 * R)) nd) : PathSummaryFits h K nd.sum := by
    have hB := bound_nonneg hb
    have f {z : ℤ} (hz : |z| ≤ k * (V + 2 * R)) : Num.Fits h K z :=
      fits_of_abs (by linarith) C.room
    refine ⟨f hb.2.1, f hb.2.2.1, ?_⟩
    cases hz : nd.sum.detector with
    | none => trivial
    | some z => exact f (hb.2.2.2.1 z hz)
  exact ⟨hsf hbp, hsf hba⟩

/-- The numbers of one splay step fit. -/
theorem splayStepOk_tree {h K k : ℕ} {V R : ℤ} (C : NumCtx h K k V R)
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag} {t : AuxTree}
    (hT : TreeB s t k V R) {x : ℕ} (hx : x ∈ t.toList) (hxr : x ≠ t.rootId)
    (hclean : ∀ u ∈ t.pathTo x, (s.nodes u).rev = false ∧ (s.nodes u).tag = pathPayload.idTag) :
    SplayStepOk (pathOk h K) pathPayload s x := by
  have hpx := SubtreeInv_par_eq_parentIn hT.inv.nodup hT.inv.sub hx
  obtain ⟨hpm, -, hpath⟩ := AuxTree.parentIn_mem_and_depth (p₀ := 0) hT.inv.nodup hx hxr
  have hpp := SubtreeInv_par_eq_parentIn hT.inv.nodup hT.inv.sub hpm
  have hp_path : t.parentIn x 0 ∈ t.pathTo x := by
    rw [hpath]; exact List.mem_append.mpr (Or.inl (AuxTree.self_mem_pathTo hpm))
  have hclean_p : ∀ u ∈ t.pathTo (t.parentIn x 0), (s.nodes u).rev = false ∧
      (s.nodes u).tag = pathPayload.idTag := fun u hu =>
    hclean u (by rw [hpath]; exact List.mem_append.mpr (Or.inl hu))
  -- the second rotation of a double step
  have second : ∀ a ∈ t.pathTo x, a ≠ t.rootId →
      (∀ u ∈ t.pathTo a, (s.nodes u).rev = false ∧ (s.nodes u).tag = pathPayload.idTag) →
      RotateOk (pathOk h K) pathPayload (rotate pathPayload s a) x := by
    intro a ha har hca
    have ham := AuxTree.mem_pathTo ha
    have hT' := rotate_treeB hT ham har hca
    obtain ⟨-, hperm, -, -, -, hrt⟩ := rotate_preserves pathPayload_laws hT.inv ham har hca
    refine rotateOk_tree C hT' (hperm.mem_iff.mpr hx) fun u hu => ?_
    have hu' := AuxTree.rotateAt_pathTo_subset hT.inv.nodup hx ha u hu
    rw [(hrt u (AuxTree.mem_pathTo hu')).1, (hrt u (AuxTree.mem_pathTo hu')).2]
    exact hclean u hu'
  unfold SplayStepOk
  simp only [hpx, hpp]
  split_ifs with hg hzz
  · exact rotateOk_tree C hT hx hclean
  · have hpr : t.parentIn x 0 ≠ t.rootId := by
      intro h; apply hg; rw [h]; exact parentIn_rootId 0
    exact ⟨rotateOk_tree C hT hpm hclean_p, second _ hp_path hpr hclean_p⟩
  · exact ⟨rotateOk_tree C hT hx hclean, second _ (AuxTree.self_mem_pathTo hx) hxr hclean⟩

/-- The numbers of the rotations of a splay fit. -/
theorem splayLoopOk_tree {h K k : ℕ} {V R : ℤ} (C : NumCtx h K k V R) :
    ∀ (fuel : ℕ) {s : SplayState (Option PathEdgeValue) PathSummary PathTag} {t : AuxTree}
      {x : ℕ}, TreeB s t k V R → x ∈ t.toList →
      (∀ u ∈ t.pathTo x, (s.nodes u).rev = false ∧ (s.nodes u).tag = pathPayload.idTag) →
      SplayLoopOk (pathOk h K) pathPayload s fuel x
  | 0, _, _, _, _, _, _ => trivial
  | fuel + 1, s, t, x, hT, hx, hclean => by
    intro _ hp
    have hxr : x ≠ t.rootId := by
      intro h; apply hp
      rw [SubtreeInv_par_eq_parentIn hT.inv.nodup hT.inv.sub hx, h]; exact parentIn_rootId 0
    refine ⟨splayStepOk_tree C hT hx hxr hclean, ?_⟩
    obtain ⟨t', ht', hperm, hev, -, -, hrt, hsub, -, -⟩ :=
      splayStep_preserves pathPayload_laws hT.inv hx hxr hclean
    have hT' : TreeB (splayStep pathPayload s x) t' k V R := by
      refine ⟨ht', hev ▸ hT.val, fun y hy => ?_, by rw [countNodes_perm hperm]; exact hT.size⟩
      have hy' := hperm.mem_iff.mp hy
      rw [splayStep_charge hT.inv hx hxr hclean hT.size y hy']
      exact hT.chg y hy'
    refine splayLoopOk_tree C fuel hT' (hperm.mem_iff.mpr hx) fun u hu => ?_
    have hu' := hsub u hu
    rw [(hrt u (AuxTree.mem_pathTo hu')).1, (hrt u (AuxTree.mem_pathTo hu')).2]
    exact hclean u hu'

/-- Pushing the path to `x` keeps the bounds. -/
theorem pushPath_treeB {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {t : AuxTree} {k : ℕ} {V R : ℤ} (hT : TreeB s t k V R) {x F : ℕ} (hx : x ∈ t.toList)
    (hF : t.depthOf x < F) :
    ∃ t₁, TreeB (pushPath pathPayload s F x) t₁ k V R ∧ t₁.toList.Perm t.toList ∧
      (∀ u ∈ t₁.pathTo x, ((pushPath pathPayload s F x).nodes u).rev = false ∧
        ((pushPath pathPayload s F x).nodes u).tag = pathPayload.idTag) := by
  obtain ⟨t₁, ht₁, hperm₁, -, -, hpath₁, -, hclean₁, -, -, hev₁⟩ :=
    pushPath_preserves pathPayload_laws hT.inv hx hF
  have hk₁ : t₁.countNodes ≤ k := by rw [countNodes_perm hperm₁]; exact hT.size
  refine ⟨t₁, ⟨ht₁, hev₁ ▸ hT.val, fun y hy => ?_, hk₁⟩, hperm₁, hclean₁⟩
  have hy' := hperm₁.mem_iff.mp hy
  rw [charge_eq_route ht₁ hy hk₁]
  unfold route
  rw [hpath₁ y]
  refine (pathTagRouteMagnitude_pushPath_le hT.inv hx hF hy').trans ?_
  have := hT.chg y hy'
  rwa [charge_eq_route hT.inv hy' hT.size] at this

/-- The numbers of the pushes of a splay fit. -/
theorem pushPathOk_tree {h K k : ℕ} {V R : ℤ} (C : NumCtx h K k V R)
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag} {t : AuxTree}
    (hT : TreeB s t k V R) :
    ∀ F x, x ∈ t.toList → t.depthOf x < F → PushPathOk (pathOk h K) pathPayload s F x
  | 0, _, _, hF => absurd hF (Nat.not_lt_zero _)
  | F + 1, x, hx, hF => by
    intro _
    by_cases hp : (s.nodes x).par = 0
    · refine ⟨fun h => absurd hp h, ?_⟩
      simp only [hp, ↓reduceIte]
      exact pushDownOk_tree C hT hx
    have hpx := SubtreeInv_par_eq_parentIn hT.inv.nodup hT.inv.sub hx
    have hxr : x ≠ t.rootId := by
      intro h; apply hp; rw [hpx, h]; exact parentIn_rootId 0
    obtain ⟨hpm, hdep, -⟩ := AuxTree.parentIn_mem_and_depth (p₀ := 0) hT.inv.nodup hx hxr
    rw [← hpx] at hpm hdep
    refine ⟨fun _ => pushPathOk_tree C hT F _ hpm (by omega), ?_⟩
    simp only [hp, ↓reduceIte]
    obtain ⟨t₁, hT₁, hperm₁, -⟩ := pushPath_treeB hT hpm (F := F) (by omega)
    exact pushDownOk_tree C hT₁ (hperm₁.mem_iff.mpr hx)

/-- The numbers of a splay fit. -/
theorem splayOk_tree {h K k : ℕ} {V R : ℤ} (C : NumCtx h K k V R)
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag} {t : AuxTree}
    (hT : TreeB s t k V R) {x F : ℕ} (hx : x ∈ t.toList) (hF : t.depthOf x < F) :
    SplayOk (pathOk h K) pathPayload s F x := by
  intro _
  refine ⟨pushPathOk_tree C hT F x hx hF, ?_⟩
  obtain ⟨t₁, hT₁, hperm₁, hclean₁⟩ := pushPath_treeB hT hx hF
  exact splayLoopOk_tree C F hT₁ (hperm₁.mem_iff.mpr hx) hclean₁

end MinCostFlow.LinkCut.PathTree
