module

public import MinCostFlow.LinkCut.PathTree.NumSplay
public import MinCostFlow.LinkCut.ForestExposeSpec
import MinCostFlow.LinkCut.ForestReversals

/-!
# Bounds on a whole forest

`ForestB st trees V R` says that every evaluated value of the forest is at most `V` and every
tag charge is at most `R`. Each auxiliary tree then meets `TreeB` (`forestB_treeB`), so the
numbers a splay computes fit (`NumSplay`).

This file shows that the two steps of an expose keep `ForestB`, and that their numbers fit:

* `splay_num`: a splay in one tree. Its values only move, and no charge grows.
* `detach_num`: cutting off the right subtree of a root with a pushed tag. Each new route is
  part of an old one.

Both steps leave the trees they do not touch alone, so those charges stay
(`charge_keep`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathTree

open MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.SplayState
  MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.Path

/-- The evaluated values of the forest are at most `V`, and its tag charges at most `R`. -/
structure ForestB (st : PathTreeState) (trees : List AuxTree) (V R : ℤ) : Prop where
  val : ∀ p ∈ forestPairs pathPayload st.splay trees, ValB V p.2
  chg : ∀ t ∈ trees, ∀ y ∈ t.toList, charge st.splay (2 * st.n + 1) y ≤ R

theorem tree_size {st : PathTreeState} {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees fl d) {t : AuxTree} (ht : t ∈ trees) :
    t.countNodes ≤ 2 * st.n + 1 := by
  have h1 := tree_length_le_active ht
  have h2 := active_length_le_two_mul W.activeNodup W.activeValid
  rw [AuxTree.length_toList] at h1
  omega

theorem forestB_treeB {st : PathTreeState} {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees fl d) {V R : ℤ} (hB : ForestB st trees V R)
    {t : AuxTree} (ht : t ∈ trees) : TreeB st.splay t (2 * st.n + 1) V R :=
  ⟨W.treesInv t ht, fun p hp => hB.val p (List.mem_flatMap.mpr ⟨t, ht, hp⟩), hB.chg t ht,
    tree_size W ht⟩

/-- A tree whose nodes do not change keeps its charges. -/
theorem charge_keep {s s' : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {t : AuxTree} (ht : TreeInv pathPayload s t) (ht' : TreeInv pathPayload s' t) {k : ℕ}
    (hk : t.countNodes ≤ k) (hkeep : ∀ u ∈ t.toList, s'.nodes u = s.nodes u) {y : ℕ}
    (hy : y ∈ t.toList) : charge s' k y = charge s k y := by
  rw [charge_eq_route ht' hy hk, charge_eq_route ht hy hk]
  unfold route pathTagRouteMagnitude
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [hkeep u (AuxTree.mem_pathTo hu)]

theorem sumFits_of_bound {h K : ℕ} {B : ℤ}
    {nd : SplayNode (Option PathEdgeValue) PathSummary PathTag} (hb : PathNodeBound B nd)
    (hr : Room h K B) : PathSummaryFits h K nd.sum := by
  have hB := bound_nonneg hb
  have f {z : ℤ} (hz : |z| ≤ B) : Num.Fits h K z := fits_of_abs (by linarith) hr
  refine ⟨f hb.2.1, f hb.2.2.1, ?_⟩
  cases hz : nd.sum.detector with
  | none => trivial
  | some z => exact f (hb.2.2.2.1 z hz)

/-- The summary of a node of a bounded tree fits. -/
theorem sumFits_tree {h K k : ℕ} {V R : ℤ} (C : NumCtx h K k V R)
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag} {t : AuxTree}
    (hT : TreeB s t k V R) {y : ℕ} (hy : y ∈ t.toList) : PathSummaryFits h K (s.nodes y).sum :=
  sumFits_of_bound (treeB_bound hT C.hV C.hR C.hk y hy) C.room

/-- A splay in one tree: its numbers fit, and the forest keeps its bounds. -/
theorem splay_num {h K : ℕ} {V R : ℤ} {st : PathTreeState} {trees : List AuxTree}
    {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith pathPayload st trees fl d)
    (hB : ForestB st trees V R) (C : NumCtx h K (2 * st.n + 1) V R)
    {t : AuxTree} {x : ℕ} (ht : t ∈ trees) (hx : x ∈ t.toList) :
    let s' := splay pathPayload st.splay (2 * st.n + 1) x
    let st' : PathTreeState := ⟨st.n, s', st.freeHead⟩
    SplayOk (pathOk h K) pathPayload st.splay (2 * st.n + 1) x ∧
    ∃ t', t' ≠ .leaf ∧ t'.rootId = x ∧ t'.toList.Perm t.toList ∧
      (s'.nodes x).ppar = (st.splay.nodes t.rootId).ppar ∧
      (s'.nodes x).rev = false ∧ (s'.nodes x).tag = pathPayload.idTag ∧
      LctInvWith pathPayload st' (t' :: trees.erase t) fl d ∧
      ForestB st' (t' :: trees.erase t) V R ∧
      (∀ u ∉ t.toList, s'.nodes u = st.splay.nodes u) := by
  intro s' st'
  have hT := forestB_treeB W hB ht
  have hdep : t.depthOf x < 2 * st.n + 1 :=
    lt_of_lt_of_le (depthOf_lt_countNodes hx) hT.size
  refine ⟨splayOk_tree C hT hx hdep, ?_⟩
  rcases lctSplayTree_spec pathPayload_laws W ht hx with
    ⟨t', hne, hrt, hperm, hpp, hrev, htag, hW1, -, hfp, -, hout, -⟩
  refine ⟨t', hne, hrt, hperm, hpp, hrev, htag, hW1, ⟨?_, ?_⟩, hout⟩
  · intro p hp
    exact hB.val p (hfp.mem_iff.mp hp)
  · intro c hc y hy
    rcases List.mem_cons.mp hc with rfl | hc
    · have hy' := hperm.mem_iff.mp hy
      exact (splay_charge_le hT.inv hx hdep hT.size y hy').trans (hB.chg _ ht y hy')
    · have hct := List.mem_of_mem_erase hc
      have hdisj : ∀ u ∈ c.toList, u ∉ t.toList := fun u hu =>
        erase_flatMap_disjoint_of_nodup ht W.activeNodup u (List.mem_flatMap.mpr ⟨c, hc, hu⟩)
      change charge s' (2 * st.n + 1) y ≤ R
      rw [charge_keep (W.treesInv c hct) (hW1.treesInv c (List.mem_cons_of_mem _ hc))
        (tree_size W hct) (fun u hu => hout u (hdisj u hu)) hy]
      exact hB.chg c hct y hy

/-- Cutting off the right subtree of a root with a pushed tag: the numbers fit, and the forest
keeps its bounds. -/
theorem detach_num {h K : ℕ} {V R : ℤ} {st : PathTreeState} {trees : List AuxTree}
    {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith pathPayload st trees fl d)
    (hB : ForestB st trees V R) (C : NumCtx h K (2 * st.n + 1) V R)
    {x : ℕ} {L Rt : AuxTree} (ht : AuxTree.node x L Rt ∈ trees)
    (hrev : (st.splay.nodes x).rev = false) (htag : (st.splay.nodes x).tag = pathPayload.idTag) :
    let s' := detachRight pathPayload st.splay x
    let st' : PathTreeState := { st with splay := s' }
    let trees' := if Rt = .leaf then trees else
      AuxTree.node x L .leaf :: Rt :: trees.erase (.node x L Rt)
    DetachRightOk (pathOk h K) pathPayload st.splay x ∧
      LctInvWith pathPayload st' trees' fl d ∧ ForestB st' trees' V R := by
  intro s' st' trees'
  have W1 := (detachRight_spec pathPayload_laws W ht hrev htag).1
  have hTI := W.treesInv _ ht
  obtain ⟨-, -, -, -, -, -, -, hout⟩ := detachRight_preserves pathPayload_laws hTI hrev htag
  have hfp := forestPairs_perm_detachRight pathPayload_laws ht hTI hrev htag W.activeNodup
  have hright : (st.splay.nodes x).right = Rt.rootId := hTI.sub.2.2.1
  have hB' : ForestB st' trees' V R := by
    refine ⟨fun p hp => hB.val p (hfp.mem_iff.mp hp), ?_⟩
    by_cases hRl : Rt = .leaf
    · have hs' : s' = st.splay := by
        have : (st.splay.nodes x).right = 0 := by rw [hright, hRl]; rfl
        simp [s', detachRight, this]
      intro c hc y hy
      have hc' : c ∈ trees := by simpa [trees', hRl] using hc
      change charge s' (2 * st.n + 1) y ≤ R
      rw [hs']
      exact hB.chg c hc' y hy
    intro c hc y hy
    change charge s' (2 * st.n + 1) y ≤ R
    have hc' : c ∈ AuxTree.node x L .leaf :: Rt :: trees.erase (.node x L Rt) := by
      simpa [trees', hRl] using hc
    have hW1t := W1.treesInv c hc
    have hsz := tree_size W1 hc
    have hold : ∀ z ∈ (AuxTree.node x L Rt).toList, charge st.splay (2 * st.n + 1) z ≤ R :=
      hB.chg _ ht
    have hsz0 := tree_size W ht
    rcases List.mem_cons.mp hc' with rfl | hc'
    · rw [charge_eq_route hW1t hy hsz]
      have hy' : y = x ∨ y ∈ L.toList := by
        simp only [AuxTree.toList, List.mem_append, List.mem_singleton, List.not_mem_nil,
          or_false] at hy
        tauto
      unfold route
      rw [(pathTagRouteMagnitude_rightSplice_retained (s := st.splay) (right := Rt) hy').1]
      have hyT : y ∈ (AuxTree.node x L Rt).toList := by
        rcases hy' with rfl | hy' <;> simp [AuxTree.toList, *]
      have := hold y hyT
      rwa [charge_eq_route hTI hyT hsz0] at this
    rcases List.mem_cons.mp hc' with rfl | hc'
    · rw [charge_eq_route hW1t hy hsz]
      unfold route
      rw [pathTagRouteMagnitude_detachRight hTI htag hy]
      have hyT : y ∈ (AuxTree.node x L c).toList := by simp [AuxTree.toList, hy]
      have := hold y hyT
      rwa [charge_eq_route hTI hyT hsz0] at this
    · have hct := List.mem_of_mem_erase hc'
      have hdisj : ∀ u ∈ c.toList, u ∉ (AuxTree.node x L Rt).toList := fun u hu =>
        erase_flatMap_disjoint_of_nodup ht W.activeNodup u (List.mem_flatMap.mpr ⟨c, hc', hu⟩)
      rw [charge_keep (W.treesInv c hct) hW1t (tree_size W hct) (fun u hu => hout u (hdisj u hu))
        hy]
      exact hB.chg c hct y hy
  refine ⟨?_, W1, hB'⟩
  intro hx0 hr0
  have hRl : Rt ≠ .leaf := by rintro rfl; exact hr0 hright
  have hmem : AuxTree.node x L .leaf ∈ trees' := by simp [trees', hRl]
  have hsum := sumFits_tree C (forestB_treeB W1 hB' hmem) (y := x) (by simp [AuxTree.toList])
  change PathSummaryFits h K (pullSum pathPayload (detachRightMid st.splay x) x)
  have : (s'.nodes x).sum = pullSum pathPayload (detachRightMid st.splay x) x := by
    simp only [s', detachRight_eq hx0 hr0, pull_nodes_self hx0]
  rw [← this]
  exact hsum

/-- Hanging a tree below a root with a pushed tag: the numbers fit, and the forest keeps its
bounds. -/
theorem attach_num {h K : ℕ} {V R : ℤ} {st : PathTreeState} {trees : List AuxTree}
    {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith pathPayload st trees fl d)
    (hB : ForestB st trees V R) (C : NumCtx h K (2 * st.n + 1) V R)
    {u : ℕ} {Lu tx : AuxTree} (htu : AuxTree.node u Lu .leaf ∈ trees) (htx : tx ∈ trees)
    (hne : AuxTree.node u Lu .leaf ≠ tx)
    (hrev : (st.splay.nodes u).rev = false) (htag : (st.splay.nodes u).tag = pathPayload.idTag)
    (hpp : (st.splay.nodes tx.rootId).ppar = u) :
    let s' := attachRight pathPayload st.splay u tx.rootId
    let st' : PathTreeState := { st with splay := s' }
    let trees' := AuxTree.node u Lu tx :: ((trees.erase (.node u Lu .leaf)).erase tx)
    AttachRightOk (pathOk h K) pathPayload st.splay u tx.rootId ∧
      LctInvWith pathPayload st' trees' fl d ∧ ForestB st' trees' V R := by
  intro s' st' trees'
  have W1 := (attachRight_spec pathPayload_laws W htu htx hne hrev htag hpp).1
  have hTu := W.treesInv _ htu
  have hTx := W.treesInv _ htx
  have hx_ne := W.treesNonEmpty _ htx
  have hdisj_er := erase_flatMap_disjoint_of_nodup htu W.activeNodup
  have htx_er : tx ∈ trees.erase (.node u Lu .leaf) := (List.mem_erase_of_ne hne.symm).mpr htx
  have hdisj_u_x : ∀ a ∈ (AuxTree.node u Lu .leaf).toList, a ∉ tx.toList := fun a ha hax =>
    hdisj_er a (List.mem_flatMap.mpr ⟨tx, htx_er, hax⟩) ha
  obtain ⟨-, -, -, -, -, hout⟩ :=
    attachRight_preserves pathPayload_laws hTu hrev htag hTx hx_ne rfl hdisj_u_x
  have hfp := forestPairs_perm_attachRight pathPayload_laws W.treesNonEmpty htu htx hne hTu hrev
    htag hTx hx_ne W.activeNodup
  have hnd_er : ((trees.erase (.node u Lu .leaf)).flatMap AuxTree.toList).Nodup := by
    have hp := (List.perm_cons_erase htu).flatMap_right AuxTree.toList
    have := hp.nodup_iff.mp W.activeNodup
    rw [List.flatMap_cons] at this
    exact (List.nodup_append.mp this).2.1
  have hdisj_x := erase_flatMap_disjoint_of_nodup htx_er hnd_er
  have hmem_new : AuxTree.node u Lu tx ∈ trees' := List.mem_cons_self
  have hB' : ForestB st' trees' V R := by
    refine ⟨fun p hp => hB.val p (hfp.mem_iff.mp hp), ?_⟩
    intro c hc y hy
    change charge s' (2 * st.n + 1) y ≤ R
    have hW1t := W1.treesInv c hc
    have hsz := tree_size W1 hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · rw [charge_eq_route hW1t hy hsz]
      unfold route
      by_cases hyx : y ∈ tx.toList
      · rw [pathTagRouteMagnitude_attachRight hW1t.nodup htag hyx]
        have := hB.chg tx htx y hyx
        rwa [charge_eq_route hTx hyx (tree_size W htx)] at this
      · have hy' : y = u ∨ y ∈ Lu.toList := by
          simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hy
          tauto
        rw [(pathTagRouteMagnitude_rightSplice_retained (s := st.splay) (right := tx) hy').2]
        have hyT : y ∈ (AuxTree.node u Lu .leaf).toList := by
          rcases hy' with rfl | hy' <;> simp [AuxTree.toList, *]
        have := hB.chg _ htu y hyT
        rwa [charge_eq_route hTu hyT (tree_size W htu)] at this
    · have hc1 := List.mem_of_mem_erase hc'
      have hct := List.mem_of_mem_erase hc1
      have hkeep : ∀ z ∈ c.toList, s'.nodes z = st.splay.nodes z := by
        intro z hz
        apply hout
        have h1 : z ∉ (AuxTree.node u Lu .leaf).toList :=
          hdisj_er z (List.mem_flatMap.mpr ⟨c, hc1, hz⟩)
        have h2 : z ∉ tx.toList := hdisj_x z (List.mem_flatMap.mpr ⟨c, hc', hz⟩)
        simp only [AuxTree.toList, List.mem_append, List.mem_singleton, List.not_mem_nil,
          or_false] at h1 ⊢
        tauto
      rw [charge_keep (W.treesInv c hct) hW1t (tree_size W hct) hkeep hy]
      exact hB.chg c hct y hy
  refine ⟨?_, W1, hB'⟩
  intro hu0
  have hsum := sumFits_tree C (forestB_treeB W1 hB' hmem_new) (y := u) (by simp [AuxTree.toList])
  change PathSummaryFits h K (pullSum pathPayload (attachRightMid st.splay u tx.rootId) u)
  have : (s'.nodes u).sum = pullSum pathPayload (attachRightMid st.splay u tx.rootId) u := by
    simp only [s', attachRight_eq hu0, pull_nodes_self hu0]
  rw [← this]
  exact hsum

end MinCostFlow.LinkCut.PathTree
