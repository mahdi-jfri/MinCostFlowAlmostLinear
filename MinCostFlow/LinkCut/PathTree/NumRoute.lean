module

public import MinCostFlow.LinkCut.PathTree.NumNode
public import MinCostFlow.LinkCut.PathTree.Descend
public import MinCostFlow.LinkCut.SplayOps

/-!
# Tag routes through a splay

The bound of `NumNode` needs the tag route of every node: the tag sizes on the way from the
root of its tree down to it. A splay changes the shape of the tree, so we read the route from
the parent pointers instead (`charge`): the list `chainList` of `Descend` walks from a node up
to its root. In a tree that meets `TreeInv`, this list is the path from the root
(`chainList_eq_pathTo`), so the charge is the route.

A splay first pushes the tags on the path to `x` (no route grows:
`pathTagRouteMagnitude_pushPath_le`), then rotates. A rotation only moves nodes whose tags are
already pushed, so no charge changes (`rotate_charge`, from `pathTagRouteMagnitude_rotate_eq`).
The main result is `splay_charge_le`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathTree

open MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.SplayState

variable {α σ τ : Type*}

/-- In a tree that meets `TreeInv`, the parent walk from `y` read from the top is the path from
the root to `y`. -/
theorem chainList_eq_pathTo {P : LctPayload α σ τ} {s : SplayState α σ τ} {t : AuxTree}
    (ht : TreeInv P s t) :
    ∀ k y, y ∈ t.toList → t.depthOf y < k → chainList s k y = t.pathTo y
  | 0, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | k + 1, y, hy, hk => by
    have hy0 : y ≠ 0 := SubtreeInv_nonZero ht.sub hy
    have hpar := SubtreeInv_par_eq_parentIn ht.nodup ht.sub hy
    by_cases hr : y = t.rootId
    · have hp0 : (s.nodes y).par = 0 := by rw [hpar, hr]; exact parentIn_rootId 0
      cases t with
      | leaf => simp [AuxTree.toList] at hy
      | node id l r =>
        simp only [AuxTree.rootId] at hr
        subst hr
        simp [chainList, hy0, hp0, AuxTree.pathTo]
    · obtain ⟨hpm, hdep, hpath⟩ := AuxTree.parentIn_mem_and_depth (p₀ := 0) ht.nodup hy hr
      have hp0 : (s.nodes y).par ≠ 0 := by
        rw [hpar]; exact SubtreeInv_nonZero ht.sub hpm
      have ih := chainList_eq_pathTo ht k _ hpm (by omega)
      rw [hpath, ← ih, ← hpar]
      simp [chainList, hy0, hp0]

theorem chainList_eq_pathTo' {P : LctPayload α σ τ} {s : SplayState α σ τ} {t : AuxTree}
    (ht : TreeInv P s t) {k y : ℕ} (hy : y ∈ t.toList) (hk : t.countNodes ≤ k) :
    chainList s k y = t.pathTo y :=
  chainList_eq_pathTo ht k y hy (lt_of_lt_of_le (depthOf_lt_countNodes hy) hk)

/-- The tag route of `y` read from the parent pointers. -/
def charge (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (k y : ℕ) : ℤ :=
  pathTagRouteMagnitude s (chainList s k y)

theorem charge_eq_route {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {t : AuxTree} (ht : TreeInv pathPayload s t) {k y : ℕ} (hy : y ∈ t.toList)
    (hk : t.countNodes ≤ k) : charge s k y = route s t y := by
  unfold charge route
  rw [chainList_eq_pathTo' ht hy hk]

theorem countNodes_perm {t t' : AuxTree} (h : t'.toList.Perm t.toList) :
    t'.countNodes = t.countNodes := by
  rw [← AuxTree.length_toList, ← AuxTree.length_toList, h.length_eq]

/-- A rotation at a node whose path is pushed changes no charge. -/
theorem rotate_charge {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {t : AuxTree} (ht : TreeInv pathPayload s t) {a k : ℕ} (ha : a ∈ t.toList)
    (hclean : ∀ u ∈ t.pathTo a, (s.nodes u).rev = false ∧ (s.nodes u).tag = pathPayload.idTag)
    (hk : t.countNodes ≤ k) :
    ∀ y ∈ t.toList, charge (rotate pathPayload s a) k y = charge s k y := by
  intro y hy
  by_cases hr : a = t.rootId
  · have hp0 : (s.nodes a).par = 0 := by
      rw [SubtreeInv_par_eq_parentIn ht.nodup ht.sub ha, hr]; exact parentIn_rootId 0
    have : rotate pathPayload s a = s := by
      unfold rotate; simp [hp0]
    rw [this]
  obtain ⟨ht', hperm, -, -, -, -⟩ := rotate_preserves pathPayload_laws ht ha hr hclean
  rw [charge_eq_route ht' (hperm.mem_iff.mpr hy) (by rw [countNodes_perm hperm]; exact hk),
    charge_eq_route ht hy hk]
  exact pathTagRouteMagnitude_rotate_eq ht ha hr hclean

/-- Two rotations, first at a node `a` on the path to `x`, then at `x`. -/
theorem rotate2_charge {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {t : AuxTree} (ht : TreeInv pathPayload s t) {a x k : ℕ} (hx : x ∈ t.toList)
    (ha : a ∈ t.pathTo x) (har : a ≠ t.rootId)
    (hclean : ∀ u ∈ t.pathTo x, (s.nodes u).rev = false ∧ (s.nodes u).tag = pathPayload.idTag)
    (hclean_a : ∀ u ∈ t.pathTo a, (s.nodes u).rev = false ∧ (s.nodes u).tag = pathPayload.idTag)
    (hk : t.countNodes ≤ k) :
    ∀ y ∈ t.toList,
      charge (rotate pathPayload (rotate pathPayload s a) x) k y = charge s k y := by
  have ham : a ∈ t.toList := AuxTree.mem_pathTo ha
  obtain ⟨ht₁, hperm₁, -, -, -, hrt₁⟩ := rotate_preserves pathPayload_laws ht ham har hclean_a
  have hclean₁ : ∀ u ∈ (t.rotateAt a).pathTo x, ((rotate pathPayload s a).nodes u).rev = false ∧
      ((rotate pathPayload s a).nodes u).tag = pathPayload.idTag := by
    intro u hu
    have hu' := AuxTree.rotateAt_pathTo_subset ht.nodup hx ha u hu
    rw [(hrt₁ u (AuxTree.mem_pathTo hu')).1, (hrt₁ u (AuxTree.mem_pathTo hu')).2]
    exact hclean u hu'
  have hk₁ : (t.rotateAt a).countNodes ≤ k := by rw [countNodes_perm hperm₁]; exact hk
  intro y hy
  rw [rotate_charge ht₁ (hperm₁.mem_iff.mpr hx) hclean₁ hk₁ y (hperm₁.mem_iff.mpr hy)]
  exact rotate_charge ht ham hclean_a hk y hy

/-- A splay step changes no charge. -/
theorem splayStep_charge {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {t : AuxTree} (ht : TreeInv pathPayload s t) {x k : ℕ} (hx : x ∈ t.toList)
    (hxr : x ≠ t.rootId)
    (hclean : ∀ u ∈ t.pathTo x, (s.nodes u).rev = false ∧ (s.nodes u).tag = pathPayload.idTag)
    (hk : t.countNodes ≤ k) :
    ∀ y ∈ t.toList, charge (splayStep pathPayload s x) k y = charge s k y := by
  have hx0 : x ≠ 0 := SubtreeInv_nonZero ht.sub hx
  have hpx := SubtreeInv_par_eq_parentIn ht.nodup ht.sub hx
  obtain ⟨hpm, -, hpath⟩ := AuxTree.parentIn_mem_and_depth (p₀ := 0) ht.nodup hx hxr
  set p := t.parentIn x 0 with hp_def
  have hp0 : p ≠ 0 := SubtreeInv_nonZero ht.sub hpm
  have hpp := SubtreeInv_par_eq_parentIn ht.nodup ht.sub hpm
  have hp_path : p ∈ t.pathTo x := by
    rw [hpath]; exact List.mem_append.mpr (Or.inl (AuxTree.self_mem_pathTo hpm))
  have hx_path : x ∈ t.pathTo x := AuxTree.self_mem_pathTo hx
  unfold splayStep
  simp only [hx0, ↓reduceIte, hpx, hp0]
  by_cases hg : t.parentIn p 0 = 0
  · simp only [hpp, hg, ↓reduceIte]
    exact rotate_charge ht hx hclean hk
  · have hpr : p ≠ t.rootId := by
      intro h; apply hg; rw [h]; exact parentIn_rootId 0
    simp only [hpp, hg, ↓reduceIte]
    split
    · refine rotate2_charge ht hx hp_path hpr hclean (fun u hu => hclean u ?_) hk
      rw [hpath]; exact List.mem_append.mpr (Or.inl hu)
    · exact rotate2_charge ht hx hx_path hxr hclean hclean hk

/-- The rotations of a splay change no charge. -/
theorem splayLoop_charge {k : ℕ} :
    ∀ (fuel : ℕ) {s : SplayState (Option PathEdgeValue) PathSummary PathTag} {t : AuxTree}
      {x : ℕ}, TreeInv pathPayload s t → x ∈ t.toList →
      (∀ u ∈ t.pathTo x, (s.nodes u).rev = false ∧ (s.nodes u).tag = pathPayload.idTag) →
      t.countNodes ≤ k →
      ∀ y ∈ t.toList, charge (splayLoop pathPayload s fuel x) k y = charge s k y
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | fuel + 1, s, t, x, ht, hx, hclean, hk, y, hy => by
    have hx0 : x ≠ 0 := SubtreeInv_nonZero ht.sub hx
    unfold splayLoop
    by_cases hp : (s.nodes x).par = 0
    · simp [hx0, hp]
    simp only [hx0, hp, ↓reduceIte]
    have hxr : x ≠ t.rootId := by
      intro h; apply hp
      rw [SubtreeInv_par_eq_parentIn ht.nodup ht.sub hx, h]; exact parentIn_rootId 0
    obtain ⟨t', ht', hperm, -, -, -, hrt, hsub, -, -⟩ :=
      splayStep_preserves pathPayload_laws ht hx hxr hclean
    have hclean' : ∀ u ∈ t'.pathTo x, ((splayStep pathPayload s x).nodes u).rev = false ∧
        ((splayStep pathPayload s x).nodes u).tag = pathPayload.idTag := by
      intro u hu
      have hu' := hsub u hu
      rw [(hrt u (AuxTree.mem_pathTo hu')).1, (hrt u (AuxTree.mem_pathTo hu')).2]
      exact hclean u hu'
    rw [splayLoop_charge fuel ht' (hperm.mem_iff.mpr hx) hclean'
      (by rw [countNodes_perm hperm]; exact hk) y (hperm.mem_iff.mpr hy)]
    exact splayStep_charge ht hx hxr hclean hk y hy

/-- A splay does not raise any charge in the tree. -/
theorem splay_charge_le {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {t : AuxTree} (ht : TreeInv pathPayload s t) {x F k : ℕ} (hx : x ∈ t.toList)
    (hF : t.depthOf x < F) (hk : t.countNodes ≤ k) :
    ∀ y ∈ t.toList, charge (splay pathPayload s F x) k y ≤ charge s k y := by
  intro y hy
  have hx0 : x ≠ 0 := SubtreeInv_nonZero ht.sub hx
  obtain ⟨t₁, ht₁, hperm₁, -, -, hpath₁, -, hclean₁, -, -, -⟩ :=
    pushPath_preserves pathPayload_laws ht hx hF
  have hk₁ : t₁.countNodes ≤ k := by rw [countNodes_perm hperm₁]; exact hk
  have hsp : splay pathPayload s F x = splayLoop pathPayload (pushPath pathPayload s F x) F x := by
    simp [splay, hx0]
  rw [hsp, splayLoop_charge F ht₁ (hperm₁.mem_iff.mpr hx) hclean₁ hk₁ y (hperm₁.mem_iff.mpr hy),
    charge_eq_route ht₁ (hperm₁.mem_iff.mpr hy) hk₁, charge_eq_route ht hy hk]
  unfold route
  rw [hpath₁ y]
  exact pathTagRouteMagnitude_pushPath_le ht hx hF hy

end MinCostFlow.LinkCut.PathTree
