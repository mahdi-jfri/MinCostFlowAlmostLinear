module

public import MinCostFlow.LSF.Program.DecompGenChar

/-!
# A label for the piece of each tree edge

The pieces of the decomposition are edge-disjoint and cover the tree, so every tree edge lies in
exactly one piece. A program records this by a label on the parent edge of each non-root vertex
`x`, computed from the root down:
* if `x` was put in a closed batch of its parent `p`, or `p` is the root, the label is
  `(p, bidx x)`;
* otherwise the bag of `x` was merged into the bag of `p`, and `x` gets the label of `p`.

The label `(y, b)` names the piece `pieceOfLab`: the batch piece `batchPiece y b` when `b < nb y`,
and the bag of the root when `y` is the root and `b = nb y`. `label_spec` shows that two parent
edges have the same label exactly when they lie in the same piece of the final decomposition.

The proof follows the label down from the root (`inPart_lab`): the vertex `x` lies in the part of
the piece that comes from one child bag, and then both `x` and its parent lie in the piece
(`inPart_piece`). Different labels name different pieces (`inPart_inj`), because the piece
`batchPiece y b` has top vertex `y` and contains the children of `y` with number `b`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program.DecompGen

open MinCostFlow MinCostFlow.LSF

variable {T : MGraph} {r : ℕ} {bidx nb : ℕ → ℕ}

/-- The piece named by a label. -/
noncomputable def pieceOfLab (T : MGraph) (r : ℕ) (bidx nb : ℕ → ℕ) (yb : ℕ × ℕ) : Finset ℕ :=
  if yb.2 < nb yb.1 then batchPiece T r bidx nb yb.1 yb.2 else bagSet T r bidx nb yb.1

/-- `x` lies in the piece named `yb`, inside the bag of a child of the top vertex (or inside the
root bag), and is not the top vertex. -/
def InPart (T : MGraph) (r : ℕ) (bidx nb : ℕ → ℕ) (yb : ℕ × ℕ) (x : ℕ) : Prop :=
  (yb.2 < nb yb.1 ∧ ∃ c ∈ childSet T r yb.1, bidx c = yb.2 ∧ x ∈ bagSet T r bidx nb c) ∨
  (yb.1 = r ∧ yb.2 = nb r ∧ x ∈ bagSet T r bidx nb r ∧ x ≠ r)

/-- The labels, computed from the root down. -/
def IsLabeling (T : MGraph) (r : ℕ) (bidx nb : ℕ → ℕ) (lab : ℕ → ℕ × ℕ) : Prop :=
  ∀ x ∈ T.V, x ≠ r → lab x =
    if bidx x < nb (parent T r x) ∨ parent T r x = r then (parent T r x, bidx x)
    else lab (parent T r x)

lemma bagSet_sub (u : ℕ) : bagSet T r bidx nb u ⊆ subtree T r u := by
  classical
  unfold bagSet
  exact Finset.filter_subset _ _

lemma mem_childSet_parent (hT : IsRootedTree T r) {x : ℕ} (hx : x ∈ T.V) (hxr : x ≠ r) :
    x ∈ childSet T r (parent T r x) := by
  rw [mem_childSet, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton]
  exact ⟨⟨mem_subtree_iff.mpr ⟨hx, isAncestor_parent hT hx hxr⟩,
    fun h => parent_ne_self hT hx hxr h.symm⟩, rfl⟩

lemma childSet_facts (hT : IsRootedTree T r) {y c : ℕ} (hc : c ∈ childSet T r y) :
    c ∈ T.V ∧ c ≠ r ∧ parent T r c = y ∧ c ≠ y ∧ y ∈ T.V ∧ IsAncestor T r y c := by
  have hc' := mem_childSet.mp hc
  rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hc'
  have hcV := (mem_subtree_iff.mp hc'.1.1).1
  have hcr : c ≠ r := by
    intro h
    have hyc := (mem_subtree_iff.mp hc'.1.1).2
    rw [h] at hyc
    have hyV := isAncestor_mem hT hT.2 hyc
    exact hc'.1.2 (h.trans (isAncestor_antisymm hT hT.2 hyV (isAncestor_root hT hyV) hyc))
  refine ⟨hcV, hcr, hc'.2, hc'.1.2, ?_, (mem_subtree_iff.mp hc'.1.1).2⟩
  rw [← hc'.2]; exact parent_mem hT hcV

lemma batchPiece_sub (hT : IsRootedTree T r) {y : ℕ} (hy : y ∈ T.V) (b : ℕ) :
    batchPiece T r bidx nb y b ⊆ subtree T r y := by
  classical
  intro x hx
  rw [batchPiece, Finset.mem_insert, Finset.mem_biUnion] at hx
  rcases hx with rfl | ⟨c, hc, hxc⟩
  · exact mem_subtree_iff.mpr ⟨hy, isAncestor_refl T r x⟩
  · exact Finset.sdiff_subset (subtree_child_subset hT (mem_childSet.mp
      (Finset.mem_filter.mp hc).1) (bagSet_sub c hxc))

/-- One step up inside a bag. -/
lemma merged_parent (hT : IsRootedTree T r) {c x : ℕ} (hx : x ∈ subtree T r c) (hxc : x ≠ c)
    (hm : Merged T r bidx nb c x) :
    x ≠ r ∧ parent T r x ∈ subtree T r c ∧ Merged T r bidx nb c (parent T r x) := by
  have hxV := (mem_subtree_iff.mp hx).1
  have hcx := (mem_subtree_iff.mp hx).2
  have hcV := isAncestor_mem hT hxV hcx
  have hxr : x ≠ r := by
    intro h
    rw [h] at hcx hxc
    exact hxc (isAncestor_antisymm hT hT.2 hcV (isAncestor_root hT hcV) hcx)
  have hcp : IsAncestor T r c (parent T r x) := by
    rcases (isAncestor_iff_eq_or_parent hT hxV).mp hcx with h | ⟨_, h⟩
    · exact absurd h.symm hxc
    · exact h
  refine ⟨hxr, mem_subtree_iff.mpr ⟨parent_mem hT hxV, hcp⟩, fun y hcy hyc hyp => ?_⟩
  exact hm y hcy hyc (isAncestor_trans hT hxV hyp (isAncestor_parent hT hxV hxr))

/-- One step down into a bag: a merged child. -/
lemma merged_extend (hT : IsRootedTree T r) {c x : ℕ} (hxV : x ∈ T.V) (hxr : x ≠ r)
    (hp : parent T r x ∈ subtree T r c) (hm : Merged T r bidx nb c (parent T r x))
    (hb : bidx x = nb (parent T r x)) :
    x ∈ subtree T r c ∧ Merged T r bidx nb c x := by
  have hcp := (mem_subtree_iff.mp hp).2
  refine ⟨mem_subtree_iff.mpr ⟨hxV, isAncestor_trans hT hxV hcp (isAncestor_parent hT hxV hxr)⟩,
    fun y hcy hyc hyx => ?_⟩
  rcases (isAncestor_iff_eq_or_parent hT hxV).mp hyx with h | ⟨_, h⟩
  · rw [h]; exact hb
  · exact hm y hcy hyc h

lemma child_eq_of_mem_subtree (hT : IsRootedTree T r) {y c c' : ℕ} (hc : c ∈ childSet T r y)
    (hc' : c' ∈ childSet T r y) (hcc : c ∈ subtree T r c') : c = c' := by
  obtain ⟨hcV, hcr, hpc, -, -, -⟩ := childSet_facts hT hc
  obtain ⟨hc'V, hc'r, hpc', -, -, -⟩ := childSet_facts hT hc'
  by_contra hne
  have hd := children_subtree_disjoint hT hcV hc'V hcr hc'r hpc hpc' hne
  exact Finset.disjoint_left.mp hd (mem_subtree_iff.mpr ⟨hcV, isAncestor_refl T r c⟩) hcc

/-- The labels name the part of the piece that holds `x`. -/
lemma inPart_lab (hT : IsRootedTree T r) {lab : ℕ → ℕ × ℕ} (hlab : IsLabeling T r bidx nb lab)
    (hle : ∀ x ∈ T.V, x ≠ r → bidx x ≤ nb (parent T r x)) :
    ∀ d x, depth T r x = d → x ∈ T.V → x ≠ r → InPart T r bidx nb (lab x) x := by
  classical
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro x hd hxV hxr
    have hpV := parent_mem hT hxV
    have hxC := mem_childSet_parent hT hxV hxr
    have hxbag : x ∈ bagSet T r bidx nb x := by
      rw [bagSet, Finset.mem_filter]
      exact ⟨mem_subtree_iff.mpr ⟨hxV, isAncestor_refl T r x⟩, merged_self hT bidx nb hxV⟩
    rw [hlab x hxV hxr]
    by_cases h1 : bidx x < nb (parent T r x)
    · rw [ite_eq_left <| (Or.inl h1)]
      exact Or.inl ⟨h1, x, hxC, rfl, hxbag⟩
    · have hb : bidx x = nb (parent T r x) := le_antisymm (hle x hxV hxr) (not_lt.mp h1)
      by_cases h2 : parent T r x = r
      · rw [ite_eq_left <| (Or.inr h2)]
        refine Or.inr ⟨h2, by rw [hb, h2], ?_, hxr⟩
        have hrr : parent T r x ∈ subtree T r r := by
          rw [h2]; exact mem_subtree_iff.mpr ⟨hT.2, isAncestor_refl T r r⟩
        have hmr : Merged T r bidx nb r (parent T r x) := by
          rw [h2]; exact merged_self hT bidx nb hT.2
        obtain ⟨hs, hm⟩ := merged_extend hT hxV hxr hrr hmr hb
        rw [bagSet, Finset.mem_filter]; exact ⟨hs, hm⟩
      · rw [ite_eq_right <| (by tauto)]
        have hdp := depth_parent hT hxV hxr
        have hIH := ih (depth T r (parent T r x)) (by omega) (parent T r x) rfl hpV h2
        rcases hIH with ⟨hlt, c, hc, hbc, hpc⟩ | ⟨hy, hbn, hpr, hpne⟩
        · refine Or.inl ⟨hlt, c, hc, hbc, ?_⟩
          rw [bagSet, Finset.mem_filter] at hpc ⊢
          exact merged_extend hT hxV hxr hpc.1 hpc.2 hb
        · refine Or.inr ⟨hy, hbn, ?_, hxr⟩
          rw [bagSet, Finset.mem_filter] at hpr ⊢
          exact merged_extend hT hxV hxr hpr.1 hpr.2 hb

/-- `x` and its parent lie in the named piece. -/
lemma inPart_piece (hT : IsRootedTree T r) {yb : ℕ × ℕ} {x : ℕ}
    (h : InPart T r bidx nb yb x) :
    x ≠ r ∧ x ∈ pieceOfLab T r bidx nb yb ∧ parent T r x ∈ pieceOfLab T r bidx nb yb := by
  classical
  rcases h with ⟨hlt, c, hc, hbc, hxc⟩ | ⟨hy, hbn, hxr, hxne⟩
  · rw [pieceOfLab, ite_eq_left <| hlt, batchPiece]
    have hcmem : c ∈ (childSet T r yb.1).filter (fun c => bidx c = yb.2) :=
      Finset.mem_filter.mpr ⟨hc, hbc⟩
    obtain ⟨hcV, hcr, hpc, -, -, -⟩ := childSet_facts hT hc
    have hxc' := hxc
    rw [bagSet, Finset.mem_filter] at hxc'
    have hxr : x ≠ r := by
      intro h
      have hcx := (mem_subtree_iff.mp hxc'.1).2
      rw [h] at hcx
      exact hcr (isAncestor_antisymm hT hcV hT.2 hcx (isAncestor_root hT hcV))
    refine ⟨hxr, Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨c, hcmem, hxc⟩), ?_⟩
    by_cases hxeq : x = c
    · rw [hxeq, hpc]; exact Finset.mem_insert_self _ _
    · obtain ⟨-, hps, hpm⟩ := merged_parent hT hxc'.1 hxeq hxc'.2
      refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨c, hcmem, ?_⟩)
      rw [bagSet, Finset.mem_filter]; exact ⟨hps, hpm⟩
  · have hnot : ¬ yb.2 < nb yb.1 := by rw [hy, hbn]; exact lt_irrefl _
    rw [pieceOfLab, ite_eq_right <| hnot, hy]
    refine ⟨hxne, hxr, ?_⟩
    rw [bagSet, Finset.mem_filter] at hxr ⊢
    exact (merged_parent hT hxr.1 hxne hxr.2).2

/-- Different labels name different pieces. -/
lemma inPart_inj (hT : IsRootedTree T r) {yb yb' : ℕ × ℕ} {x x' : ℕ}
    (h : InPart T r bidx nb yb x) (h' : InPart T r bidx nb yb' x')
    (heq : pieceOfLab T r bidx nb yb = pieceOfLab T r bidx nb yb') : yb = yb' := by
  classical
  -- the batch piece `(y, b)` contains a child `c` of `y` of number `b`
  have hbp : ∀ {y b c}, b < nb y → c ∈ childSet T r y → bidx c = b →
      c ∈ pieceOfLab T r bidx nb (y, b) := by
    intro y b c hlt hc hbc
    obtain ⟨hcV, -, -, -, -, -⟩ := childSet_facts hT hc
    rw [pieceOfLab, ite_eq_left <| hlt, batchPiece]
    refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, hbc⟩, ?_⟩)
    rw [bagSet, Finset.mem_filter]
    exact ⟨mem_subtree_iff.mpr ⟨hcV, isAncestor_refl T r c⟩, merged_self hT bidx nb hcV⟩
  -- in the batch piece `(y, b)`, a child of `y` has number `b`
  have hbp_child : ∀ {y b c}, b < nb y → c ∈ childSet T r y →
      c ∈ pieceOfLab T r bidx nb (y, b) → bidx c = b := by
    intro y b c hlt hc hcP
    obtain ⟨-, -, -, hcy, -, -⟩ := childSet_facts hT hc
    rw [pieceOfLab, ite_eq_left <| hlt, batchPiece, Finset.mem_insert, Finset.mem_biUnion] at hcP
    rcases hcP with h | ⟨c', hc', hcc'⟩
    · exact absurd h hcy
    · have hc'f := Finset.mem_filter.mp hc'
      rw [child_eq_of_mem_subtree hT hc hc'f.1 (bagSet_sub c' hcc')]
      exact hc'f.2
  -- the top vertex of the batch piece `(y, b)`
  have htop : ∀ {y b}, b < nb y → y ∈ T.V →
      y ∈ pieceOfLab T r bidx nb (y, b) ∧ pieceOfLab T r bidx nb (y, b) ⊆ subtree T r y := by
    intro y b hlt hy
    rw [pieceOfLab, ite_eq_left <| hlt]
    exact ⟨by rw [batchPiece]; exact Finset.mem_insert_self _ _, batchPiece_sub hT hy b⟩
  have hroot : ∀ {b}, ¬ b < nb r →
      pieceOfLab T r bidx nb (r, b) = bagSet T r bidx nb r := by
    intro b hb; rw [pieceOfLab, ite_eq_right <| hb]
  -- the root bag contains no child of the root with a closed batch
  have hrbag : ∀ {c}, c ∈ childSet T r r → c ∈ bagSet T r bidx nb r → bidx c = nb r := by
    intro c hc hcb
    obtain ⟨-, -, hpc, hcr, -, hrc⟩ := childSet_facts hT hc
    rw [bagSet, Finset.mem_filter] at hcb
    have := hcb.2 c hrc hcr (isAncestor_refl T r c)
    rw [hpc] at this; exact this
  obtain ⟨y, b⟩ := yb
  obtain ⟨y', b'⟩ := yb'
  rcases h with ⟨hlt, c, hc, hbc, -⟩ | ⟨hy, hbn, -, -⟩ <;>
    rcases h' with ⟨hlt', c', hc', hbc', -⟩ | ⟨hy', hbn', -, -⟩
  · dsimp only at hlt hc hbc hlt' hc' hbc'
    obtain ⟨-, -, -, -, hyV, -⟩ := childSet_facts hT hc
    obtain ⟨-, -, -, -, hy'V, -⟩ := childSet_facts hT hc'
    obtain ⟨hyP, hPy⟩ := htop hlt hyV
    obtain ⟨hy'P, hPy'⟩ := htop hlt' hy'V
    rw [heq] at hyP hPy
    have hyy : y = y' := isAncestor_antisymm hT hyV hy'V
      (mem_subtree_iff.mp (hPy hy'P)).2 (mem_subtree_iff.mp (hPy' hyP)).2
    subst hyy
    have hcP := hbp hlt hc hbc
    rw [heq] at hcP
    rw [← hbc, hbp_child hlt' hc hcP]
  · dsimp only at hlt hc hbc hy' hbn'
    rw [hy', hbn'] at heq ⊢
    obtain ⟨-, -, -, -, hyV, -⟩ := childSet_facts hT hc
    obtain ⟨-, hPy⟩ := htop hlt hyV
    rw [heq, hroot (lt_irrefl _)] at hPy
    have hrP : r ∈ bagSet T r bidx nb r := by
      rw [bagSet, Finset.mem_filter]
      exact ⟨mem_subtree_iff.mpr ⟨hT.2, isAncestor_refl T r r⟩, merged_self hT bidx nb hT.2⟩
    have hyr : y = r := isAncestor_antisymm hT hyV hT.2
      (mem_subtree_iff.mp (hPy hrP)).2 (isAncestor_root hT hyV)
    rw [hyr] at hlt hc heq
    have hcP := hbp hlt hc hbc
    rw [heq, hroot (lt_irrefl _)] at hcP
    have := hrbag hc hcP
    omega
  · dsimp only at hlt' hc' hbc' hy hbn
    rw [hy, hbn] at heq ⊢
    obtain ⟨-, -, -, -, hyV, -⟩ := childSet_facts hT hc'
    obtain ⟨-, hPy⟩ := htop hlt' hyV
    rw [← heq, hroot (lt_irrefl _)] at hPy
    have hrP : r ∈ bagSet T r bidx nb r := by
      rw [bagSet, Finset.mem_filter]
      exact ⟨mem_subtree_iff.mpr ⟨hT.2, isAncestor_refl T r r⟩, merged_self hT bidx nb hT.2⟩
    have hyr : y' = r := isAncestor_antisymm hT hyV hT.2
      (mem_subtree_iff.mp (hPy hrP)).2 (isAncestor_root hT hyV)
    rw [hyr] at hlt' hc' heq
    have hcP := hbp hlt' hc' hbc'
    rw [← heq, hroot (lt_irrefl _)] at hcP
    have := hrbag hc' hcP
    omega
  · dsimp only at hy hbn hy' hbn'
    rw [hy, hbn, hy', hbn']

/-- A parent edge lies in every piece that holds both of its ends. -/
lemma parentEdge_mem_inducedEdges (hT : IsRootedTree T r) {x : ℕ} {P : Finset ℕ}
    (hxV : x ∈ T.V) (hxr : x ≠ r) (hx : x ∈ P) (hp : parent T r x ∈ P) :
    parentEdge T r x ∈ inducedEdges T P := by
  have hend := parentEdge_endpoints hT hxV hxr
  have ht : T.tail (parentEdge T r x) ∈ ({x, parent T r x} : Set ℕ) := by
    rw [← hend]; exact Set.mem_insert _ _
  have hh : T.head (parentEdge T r x) ∈ ({x, parent T r x} : Set ℕ) := by
    rw [← hend]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  rw [inducedEdges, Finset.mem_filter]
  refine ⟨parentEdge_mem hT hxV hxr, ?_, ?_⟩
  · rcases ht with h | h
    · rw [h]; exact hx
    · rw [Set.mem_singleton_iff.mp h]; exact hp
  · rcases hh with h | h
    · rw [h]; exact hx
    · rw [Set.mem_singleton_iff.mp h]; exact hp

/-- The labels of the parent edges name their pieces in the final decomposition, and two parent
edges have the same label exactly when they lie in the same piece. -/
theorem label_spec (hT : IsRootedTree T r) (ν : ℕ → ℝ) (θ : ℝ) {L : ℕ → List ℕ}
    (hL : IsChildLists T r L) (s : ℕ → ℝ)
    (hrun : ∀ u ∈ T.V, OnlineRun θ s bidx 0 0 (L u) (nb u) (s u - ν u))
    {lab : ℕ → ℕ × ℕ} (hlab : IsLabeling T r bidx nb lab)
    (G : MGraph) (w : ℕ → ℝ) (k : ℝ)
    (hdisj : ∀ C₁ ∈ finalDecomp G w k T r (progDecomp ν θ L T.V.card r).1
        (progDecomp ν θ L T.V.card r).2,
      ∀ C₂ ∈ finalDecomp G w k T r (progDecomp ν θ L T.V.card r).1
        (progDecomp ν θ L T.V.card r).2,
      C₁ ≠ C₂ → Disjoint (inducedEdges T C₁) (inducedEdges T C₂)) :
    (∀ x ∈ T.V, x ≠ r →
      pieceOfLab T r bidx nb (lab x) ∈ finalDecomp G w k T r (progDecomp ν θ L T.V.card r).1
        (progDecomp ν θ L T.V.card r).2 ∧
      parentEdge T r x ∈ inducedEdges T (pieceOfLab T r bidx nb (lab x))) ∧
    (∀ x ∈ T.V, x ≠ r → ∀ x' ∈ T.V, x' ≠ r →
      (lab x = lab x' ↔ ∃ P ∈ finalDecomp G w k T r (progDecomp ν θ L T.V.card r).1
        (progDecomp ν θ L T.V.card r).2,
        parentEdge T r x ∈ inducedEdges T P ∧ parentEdge T r x' ∈ inducedEdges T P)) := by
  classical
  set D := progDecomp ν θ L T.V.card r with hD
  have hroot_card : (subtree T r r).card ≤ T.V.card :=
    Finset.card_le_card (fun _ hx => (mem_subtree_iff.mp hx).1)
  obtain ⟨hD2, -, hD1⟩ := progDecomp_char hT ν θ hL s bidx nb hrun T.V.card r hT.2 hroot_card
  have hle : ∀ x ∈ T.V, x ≠ r → bidx x ≤ nb (parent T r x) := by
    intro x hxV hxr
    have hpV := parent_mem hT hxV
    have hxL : x ∈ L (parent T r x) := ((hL _ hpV).2 x).mpr (mem_childSet_parent hT hxV hxr)
    exact ((onlineRun_bounds θ s bidx _ _ _ _ _ (hrun _ hpV)).2 x hxL).2
  have hpart : ∀ x ∈ T.V, x ≠ r → InPart T r bidx nb (lab x) x :=
    fun x hxV hxr => inPart_lab hT hlab hle _ x rfl hxV hxr
  have hmemW : ∀ x ∈ T.V, x ≠ r →
      pieceOfLab T r bidx nb (lab x) ∈ finalDecomp G w k T r D.1 D.2 := by
    intro x hxV hxr
    unfold finalDecomp
    refine Finset.mem_union_left _ ?_
    unfold rootPieces
    rcases hpart x hxV hxr with ⟨hlt, c, hc, -, -⟩ | ⟨hy, hbn, hxb, hxne⟩
    · have hyV := (childSet_facts hT hc).2.2.2.2.1
      have hin : pieceOfLab T r bidx nb (lab x) ∈ D.1 := by
        rw [hD1, pieceOfLab, ite_eq_left hlt]
        exact ⟨(lab x).1, mem_subtree_iff.mpr ⟨hyV, isAncestor_root hT hyV⟩, (lab x).2, hlt, rfl⟩
      split_ifs
      · exact hin
      · exact Finset.mem_insert_of_mem hin
    · have hnot : ¬ (lab x).2 < nb (lab x).1 := by rw [hy, hbn]; exact lt_irrefl _
      have hP : pieceOfLab T r bidx nb (lab x) = D.2 := by
        rw [pieceOfLab, ite_eq_right hnot, hy, hD2]
      rw [hP]
      have hne : D.2 ≠ {r} := by
        intro h
        rw [hD2] at h
        rw [h, Finset.mem_singleton] at hxb
        exact hxne hxb
      rw [ite_eq_right hne]
      exact Finset.mem_insert_self _ _
  have hedge : ∀ x ∈ T.V, x ≠ r →
      parentEdge T r x ∈ inducedEdges T (pieceOfLab T r bidx nb (lab x)) := by
    intro x hxV hxr
    obtain ⟨-, hx, hp⟩ := inPart_piece hT (hpart x hxV hxr)
    exact parentEdge_mem_inducedEdges hT hxV hxr hx hp
  refine ⟨fun x hxV hxr => ⟨hmemW x hxV hxr, hedge x hxV hxr⟩, ?_⟩
  intro x hxV hxr x' hx'V hx'r
  constructor
  · intro heq
    refine ⟨_, hmemW x hxV hxr, hedge x hxV hxr, ?_⟩
    rw [heq]; exact hedge x' hx'V hx'r
  · rintro ⟨P, hP, hxP, hx'P⟩
    have hsame : ∀ y ∈ T.V, y ≠ r → parentEdge T r y ∈ inducedEdges T P →
        pieceOfLab T r bidx nb (lab y) = P := by
      intro y hyV hyr hyP
      by_contra hne
      exact Finset.disjoint_left.mp (hdisj _ (hmemW y hyV hyr) P hP hne) (hedge y hyV hyr) hyP
    exact inPart_inj hT (hpart x hxV hxr) (hpart x' hx'V hx'r)
      ((hsame x hxV hxr hxP).trans (hsame x' hx'V hx'r hx'P).symm)

end MinCostFlow.LSF.Program.DecompGen
