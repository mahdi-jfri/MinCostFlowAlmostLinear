module

public import MinCostFlow.LinkCut.Prog.MathForestCutWrite

/-!
# The representation after the write of `cut`

Before the write, `cut` has the auxiliary tree `ed (x + 1) (y + 1)` for the exposed path
`[x + 1, ed, y + 1]`, with path parent `0`. The write (`lctCutWriteMem`) gives the two vertex
nodes parent `0` and clears `ed`. This file proves that the result is again a full
representation (`LctExposeInvs`) of the same slots, with `ed` moved from the active edges to the
free slots and with the three one-node trees `x + 1`, `y + 1` and `ed` in place of the old tree
(`cut_invs_after_write`). It also computes the new represented parent map: it is the old one with
the entries of `x + 1`, `y + 1` and `ed` set to `0`.

The key fact is that only `y + 1` has `ed` as its represented parent
(`cut_par_eq_ed_only`): a vertex with parent `ed` is an endpoint of the edge of `ed`, and `x + 1` is
the root. So no other auxiliary tree hangs below `ed`, and every remaining path parent stays an
active node.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section CutAfter

private lemma findSome_cut_cons_pos {mem : ℕ → ℕ} {nb z : ℕ} {s : AuxTree} {ss : List AuxTree}
    (hz : z ∈ s.evalInorder (revFlag mem nb) false) :
    (s :: ss).findSome? (fun t =>
      let seq := t.evalInorder (revFlag mem nb) false
      if z ∈ seq then some (listParentFrom (nodeField mem nb t.rootId OFF_PPAR) seq z) else none) =
      some (listParentFrom (nodeField mem nb s.rootId OFF_PPAR)
        (s.evalInorder (revFlag mem nb) false) z) := by
  simp [List.findSome?, hz]

private lemma findSome_cut_cons_neg {mem : ℕ → ℕ} {nb z : ℕ} {s : AuxTree} {ss : List AuxTree}
    (hz : z ∉ s.evalInorder (revFlag mem nb) false) :
    (s :: ss).findSome? (fun t =>
      let seq := t.evalInorder (revFlag mem nb) false
      if z ∈ seq then some (listParentFrom (nodeField mem nb t.rootId OFF_PPAR) seq z) else none) =
      ss.findSome? (fun t =>
        let seq := t.evalInorder (revFlag mem nb) false
        if z ∈ seq then some (listParentFrom (nodeField mem nb t.rootId OFF_PPAR) seq z) else none) := by
  simp [List.findSome?, hz]

private lemma evalInorder_single (rev : ℕ → Bool) (z : ℕ) :
    (AuxTree.node z .leaf .leaf).evalInorder rev false = [z] := by
  cases hr : rev z <;> simp [AuxTree.evalInorder]

/-- The write of `cut` leaves every address below the node array unchanged, except the head of
the free stack. -/
theorem lctCutWriteMem_below {mem : ℕ → ℕ} {b x y oldFree ed a : ℕ}
    (hed1 : 1 ≤ ed) (ha : a < lctNodesBase b) (hne : a ≠ b + LCT_HDR_FREE) :
    lctCutWriteMem mem (lctNodesBase b) b x y oldFree ed a = mem a := by
  have hmul : NODE_STRIDE ≤ NODE_STRIDE * ed := Nat.le_mul_of_pos_right _ hed1
  apply lctCutWriteMem_outside hne
  · have : lctNodesBase b ≤ lctNodesBase b + NODE_STRIDE * (x + 1) + OFF_PARENT := by omega
    omega
  · have : lctNodesBase b ≤ lctNodesBase b + NODE_STRIDE * (y + 1) + OFF_PARENT := by omega
    omega
  · left; omega

/-- The write of `cut` leaves every address above the node array unchanged. -/
theorem lctCutWriteMem_above {mem : ℕ → ℕ} {b cap x y oldFree ed a : ℕ}
    (hx : x + 1 ≤ cap) (hy : y + 1 ≤ cap) (hed : ed ≤ cap)
    (ha : lctNodesBase b + NODE_STRIDE * (cap + 1) ≤ a) :
    lctCutWriteMem mem (lctNodesBase b) b x y oldFree ed a = mem a := by
  have hx' : NODE_STRIDE * (x + 1 + 1) ≤ NODE_STRIDE * (cap + 1) := Nat.mul_le_mul_left _ (by omega)
  have hy' : NODE_STRIDE * (y + 1 + 1) ≤ NODE_STRIDE * (cap + 1) := Nat.mul_le_mul_left _ (by omega)
  have he' : NODE_STRIDE * (ed + 1) ≤ NODE_STRIDE * (cap + 1) := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_add, Nat.mul_one] at hx' hy' he'
  have hpar : OFF_PARENT < NODE_STRIDE := by decide
  apply lctCutWriteMem_outside
  · unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE at *; omega
  · omega
  · omega
  · right; omega

private lemma cut_vertex_case {z x y a c : ℕ} (hz1 : 1 ≤ z)
    (hend : a = x ∧ c = y ∨ a = y ∧ c = x) (hpe : a = z - 1 ∨ c = z - 1) (hnx : z ≠ x + 1) :
    z = y + 1 := by
  omega

/-- In an association list with distinct keys, a key determines its value. -/
theorem cut_key_inj : ∀ {l : List (ℕ × ForestEdge)}, (l.map Prod.fst).Nodup →
    ∀ {a : ℕ} {e₁ e₂ : ForestEdge}, (a, e₁) ∈ l → (a, e₂) ∈ l → e₁ = e₂ := by
  intro l hnd a e₁ e₂ h1 h2
  induction l with
  | nil => simp at h1
  | cons p tl ih =>
      rw [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.1 h1 with h1eq | h1' <;> rcases List.mem_cons.1 h2 with h2eq | h2'
      · exact (Prod.mk.inj (h1eq.trans h2eq.symm)).2
      · subst h1eq
        exact absurd (List.mem_map.2 ⟨(a, e₂), h2', rfl⟩) hnd.1
      · subst h2eq
        exact absurd (List.mem_map.2 ⟨(a, e₁), h1', rfl⟩) hnd.1
      · exact ih hnd.2 h1' h2'

/-- In the represented forest before the write, only `y + 1` has `ed` as its parent. -/
theorem cut_par_eq_ed_only {w h L P b n x y ed : ℕ} {freeEdges : List ℕ}
    {edgeMap : List (ℕ × ForestEdge)} {trees : List AuxTree} {mem : ℕ → ℕ} {e : ForestEdge}
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap trees mem)
    (hslots : (edgeMap.map Prod.fst ++ freeEdges).Perm ((List.range n).map (n + 1 + ·)))
    (hed_em : (ed, e) ∈ edgeMap)
    (he_end : (e.u = x ∧ e.v = y) ∨ (e.u = y ∧ e.v = x))
    (hpar_x : lctAuxParent mem (lctNodesBase b) (lctCap n) (x + 1) = 0)
    (hedge_lt : ∀ p ∈ edgeMap, p.2.u < n ∧ p.2.v < n)
    {z : ℕ} (hz1 : 1 ≤ z) (hz2 : z ≤ lctCap n)
    (hz : lctAuxParent mem (lctNodesBase b) (lctCap n) z = ed) : z = y + 1 := by
  have hed_ok := hi.edgeOk (ed, e) hed_em
  have hed_n : n + 1 ≤ ed := hed_ok.1
  have hnd : (edgeMap.map Prod.fst ++ freeEdges).Nodup :=
    hslots.nodup_iff.2 ((List.nodup_range).map (fun _ _ h => by omega))
  have hnd_em : (edgeMap.map Prod.fst).Nodup := hnd.of_append_left
  by_cases hzn : z ≤ n
  · have hv := hi.subdivOk.2.2.1 (z - 1) (by omega)
    have hz' : z - 1 + 1 = z := by omega
    rw [hz'] at hv
    rcases hv with h0 | ⟨p, hp, hpe, hpp⟩
    · omega
    · have hp1 : p.1 = ed := hpp.symm.trans hz
      have hpe' : p.2 = e := cut_key_inj hnd_em (by rw [← hp1]; exact hp) hed_em
      rw [hpe'] at hpe
      have hnx : z ≠ x + 1 := fun hzx => by
        rw [hzx, hpar_x] at hz; omega
      exact cut_vertex_case hz1 he_end hpe hnx
  · have hslot : z ∈ edgeMap.map Prod.fst ++ freeEdges := by
      refine hslots.symm.subset (List.mem_map.2 ⟨z - n - 1, List.mem_range.2 ?_, by omega⟩)
      unfold lctCap at hz2; omega
    rcases List.mem_append.1 hslot with hem | hfr
    · rcases List.mem_map.1 hem with ⟨p, hp, hpz⟩
      have hb := hedge_lt p hp
      rcases hi.subdivOk.2.2.2 p hp with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [hpz, hz] at h1; omega
      · rw [hpz, hz] at h1; omega
    · have h0 := hi.subdivOk.2.1 z hfr
      rw [hz] at h0; omega

/-- Zeroing some entries of a parent map keeps it acyclic. -/
theorem iterParent_zeroed {par par' : ℕ → ℕ} (hp0 : par' 0 = 0)
    (hpar : ∀ z, par' z = 0 ∨ par' z = par z) :
    ∀ k u, iterParent par' k u = 0 ∨ iterParent par' k u = iterParent par k u := by
  intro k
  induction k with
  | zero => intro u; right; rfl
  | succ k ih =>
      intro u
      simp only [iterParent]
      rcases hpar u with h | h
      · left; rw [h, iterParent_zero_fixed hp0]
      · rw [h]; exact ih (par u)

/-- The write of `cut` turns the tree `ed (x + 1) (y + 1)` of the exposed path
`[x + 1, ed, y + 1]` into three one-node trees, moves `ed` to the free slots, and keeps the full
representation invariant. The represented parent map loses exactly the entries of `x + 1`,
`y + 1` and `ed`, and the other trees keep their path parents and in-order sequences. -/
theorem cut_invs_after_write {w h L P b n x y ed : ℕ} {freeEdges : List ℕ}
    {edgeMap : List (ℕ × ForestEdge)} {rest : List AuxTree} {mem₃ : ℕ → ℕ} {e : ForestEdge}
    (hi₃ : LctExposeInvs w h L P b n freeEdges edgeMap
      (AuxTree.node ed (.node (x + 1) .leaf .leaf) (.node (y + 1) .leaf .leaf) :: rest) mem₃)
    (hpp_ed : nodeField mem₃ (lctNodesBase b) ed OFF_PPAR = 0)
    (hev3 : (AuxTree.node ed (.node (x + 1) .leaf .leaf) (.node (y + 1) .leaf .leaf)).evalInorder
      (revFlag mem₃ (lctNodesBase b)) false = [x + 1, ed, y + 1])
    (hed_em : (ed, e) ∈ edgeMap)
    (he_end : (e.u = x ∧ e.v = y) ∨ (e.u = y ∧ e.v = x))
    (hx : x < n) (hy : y < n) (hxy : x ≠ y)
    (hedge_lt : ∀ p ∈ edgeMap, p.2.u < n ∧ p.2.v < n)
    (hslots : (edgeMap.map Prod.fst ++ freeEdges).Perm ((List.range n).map (n + 1 + ·))) :
    let nb := lctNodesBase b
    let cap := lctCap n
    let mem_w := lctCutWriteMem mem₃ nb b x y (mem₃ (b + LCT_HDR_FREE)) ed
    LctExposeInvs w h L P b n (ed :: freeEdges) (edgeMap.filter (fun p => decide (p.1 ≠ ed)))
      (.node (x + 1) .leaf .leaf :: .node (y + 1) .leaf .leaf :: .node ed .leaf .leaf :: rest)
      mem_w ∧
    (∀ z, lctAuxParent mem_w nb cap z =
      if z = ed ∨ z = x + 1 ∨ z = y + 1 then 0 else lctAuxParent mem₃ nb cap z) ∧
    (∀ s ∈ rest, nodeField mem_w nb s.rootId OFF_PPAR = nodeField mem₃ nb s.rootId OFF_PPAR ∧
      s.evalInorder (revFlag mem_w nb) false = s.evalInorder (revFlag mem₃ nb) false) ∧
    mem_w (nb - 1) = mem₃ (nb - 1) ∧
    nodeField mem_w nb (x + 1) OFF_PPAR = 0 ∧ nodeField mem_w nb (y + 1) OFF_PPAR = 0 ∧
    nodeField mem_w nb ed OFF_PPAR = 0 ∧
    lctAuxParent mem₃ nb cap (x + 1) = 0 ∧ lctAuxParent mem₃ nb cap ed = x + 1 ∧
    lctAuxParent mem₃ nb cap (y + 1) = ed := by
  intro nb cap mem_w
  have hnb : nb = lctNodesBase b := rfl
  have hnb3 : 3 ≤ nb := lctNodesBase_ge3 b
  let oldFree := mem₃ (b + LCT_HDR_FREE)
  let t_x := AuxTree.node (x + 1) .leaf .leaf
  let t_y := AuxTree.node (y + 1) .leaf .leaf
  let t_ed := AuxTree.node ed t_x t_y
  let t_f := AuxTree.node ed .leaf .leaf
  have hed_ok := hi₃.edgeOk (ed, e) hed_em
  have hed_n : n + 1 ≤ ed := hed_ok.1
  have hed2 : ed ≤ cap := hed_ok.2.1
  have hed1 : 1 ≤ ed := by omega
  have hx_cap : x + 1 ≤ cap := by dsimp only [cap, lctCap]; omega
  have hy_cap : y + 1 ≤ cap := by dsimp only [cap, lctCap]; omega
  have hxed : x + 1 ≠ ed := by omega
  have hyed : y + 1 ≠ ed := by omega
  have hnd_all : ((t_ed :: rest).flatMap AuxTree.toList).Nodup :=
    hi₃.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  have hdisj : ∀ s ∈ rest, ∀ z ∈ s.toList, z ≠ x + 1 ∧ z ≠ y + 1 ∧ z ≠ ed := by
    intro s hs z hz
    have hz_rest : z ∈ rest.flatMap AuxTree.toList := List.mem_flatMap.2 ⟨s, hs, hz⟩
    have h1 := hnd_all
    rw [List.flatMap_cons, List.nodup_append] at h1
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
      exact h1.2.2 z (by simp [t_ed, t_x, t_y, AuxTree.toList, h]) z hz_rest rfl
  have hnd_em : (edgeMap.map Prod.fst).Nodup :=
    (hslots.nodup_iff.2 ((List.nodup_range).map (fun _ _ h => by omega))).of_append_left
  have hfree_nin : ∀ fe ∈ freeEdges, fe ≠ ed := by
    intro fe hfe heq
    have hnd : (edgeMap.map Prod.fst ++ freeEdges).Nodup :=
      hslots.nodup_iff.2 ((List.nodup_range).map (fun _ _ h => by omega))
    exact List.disjoint_of_nodup_append hnd (List.mem_map.2 ⟨(ed, e), hed_em, rfl⟩) (heq ▸ hfe)
  -- Field facts of the write.
  have hf_other : ∀ z off, 1 ≤ z → off < NODE_STRIDE → z ≠ x + 1 → z ≠ y + 1 → z ≠ ed →
      nodeField mem_w nb z off = nodeField mem₃ nb z off := fun z off hz1 hoff h1 h2 h3 =>
    lctCutWriteMem_nodeField_other hnb hz1 hoff h1 h2 h3
  have hf_x : ∀ off < NODE_STRIDE, off ≠ OFF_PARENT →
      nodeField mem_w nb (x + 1) off = nodeField mem₃ nb (x + 1) off := fun off hoff hne =>
    lctCutWriteMem_nodeField_x_other hnb hoff hne hxy hxed
  have hf_y : ∀ off < NODE_STRIDE, off ≠ OFF_PARENT →
      nodeField mem_w nb (y + 1) off = nodeField mem₃ nb (y + 1) off := fun off hoff hne =>
    lctCutWriteMem_nodeField_y_other hnb hoff hne hxy hyed
  have hf_xp : nodeField mem_w nb (x + 1) OFF_PARENT = 0 :=
    lctCutWriteMem_nodeField_x_parent hxy hxed
  have hf_yp : nodeField mem_w nb (y + 1) OFF_PARENT = 0 :=
    lctCutWriteMem_nodeField_y_parent hyed
  have hf_ed : ∀ off < NODE_STRIDE, nodeField mem_w nb ed off = if off = OFF_EU then oldFree else 0 :=
    fun off hoff => lctCutWriteMem_nodeField_ed hoff
  have hf_ed0 : ∀ off < NODE_STRIDE, off ≠ OFF_EU → nodeField mem_w nb ed off = 0 :=
    fun off hoff hne => by rw [hf_ed off hoff]; simp [hne]
  have hheap : ∀ a, nb + NODE_STRIDE * (cap + 1) ≤ a → mem_w a = mem₃ a := fun a ha =>
    lctCutWriteMem_above hx_cap hy_cap hed2 ha
  have hbelow : ∀ a, a < nb → a ≠ b + LCT_HDR_FREE → mem_w a = mem₃ a := fun a ha hne =>
    lctCutWriteMem_below hed1 ha hne
  have hhp_w : mem_w (nb - 1) = mem₃ (nb - 1) :=
    hbelow _ (by omega) (by rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega)
  have hL_w : mem_w (nb - 3) = mem₃ (nb - 3) :=
    hbelow _ (by omega) (by rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega)
  have hhdr : ∀ off, off < LCT_HDR_SIZE → off ≠ LCT_HDR_FREE → mem_w (b + off) = mem₃ (b + off) :=
    fun off hoff hne => hbelow _ (by rw [hnb]; unfold lctNodesBase; omega)
      (fun h => hne (by omega))
  have hfree_w : mem_w (b + LCT_HDR_FREE) = ed := lctCutWriteMem_hdr_free hnb hed1
  -- The old tree and its children.
  have hted_ok := hi₃.sf.trees_ok t_ed List.mem_cons_self
  have hted_tm : TreeMemMatch w h L mem₃ nb cap t_ed 0 0 := by
    have := hted_ok.2.2
    simpa [t_ed, AuxTree.rootId, hpp_ed] using this
  have hch := TreeMemMatch.children_match hted_tm
  have hpx3 : nodeField mem₃ nb (x + 1) OFF_PPAR = 0 := by
    have h1 := hch.1; rw [TreeMemMatch.eq_2] at h1; exact h1.2.2.2.2.2.1
  have hpy3 : nodeField mem₃ nb (y + 1) OFF_PPAR = 0 := by
    have h2 := hch.2; rw [TreeMemMatch.eq_2] at h2; exact h2.2.2.2.2.2.1
  have hhp_le : mem₃ (nb - 1) ≤ mem_w (nb - 1) := le_of_eq hhp_w.symm
  have hheap' : ∀ a, nb + NODE_STRIDE * (cap + 1) ≤ a → a < mem₃ (nb - 1) → mem_w a = mem₃ a :=
    fun a ha _ => hheap a ha
  have htx_w : TreeMemMatch w h L mem_w nb cap t_x 0 0 :=
    treeMemMatch_reparent_root hch.1 (by simp [t_x, AuxTree.toList]) (fun _ => hf_xp)
      (fun _ => by
        show nodeField mem_w nb (x + 1) OFF_PPAR = 0
        rw [hf_x OFF_PPAR (by decide) (by decide)]; exact hpx3)
      (fun u hu off hoff hroot => by
        simp only [t_x, AuxTree.toList, List.nil_append, List.append_nil,
          List.mem_singleton] at hu
        subst hu
        exact hf_x off hoff (hroot rfl).1) hhp_le hheap'
  have hty_w : TreeMemMatch w h L mem_w nb cap t_y 0 0 :=
    treeMemMatch_reparent_root hch.2 (by simp [t_y, AuxTree.toList]) (fun _ => hf_yp)
      (fun _ => by
        show nodeField mem_w nb (y + 1) OFF_PPAR = 0
        rw [hf_y OFF_PPAR (by decide) (by decide)]; exact hpy3)
      (fun u hu off hoff hroot => by
        simp only [t_y, AuxTree.toList, List.nil_append, List.append_nil,
          List.mem_singleton] at hu
        subst hu
        exact hf_y off hoff (hroot rfl).1) hhp_le hheap'
  have hold_lt : oldFree < 2 ^ w := by
    have hch3 := hi₃.freeChain
    have hcap_w : cap < 2 ^ w := by
      have h1 : nb + NODE_STRIDE * (cap + 1) ≤ mem₃ (nb - 1) := hi₃.sf.2.2.2.1
      have h2 : mem₃ (nb - 1) < 2 ^ w := hi₃.sf.2.2.2.2.2.1
      have : cap < nb + NODE_STRIDE * (cap + 1) := by unfold NODE_STRIDE; omega
      omega
    cases freeEdges with
    | nil =>
        have : oldFree = 0 := hch3
        rw [this]; exact Nat.two_pow_pos w
    | cons fe fs =>
        have h1 : oldFree = fe := hch3.1
        have h2 := (hi₃.freeNodeOk fe List.mem_cons_self).2.1
        rw [h1]; omega
  have htf_w : TreeMemMatch w h L mem_w nb cap t_f 0 0 :=
    treeMemMatch_cleared_slot hed1 hed2 hold_lt hf_ed
  -- The other trees keep their fields.
  have hrest_f : ∀ s ∈ rest, ∀ z ∈ s.toList, ∀ off < NODE_STRIDE,
      nodeField mem_w nb z off = nodeField mem₃ nb z off := by
    intro s hs z hz off hoff
    have hs_tm := (hi₃.sf.trees_ok s (List.mem_cons_of_mem _ hs)).2.2
    have hd := hdisj s hs z hz
    exact hf_other z off (hs_tm.nodup_perm_mem hz).1 hoff hd.1 hd.2.1 hd.2.2
  have hrest_agree : ∀ s ∈ rest,
      nodeField mem_w nb s.rootId OFF_PPAR = nodeField mem₃ nb s.rootId OFF_PPAR ∧
      s.evalInorder (revFlag mem_w nb) false = s.evalInorder (revFlag mem₃ nb) false ∧
      TreeMemMatch w h L mem_w nb cap s 0 (nodeField mem_w nb s.rootId OFF_PPAR) ∧
      evalMemSteps mem_w nb h L s false 0 = evalMemSteps mem₃ nb h L s false 0 := by
    intro s hs
    have hs_in : s ∈ t_ed :: rest := List.mem_cons_of_mem _ hs
    have hs_ok := hi₃.sf.trees_ok s hs_in
    have hs_tm := hs_ok.2.2
    have hs_nd := list_nodup_of_flatMap_nodup hnd_all hs_in
    have hroot_mem := AuxTree.rootId_mem_toList hs_ok.1
    have hpp_s := hrest_f s hs s.rootId hroot_mem OFF_PPAR (by decide)
    have hpar_s : s ≠ .leaf → nodeField mem_w nb s.rootId OFF_PARENT = 0 := fun hne => by
      rw [hrest_f s hs s.rootId hroot_mem OFF_PARENT (by decide)]
      cases hs_eq : s with
      | leaf => exact absurd hs_eq hne
      | node rid sl sr =>
          have htm := hs_tm
          rw [hs_eq] at htm
          exact htm.parent_eq
    refine ⟨hpp_s, ?_, ?_, ?_⟩
    · apply AuxTree.evalInorder_agree
      intro z hz
      simp only [revFlag, hrest_f s hs z hz OFF_REV (by decide)]
    · rw [hpp_s]
      exact treeMemMatch_reparent_root hs_tm hs_nd hpar_s (fun _ => hpp_s)
        (fun z hz off hoff _ => hrest_f s hs z hz off hoff) hhp_le hheap'
    · exact evalMemSteps_agree_of_nonStruct hs_tm hs_nd
        (fun z hz off hoff _ => hrest_f s hs z hz off hoff) hheap' false 0
  -- The splay forest.
  have hperm_w : ((t_x :: t_y :: t_f :: rest).flatMap AuxTree.toList).Perm
      ((List.range cap).map (· + 1)) := by
    refine List.Perm.trans ?_ hi₃.sf.perm
    simp only [List.flatMap_cons, t_x, t_y, t_f, AuxTree.toList, List.nil_append,
      List.append_nil, List.cons_append]
    exact List.Perm.cons _ (List.Perm.swap _ _ _)
  have hsf_w : SplayForestOk w h L mem_w nb cap (t_x :: t_y :: t_f :: rest) := by
    refine ⟨hi₃.sf.1, hi₃.sf.2.1, hnb3, by rw [hhp_w]; exact hi₃.sf.2.2.2.1,
      by rw [hL_w]; exact hi₃.sf.2.2.2.2.1, by rw [hhp_w]; exact hi₃.sf.2.2.2.2.2.1, ?_, ?_,
      hperm_w, ?_⟩
    · intro a ha
      rw [hhp_w] at ha
      rw [hheap a (le_trans hi₃.sf.2.2.2.1 ha)]
      exact hi₃.sf.2.2.2.2.2.2.1 a ha
    · intro off hoff
      have hne : nb + off ≠ b + LCT_HDR_FREE := by
        rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega
      have h1 : nodeField mem_w nb 0 off = nodeField mem₃ nb 0 off := by
        dsimp only [nodeField]
        simp only [Nat.mul_zero, Nat.add_zero]
        apply lctCutWriteMem_outside hne
        · have : NODE_STRIDE ≤ NODE_STRIDE * (x + 1) := Nat.le_mul_of_pos_right _ (by omega)
          intro h; have : off = NODE_STRIDE * (x + 1) + OFF_PARENT := by omega
          omega
        · have : NODE_STRIDE ≤ NODE_STRIDE * (y + 1) := Nat.le_mul_of_pos_right _ (by omega)
          intro h; have : off = NODE_STRIDE * (y + 1) + OFF_PARENT := by omega
          omega
        · left; have : NODE_STRIDE ≤ NODE_STRIDE * ed := Nat.le_mul_of_pos_right _ hed1; omega
      have h2 := hi₃.sf.2.2.2.2.2.2.2.1 off hoff
      dsimp only [nodeField] at h1
      simp only [Nat.mul_zero, Nat.add_zero] at h1
      rw [h1]; exact h2
    · intro t ht
      have hw1 : 0 < 2 ^ w := Nat.two_pow_pos w
      simp only [List.mem_cons] at ht
      rcases ht with rfl | rfl | rfl | hs
      · refine ⟨by simp [t_x], ?_, ?_⟩
        · show nodeField mem_w nb (x + 1) OFF_PPAR < 2 ^ w
          rw [hf_x OFF_PPAR (by decide) (by decide), hpx3]; exact hw1
        · show TreeMemMatch w h L mem_w nb cap t_x 0 (nodeField mem_w nb (x + 1) OFF_PPAR)
          rw [hf_x OFF_PPAR (by decide) (by decide), hpx3]; exact htx_w
      · refine ⟨by simp [t_y], ?_, ?_⟩
        · show nodeField mem_w nb (y + 1) OFF_PPAR < 2 ^ w
          rw [hf_y OFF_PPAR (by decide) (by decide), hpy3]; exact hw1
        · show TreeMemMatch w h L mem_w nb cap t_y 0 (nodeField mem_w nb (y + 1) OFF_PPAR)
          rw [hf_y OFF_PPAR (by decide) (by decide), hpy3]; exact hty_w
      · refine ⟨by simp [t_f], ?_, ?_⟩
        · show nodeField mem_w nb ed OFF_PPAR < 2 ^ w
          rw [hf_ed0 OFF_PPAR (by decide) (by decide)]; exact hw1
        · show TreeMemMatch w h L mem_w nb cap t_f 0 (nodeField mem_w nb ed OFF_PPAR)
          rw [hf_ed0 OFF_PPAR (by decide) (by decide)]; exact htf_w
      · have hs_ok := hi₃.sf.trees_ok t (List.mem_cons_of_mem _ hs)
        have ha := hrest_agree t hs
        exact ⟨hs_ok.1, by rw [ha.1]; exact hs_ok.2.1, ha.2.2.1⟩
  -- The represented parent map.
  have hpx_w : nodeField mem_w nb (x + 1) OFF_PPAR = 0 := by
    rw [hf_x OFF_PPAR (by decide) (by decide)]; exact hpx3
  have hpy_w : nodeField mem_w nb (y + 1) OFF_PPAR = 0 := by
    rw [hf_y OFF_PPAR (by decide) (by decide)]; exact hpy3
  have hped_w : nodeField mem_w nb ed OFF_PPAR = 0 := hf_ed0 OFF_PPAR (by decide) (by decide)
  have hpp_le_3 : ∀ s ∈ t_ed :: rest, nodeField mem₃ nb s.rootId OFF_PPAR ≤ cap :=
    hi₃.ppar_le_cap
  have hpp_le_w : ∀ s ∈ t_x :: t_y :: t_f :: rest, nodeField mem_w nb s.rootId OFF_PPAR ≤ cap := by
    intro s hs
    simp only [List.mem_cons] at hs
    rcases hs with rfl | rfl | rfl | hs
    · show nodeField mem_w nb (x + 1) OFF_PPAR ≤ cap
      rw [hpx_w]; omega
    · show nodeField mem_w nb (y + 1) OFF_PPAR ≤ cap
      rw [hpy_w]; omega
    · show nodeField mem_w nb ed OFF_PPAR ≤ cap
      rw [hped_w]; omega
    · rw [(hrest_agree s hs).1]; exact hpp_le_3 s (List.mem_cons_of_mem _ hs)
  have hrest_find : ∀ z, rest.findSome? (fun t =>
        let seq := t.evalInorder (revFlag mem_w nb) false
        if z ∈ seq then some (listParentFrom (nodeField mem_w nb t.rootId OFF_PPAR) seq z) else none) =
      rest.findSome? (fun t =>
        let seq := t.evalInorder (revFlag mem₃ nb) false
        if z ∈ seq then some (listParentFrom (nodeField mem₃ nb t.rootId OFF_PPAR) seq z) else none) := by
    intro z
    apply findSome?_congr_left
    intro s hs
    have ho := hrest_agree s hs
    simp only [ho.1, ho.2.1]
  have hev_x : t_x.evalInorder (revFlag mem_w nb) false = [x + 1] := evalInorder_single _ _
  have hev_y : t_y.evalInorder (revFlag mem_w nb) false = [y + 1] := evalInorder_single _ _
  have hev_f : t_f.evalInorder (revFlag mem_w nb) false = [ed] := evalInorder_single _ _
  have hev3' : t_ed.evalInorder (revFlag mem₃ nb) false = [x + 1, ed, y + 1] := hev3
  have hpar_eq : ∀ z, lctAuxParent mem_w nb cap z =
      if z = ed ∨ z = x + 1 ∨ z = y + 1 then 0 else lctAuxParent mem₃ nb cap z := by
    intro z
    rw [lctAuxParent_mem_iff_of_trees hsf_w hpp_le_w z]
    by_cases hzx : z = x + 1
    · subst hzx
      rw [findSome_cut_cons_pos (by rw [hev_x]; simp)]
      simp [hev_x, listParentFrom, t_x, AuxTree.rootId, hpx_w]
    · rw [findSome_cut_cons_neg (by rw [hev_x]; simpa using hzx)]
      by_cases hzy : z = y + 1
      · subst hzy
        rw [findSome_cut_cons_pos (by rw [hev_y]; simp)]
        simp [hev_y, listParentFrom, t_y, AuxTree.rootId, hpy_w]
      · rw [findSome_cut_cons_neg (by rw [hev_y]; simpa using hzy)]
        by_cases hze : z = ed
        · subst hze
          rw [findSome_cut_cons_pos (by rw [hev_f]; simp)]
          simp [hev_f, listParentFrom, t_f, AuxTree.rootId, hped_w]
        · have hcond : ¬ (z = ed ∨ z = x + 1 ∨ z = y + 1) := by simp [hzx, hzy, hze]
          simp only [hcond, ↓reduceIte]
          rw [findSome_cut_cons_neg (by rw [hev_f]; simpa using hze), hrest_find z,
                        lctAuxParent_mem_iff_of_trees hi₃.sf hpp_le_3 z,
            findSome_cut_cons_neg (by rw [hev3']; simp [hzx, hzy, hze])]
  have hpar3_x : lctAuxParent mem₃ nb cap (x + 1) = 0 := by
    rw [lctAuxParent_mem_iff_of_trees hi₃.sf hpp_le_3 (x + 1),
      findSome_cut_cons_pos (by rw [hev3']; simp)]
    simp [hev3, listParentFrom, AuxTree.rootId, hpp_ed]
  have hpar3_y : lctAuxParent mem₃ nb cap (y + 1) = ed := by
    rw [lctAuxParent_mem_iff_of_trees hi₃.sf hpp_le_3 (y + 1),
      findSome_cut_cons_pos (by rw [hev3']; simp)]
    have hyx : y + 1 ≠ x + 1 := by omega
    simp [hev3, listParentFrom, hyed, Ne.symm hxy]
  have hpar3_ed : lctAuxParent mem₃ nb cap ed = x + 1 := by
    rw [lctAuxParent_mem_iff_of_trees hi₃.sf hpp_le_3 ed,
      findSome_cut_cons_pos (by rw [hev3']; simp)]
    simp [hev3, listParentFrom, Ne.symm hxed]
  have hpar_keep : ∀ z q, lctAuxParent mem₃ nb cap z = q → q ≠ 0 → q ≠ ed → z ≠ ed →
      lctAuxParent mem_w nb cap z = q := by
    intro z q hz hq0 hqe hze
    rw [hpar_eq z]
    by_cases hc : z = ed ∨ z = x + 1 ∨ z = y + 1
    · exfalso
      rcases hc with h | h | h
      · exact hze h
      · rw [h, hpar3_x] at hz; exact hq0 hz.symm
      · rw [h, hpar3_y] at hz; exact hqe hz.symm
    · simp only [hc, ↓reduceIte]; exact hz
  have honly : ∀ z, 1 ≤ z → z ≤ cap → lctAuxParent mem₃ nb cap z = ed → z = y + 1 :=
    fun z hz1 hz2 hz => cut_par_eq_ed_only hi₃ hslots hed_em he_end hpar3_x hedge_lt hz1 hz2 hz
  -- Field facts outside the parent fields.
  have hf_np : ∀ z off, 1 ≤ z → off < NODE_STRIDE → off ≠ OFF_PARENT → z ≠ ed →
      nodeField mem_w nb z off = nodeField mem₃ nb z off := by
    intro z off hz1 hoff hne hze
    by_cases hzx : z = x + 1
    · subst hzx; exact hf_x off hoff hne
    · by_cases hzy : z = y + 1
      · subst hzy; exact hf_y off hoff hne
      · exact hf_other z off hz1 hoff hzx hzy hze
  have hmem_new : ∀ s ∈ rest, s ∈ t_x :: t_y :: t_f :: rest := fun s hs => by simp [hs]
  refine ⟨⟨?_, ?_, ?_, ?_, hsf_w, ?_, ?_, ?_, ?_, ?_, ?_⟩, hpar_eq,
    fun s hs => ⟨(hrest_agree s hs).1, (hrest_agree s hs).2.1⟩, hhp_w, hpx_w, hpy_w, hped_w,
    hpar3_x, hpar3_ed, hpar3_y⟩
  · rw [hhdr LCT_HDR_N (by decide) (by decide)]; exact hi₃.hdrN
  · rw [hhdr LCT_HDR_CAP (by decide) (by decide)]; exact hi₃.hdrCap
  · rw [hhdr LCT_HDR_L (by decide) (by decide)]; exact hi₃.hdrL
  · rw [hhdr LCT_HDR_P (by decide) (by decide)]; exact hi₃.hdrP
  · -- free chain
    refine ⟨hfree_w, ?_⟩
    rw [hf_ed OFF_EU (by decide)]; simp only [↓reduceIte]
    refine freeSlotChain_agree_of_eu hi₃.freeChain ?_
    intro fe hfe
    have hfe_ok := hi₃.freeNodeOk fe hfe
    exact hf_np fe OFF_EU (by omega) (by decide) (by decide) (hfree_nin fe hfe)
  · -- free slots
    intro fe hfe
    rcases List.mem_cons.1 hfe with rfl | hfe
    · exact ⟨hed_n, hed2, by simp, hped_w, hf_ed0 OFF_ISV (by decide) (by decide),
        hf_ed0 OFF_HASE (by decide) (by decide)⟩
    · rcases hi₃.freeNodeOk fe hfe with ⟨h1, h2, htr, hpp, hisv, hhase⟩
      have hne := hfree_nin fe hfe
      have htr' : AuxTree.node fe .leaf .leaf ∈ rest := by
        rcases List.mem_cons.1 htr with heq | hr
        · exfalso
          have := congrArg AuxTree.toList heq
          simp [AuxTree.toList] at this
        · exact hr
      refine ⟨h1, h2, hmem_new _ htr', ?_, ?_, ?_⟩
      · rw [hf_np fe OFF_PPAR (by omega) (by decide) (by decide) hne]; exact hpp
      · rw [hf_np fe OFF_ISV (by omega) (by decide) (by decide) hne]; exact hisv
      · rw [hf_np fe OFF_HASE (by omega) (by decide) (by decide) hne]; exact hhase
  · -- vertices
    intro v hv
    have hv3 := hi₃.vertexOk v hv
    have hne : v + 1 ≠ ed := by omega
    dsimp only at hv3 ⊢
    rw [hf_np (v + 1) OFF_ISV (by omega) (by decide) (by decide) hne,
      hf_np (v + 1) OFF_HASE (by omega) (by decide) (by decide) hne]
    exact hv3
  · -- active edges
    intro q hq
    rcases List.mem_filter.1 hq with ⟨hqm, hqne⟩
    have hqne' : q.1 ≠ ed := by simpa using hqne
    rcases hi₃.edgeOk q hqm with ⟨h1, h2, hisv, hhe, heid, heu, hev, t, ht, hq_t, st, hst,
      hmatch, hdir⟩
    have hq_bd := hedge_lt q hqm
    have hq_nx : q.1 ≠ x + 1 := by omega
    have hq_ny : q.1 ≠ y + 1 := by omega
    have ht_rest : t ∈ rest := by
      rcases List.mem_cons.1 ht with rfl | hr
      · exfalso
        simp [AuxTree.toList] at hq_t
        omega
      · exact hr
    have hpq : lctAuxParent mem_w nb cap q.1 = lctAuxParent mem₃ nb cap q.1 := by
      rw [hpar_eq]; simp [hq_nx, hq_ny, hqne']
    have hq1 : 1 ≤ q.1 := by omega
    refine ⟨h1, h2, by rw [hf_np q.1 OFF_ISV hq1 (by decide) (by decide) hqne']; exact hisv,
      by rw [hf_np q.1 OFF_HASE hq1 (by decide) (by decide) hqne']; exact hhe,
      by rw [hf_np q.1 OFF_EID hq1 (by decide) (by decide) hqne']; exact heid,
      by rw [hf_np q.1 OFF_EU hq1 (by decide) (by decide) hqne']; exact heu,
      by rw [hf_np q.1 OFF_EV hq1 (by decide) (by decide) hqne']; exact hev,
      t, hmem_new t ht_rest, hq_t, st, by rw [(hrest_agree t ht_rest).2.2.2]; exact hst,
      hmatch, ?_⟩
    have hq0 : q.1 ≠ 0 := by omega
    rcases hdir with ⟨hf, ha, hb⟩ | ⟨hf, ha, hb⟩
    · left
      exact ⟨hf, by rw [hpq]; exact ha,
        hpar_keep _ _ hb hq0 hqne' (by omega)⟩
    · right
      exact ⟨hf, by rw [hpq]; exact ha,
        hpar_keep _ _ hb hq0 hqne' (by omega)⟩
  · -- auxiliary paths
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | rfl | rfl | hs
    · refine ⟨by rw [hev_x]; simp, Or.inl hpx_w, Or.inr ⟨x, hx, by rw [hev_x]; rfl⟩⟩
    · refine ⟨by rw [hev_y]; simp, Or.inl hpy_w, Or.inr ⟨y, hy, by rw [hev_y]; rfl⟩⟩
    · exact ⟨by rw [hev_f]; simp, Or.inl hped_w, Or.inl ⟨List.mem_cons_self, rfl, hped_w⟩⟩
    · have hs3 : t ∈ t_ed :: rest := List.mem_cons_of_mem _ hs
      rcases hi₃.auxPathOk t hs3 with ⟨hne, hpp, hlast⟩
      have hag := hrest_agree t hs
      refine ⟨by rw [hag.2.1]; exact hne, ?_, ?_⟩
      · rw [hag.1]
        rcases hpp with h0 | ⟨hp1, hp2, hpf⟩
        · exact Or.inl h0
        · refine Or.inr ⟨hp1, hp2, ?_⟩
          intro hm
          rcases List.mem_cons.1 hm with hpe | hm
          · -- the head of `t` would have parent `ed`
            have hseq : lctTreeSeq mem₃ nb cap t.rootId = t.evalInorder (revFlag mem₃ nb) false :=
              hi₃.sf.lctTreeSeq_eq hs3
            have hlen : 0 < (lctTreeSeq mem₃ nb cap t.rootId).length := by
              rw [hseq]; exact List.length_pos_iff.2 hne
            have hp0 := lctAuxParent_of_tree hi₃.sf hpp_le_3 hs3 0 hlen
            simp only [↓reduceIte] at hp0
            rw [hpe] at hp0
            have hsub : ∀ a ∈ lctTreeSeq mem₃ nb cap t.rootId, a ∈ t.toList := fun a ha => by
              rw [hseq] at ha
              exact (t.evalInorder_perm (revFlag mem₃ nb) false).mem_iff.1 ha
            have hmem0 : (lctTreeSeq mem₃ nb cap t.rootId)[0] ∈ t.toList :=
              hsub _ (List.getElem_mem hlen)
            have htm := (hi₃.sf.trees_ok t hs3).2.2
            have hb := htm.nodup_perm_mem hmem0
            have := honly _ hb.1 hb.2 hp0
            exact (hdisj t hs _ hmem0).2.1 this
          · exact hpf hm
      · rcases hlast with ⟨hr, ht_eq, hpp0⟩ | hv
        · exact Or.inl ⟨List.mem_cons_of_mem _ hr, ht_eq, by rw [hag.1]; exact hpp0⟩
        · rw [hag.2.1]; exact Or.inr hv
  · -- represented forest
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u hu1 hu2
      have hz := iterParent_zeroed (par := lctAuxParent mem₃ nb cap)
        (lctAuxParent_zero mem_w nb cap)
        (fun z => by rw [hpar_eq z]; split_ifs <;> simp) cap u
      rcases hz with h0 | heq
      · exact h0
      · rw [heq]; exact hi₃.subdivOk.1 u hu1 hu2
    · intro fe hfe
      rw [hpar_eq]
      rcases List.mem_cons.1 hfe with rfl | hfe
      · simp
      · split_ifs
        · rfl
        · exact hi₃.subdivOk.2.1 fe hfe
    · intro v hv
      rw [hpar_eq]
      by_cases hc : v + 1 = ed ∨ v + 1 = x + 1 ∨ v + 1 = y + 1
      · left; simp only [hc, ↓reduceIte]
      · simp only [hc, ↓reduceIte]
        rcases hi₃.subdivOk.2.2.1 v hv with h0 | ⟨p, hp, hpe, hpp⟩
        · exact Or.inl h0
        · right
          have hpne : p.1 ≠ ed := fun hpe' => by
            have := honly (v + 1) (by omega) (by dsimp only [cap, lctCap]; omega) (hpp.trans hpe')
            exact hc (Or.inr (Or.inr this))
          exact ⟨p, List.mem_filter.2 ⟨hp, by simpa using hpne⟩, hpe, hpp⟩
    · intro q hq
      rcases List.mem_filter.1 hq with ⟨hqm, hqne⟩
      have hqne' : q.1 ≠ ed := by simpa using hqne
      have hq_ok := hi₃.edgeOk q hqm
      have hq_bd := hedge_lt q hqm
      have hq_nx : q.1 ≠ x + 1 := by omega
      have hq_ny : q.1 ≠ y + 1 := by omega
      have hpq : lctAuxParent mem_w nb cap q.1 = lctAuxParent mem₃ nb cap q.1 := by
        rw [hpar_eq]; simp [hq_nx, hq_ny, hqne']
      have hq0 : q.1 ≠ 0 := by omega
      rcases hi₃.subdivOk.2.2.2 q hqm with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inl ⟨by rw [hpq]; exact ha, hpar_keep _ _ hb hq0 hqne' (by omega)⟩
      · exact Or.inr ⟨by rw [hpq]; exact ha, hpar_keep _ _ hb hq0 hqne' (by omega)⟩

end CutAfter

end MinCostFlow.LinkCut.Prog
