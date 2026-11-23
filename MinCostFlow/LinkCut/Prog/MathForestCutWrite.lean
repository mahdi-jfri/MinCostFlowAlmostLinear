module

public import MinCostFlow.LinkCut.Prog.MathForestLinkSetup

/-!
# The memory write of `cut`

After `cut` has splayed the edge node `ed` of the path `[x + 1, ed, y + 1]`, it detaches the two
vertex nodes from `ed` and pushes `ed` back on the free slot stack. This file defines that write
(`lctCutWriteMem`), computes every field it changes, and proves that it keeps `SafeMem`
(`lctCutWriteMem_safeMem`) and that the cleared slot is a valid one-node tree
(`treeMemMatch_cleared_slot`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section CutMemDefs

/-- Offset-value list clearing all `NODE_STRIDE` fields of edge slot `ed` except setting
`OFF_EU := oldFree` so `ed` becomes the new head of the free slot stack. -/
def lctCutClearPairs (oldFree : ℕ) : List (ℕ × ℕ) :=
  (List.range NODE_STRIDE).map (fun off => (off, if off = OFF_EU then oldFree else 0))

theorem lctCutClearPairs_nodup (oldFree : ℕ) :
    ((lctCutClearPairs oldFree).map Prod.fst).Nodup := by
  have hm : (lctCutClearPairs oldFree).map Prod.fst = List.range NODE_STRIDE := by
    simp [lctCutClearPairs, List.map_map, Function.comp_def]
  rw [hm]
  exact List.nodup_range

theorem lctCutClearPairs_lt_stride (oldFree : ℕ) :
    ∀ p ∈ lctCutClearPairs oldFree, p.1 < NODE_STRIDE := by
  intro p hp
  rcases List.mem_map.1 hp with ⟨off, hoff, rfl⟩
  exact List.mem_range.1 hoff

theorem lctCutClearPairs_mem (oldFree off : ℕ) (hoff : off < NODE_STRIDE) :
    (off, if off = OFF_EU then oldFree else 0) ∈ lctCutClearPairs oldFree :=
  List.mem_map.2 ⟨off, List.mem_range.2 hoff, rfl⟩

/-- Combined memory write of `lctCutSpliceBody`: pushes `ed` onto `LCT_HDR_FREE`, clears
`OFF_PARENT` on `x + 1` and `y + 1`, and clears all fields of `ed` via `lctCutClearPairs`. -/
def lctCutWriteMem (mem : ℕ → ℕ) (nb b x y oldFree ed : ℕ) : ℕ → ℕ :=
  let m1 := Function.update mem (b + LCT_HDR_FREE) ed
  let m2 := Function.update m1 (nb + NODE_STRIDE * (x + 1) + OFF_PARENT) 0
  let m3 := Function.update m2 (nb + NODE_STRIDE * (y + 1) + OFF_PARENT) 0
  writeNodeOffs m3 nb ed (lctCutClearPairs oldFree)

private lemma cut_nodeAddr_inj {nb u₁ off₁ u₂ off₂ : ℕ}
    (h1 : off₁ < NODE_STRIDE) (h2 : off₂ < NODE_STRIDE)
    (heq : nb + NODE_STRIDE * u₁ + off₁ = nb + NODE_STRIDE * u₂ + off₂) :
    u₁ = u₂ ∧ off₁ = off₂ := by
  have hsub : NODE_STRIDE * u₁ + off₁ = NODE_STRIDE * u₂ + off₂ := by omega
  have hu : u₁ = u₂ := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hm : NODE_STRIDE * (u₁ + 1) ≤ NODE_STRIDE * u₂ := Nat.mul_le_mul_left _ hlt
      rw [Nat.mul_add, Nat.mul_one] at hm
      omega
    · have hm : NODE_STRIDE * (u₂ + 1) ≤ NODE_STRIDE * u₁ := Nat.mul_le_mul_left _ hlt
      rw [Nat.mul_add, Nat.mul_one] at hm
      omega
  subst hu
  exact ⟨rfl, by omega⟩

theorem lctCutWriteMem_outside {mem : ℕ → ℕ} {nb b x y oldFree ed a : ℕ}
    (hfree : a ≠ b + LCT_HDR_FREE)
    (hx : a ≠ nb + NODE_STRIDE * (x + 1) + OFF_PARENT)
    (hy : a ≠ nb + NODE_STRIDE * (y + 1) + OFF_PARENT)
    (hed : a < nb + NODE_STRIDE * ed ∨ nb + NODE_STRIDE * ed + NODE_STRIDE ≤ a) :
    lctCutWriteMem mem nb b x y oldFree ed a = mem a := by
  dsimp only [lctCutWriteMem]
  rw [writeNodeOffs_outside (lctCutClearPairs_lt_stride oldFree) hed,
    Function.update_of_ne hy, Function.update_of_ne hx, Function.update_of_ne hfree]

theorem lctCutWriteMem_hdr_free {mem : ℕ → ℕ} {nb b x y oldFree ed : ℕ}
    (hnb : nb = lctNodesBase b) (hed1 : 1 ≤ ed) :
    lctCutWriteMem mem nb b x y oldFree ed (b + LCT_HDR_FREE) = ed := by
  have h1 : b + LCT_HDR_FREE < nb := by
    rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega
  have hed_lt : b + LCT_HDR_FREE < nb + NODE_STRIDE * ed := by
    have : NODE_STRIDE ≤ NODE_STRIDE * ed := Nat.le_mul_of_pos_right _ hed1
    omega
  dsimp only [lctCutWriteMem]
  rw [writeNodeOffs_outside (lctCutClearPairs_lt_stride oldFree) (Or.inl hed_lt),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]

theorem lctCutWriteMem_nodeField_other {mem : ℕ → ℕ}
    {nb b x y oldFree ed z off : ℕ} (hnb : nb = lctNodesBase b) (hz1 : 1 ≤ z)
    (hoff : off < NODE_STRIDE) (hnex : z ≠ x + 1) (hney : z ≠ y + 1) (hneed : z ≠ ed) :
    nodeField (lctCutWriteMem mem nb b x y oldFree ed) nb z off = nodeField mem nb z off := by
  have hne_free : nb + NODE_STRIDE * z + off ≠ b + LCT_HDR_FREE := by
    have h1 : b + LCT_HDR_FREE < nb := by
      rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega
    have h2 : NODE_STRIDE ≤ NODE_STRIDE * z := Nat.le_mul_of_pos_right _ hz1
    omega
  have hne_x : nb + NODE_STRIDE * z + off ≠ nb + NODE_STRIDE * (x + 1) + OFF_PARENT := fun heq =>
    hnex (cut_nodeAddr_inj hoff (by decide : OFF_PARENT < NODE_STRIDE) heq).1
  have hne_y : nb + NODE_STRIDE * z + off ≠ nb + NODE_STRIDE * (y + 1) + OFF_PARENT := fun heq =>
    hney (cut_nodeAddr_inj hoff (by decide : OFF_PARENT < NODE_STRIDE) heq).1
  dsimp only [lctCutWriteMem]
  change nodeField (writeNodeOffs _ nb ed (lctCutClearPairs oldFree)) nb z off = nodeField mem nb z off
  rw [writeNodeOffs_nodeField_other (lctCutClearPairs_lt_stride oldFree) hoff hneed]
  dsimp only [nodeField]
  rw [Function.update_of_ne hne_y, Function.update_of_ne hne_x, Function.update_of_ne hne_free]

theorem lctCutWriteMem_nodeField_x_parent {mem : ℕ → ℕ}
    {nb b x y oldFree ed : ℕ} (hne_xy : x ≠ y) (hne_xed : x + 1 ≠ ed) :
    nodeField (lctCutWriteMem mem nb b x y oldFree ed) nb (x + 1) OFF_PARENT = 0 := by
  have hne_y : nb + NODE_STRIDE * (x + 1) + OFF_PARENT ≠
      nb + NODE_STRIDE * (y + 1) + OFF_PARENT := fun heq => by
    have h1 := (cut_nodeAddr_inj (by decide : OFF_PARENT < NODE_STRIDE)
      (by decide : OFF_PARENT < NODE_STRIDE) heq).1
    omega
  dsimp only [lctCutWriteMem]
  change nodeField (writeNodeOffs _ nb ed (lctCutClearPairs oldFree)) nb (x + 1) OFF_PARENT = 0
  rw [writeNodeOffs_nodeField_other (lctCutClearPairs_lt_stride oldFree)
      (by decide : OFF_PARENT < NODE_STRIDE) hne_xed]
  dsimp only [nodeField]
  rw [Function.update_of_ne hne_y, Function.update_self]

theorem lctCutWriteMem_nodeField_x_other {mem : ℕ → ℕ}
    {nb b x y oldFree ed off : ℕ} (hnb : nb = lctNodesBase b) (hoff : off < NODE_STRIDE)
    (hne_par : off ≠ OFF_PARENT) (hne_xy : x ≠ y) (hne_xed : x + 1 ≠ ed) :
    nodeField (lctCutWriteMem mem nb b x y oldFree ed) nb (x + 1) off =
      nodeField mem nb (x + 1) off := by
  have hne_free : nb + NODE_STRIDE * (x + 1) + off ≠ b + LCT_HDR_FREE := by
    have h1 : b + LCT_HDR_FREE < nb := by
      rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega
    omega
  have hne_x : nb + NODE_STRIDE * (x + 1) + off ≠ nb + NODE_STRIDE * (x + 1) + OFF_PARENT := by
    omega
  have hne_y : nb + NODE_STRIDE * (x + 1) + off ≠ nb + NODE_STRIDE * (y + 1) + OFF_PARENT := fun heq =>
    hne_xy (by have := (cut_nodeAddr_inj hoff (by decide : OFF_PARENT < NODE_STRIDE) heq).1; omega)
  dsimp only [lctCutWriteMem]
  change nodeField (writeNodeOffs _ nb ed (lctCutClearPairs oldFree)) nb (x + 1) off =
    nodeField mem nb (x + 1) off
  rw [writeNodeOffs_nodeField_other (lctCutClearPairs_lt_stride oldFree) hoff hne_xed]
  dsimp only [nodeField]
  rw [Function.update_of_ne hne_y, Function.update_of_ne hne_x, Function.update_of_ne hne_free]

theorem lctCutWriteMem_nodeField_y_parent {mem : ℕ → ℕ}
    {nb b x y oldFree ed : ℕ} (hne_yed : y + 1 ≠ ed) :
    nodeField (lctCutWriteMem mem nb b x y oldFree ed) nb (y + 1) OFF_PARENT = 0 := by
  dsimp only [lctCutWriteMem]
  rw [writeNodeOffs_nodeField_other (lctCutClearPairs_lt_stride oldFree)
      (by decide : OFF_PARENT < NODE_STRIDE) hne_yed]
  dsimp only [nodeField]
  rw [Function.update_self]

theorem lctCutWriteMem_nodeField_y_other {mem : ℕ → ℕ}
    {nb b x y oldFree ed off : ℕ} (hnb : nb = lctNodesBase b) (hoff : off < NODE_STRIDE)
    (hne_par : off ≠ OFF_PARENT) (hne_xy : x ≠ y) (hne_yed : y + 1 ≠ ed) :
    nodeField (lctCutWriteMem mem nb b x y oldFree ed) nb (y + 1) off =
      nodeField mem nb (y + 1) off := by
  have hne_free : nb + NODE_STRIDE * (y + 1) + off ≠ b + LCT_HDR_FREE := by
    have h1 : b + LCT_HDR_FREE < nb := by
      rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega
    omega
  have hne_x : nb + NODE_STRIDE * (y + 1) + off ≠ nb + NODE_STRIDE * (x + 1) + OFF_PARENT := fun heq =>
    hne_xy (by have := (cut_nodeAddr_inj hoff (by decide : OFF_PARENT < NODE_STRIDE) heq).1; omega)
  have hne_y : nb + NODE_STRIDE * (y + 1) + off ≠ nb + NODE_STRIDE * (y + 1) + OFF_PARENT := by
    omega
  dsimp only [lctCutWriteMem]
  change nodeField (writeNodeOffs _ nb ed (lctCutClearPairs oldFree)) nb (y + 1) off =
    nodeField mem nb (y + 1) off
  rw [writeNodeOffs_nodeField_other (lctCutClearPairs_lt_stride oldFree) hoff hne_yed]
  dsimp only [nodeField]
  rw [Function.update_of_ne hne_y, Function.update_of_ne hne_x, Function.update_of_ne hne_free]

theorem lctCutWriteMem_nodeField_ed {mem : ℕ → ℕ}
    {nb b x y oldFree ed off : ℕ} (hoff : off < NODE_STRIDE) :
    nodeField (lctCutWriteMem mem nb b x y oldFree ed) nb ed off =
      if off = OFF_EU then oldFree else 0 := by
  dsimp only [nodeField, lctCutWriteMem]
  exact writeNodeOffs_nodeField_mem (lctCutClearPairs_nodup oldFree)
    (lctCutClearPairs_lt_stride oldFree) (lctCutClearPairs_mem oldFree off hoff)

theorem lctCutWriteMem_safeMem {mem₀ mem : ℕ → ℕ}
    {b nb cap hp_caller x y oldFree ed : ℕ}
    (hnb : nb = lctNodesBase b) (harena : nb + NODE_STRIDE * (cap + 1) ≤ hp_caller)
    (hx_le : x + 1 ≤ cap) (hy_le : y + 1 ≤ cap) (hed1 : 1 ≤ ed) (hed2 : ed ≤ cap)
    (hsafe : SafeMem mem₀ nb cap hp_caller mem) :
    SafeMem (Function.update mem₀ (b + LCT_HDR_FREE) ed) nb cap hp_caller
      (lctCutWriteMem mem nb b x y oldFree ed) := by
  let mem₀' := Function.update mem₀ (b + LCT_HDR_FREE) ed
  have hnb3 : 3 ≤ nb := by rw [hnb]; exact lctNodesBase_ge3 b
  have hfree_lt : b + LCT_HDR_FREE < nb - 1 := by
    rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega
  have hfree_ne_ptrs : ∀ u off, 1 ≤ u → u ≤ cap → off < NODE_STRIDE →
      nb + NODE_STRIDE * u + off ≠ b + LCT_HDR_FREE := fun u off hu1 _ _ => by
    have hmul : NODE_STRIDE ≤ NODE_STRIDE * u := Nat.le_mul_of_pos_right _ hu1
    rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE NODE_STRIDE at *; omega
  have hsafe1 : SafeMem mem₀' nb cap hp_caller (Function.update mem (b + LCT_HDR_FREE) ed) := by
    refine ⟨by rw [Function.update_of_ne (by omega : nb - 1 ≠ b + LCT_HDR_FREE)]; exact hsafe.1,
      ?_, ?_, ?_⟩
    · intro a ha
      dsimp only [mem₀']
      by_cases haf : a = b + LCT_HDR_FREE
      · subst haf; simp [Function.update_self]
      · simp only [Function.update_of_ne haf]
        exact hsafe.2.1 a ha
    · intro u hu1 hu2
      dsimp only [nodeField]
      rw [Function.update_of_ne (hfree_ne_ptrs u OFF_LEFT hu1 hu2 (by decide)),
        Function.update_of_ne (hfree_ne_ptrs u OFF_RIGHT hu1 hu2 (by decide)),
        Function.update_of_ne (hfree_ne_ptrs u OFF_PARENT hu1 hu2 (by decide))]
      exact hsafe.2.2.1 u hu1 hu2
    · intro u off hu1 hu2 hoff
      have hne_u := hfree_ne_ptrs u off hu1 hu2 (ptrOffs_lt_stride hoff)
      dsimp only [nodeField]
      rw [Function.update_of_ne hne_u]
      rcases hsafe.2.2.2 u off hu1 hu2 hoff with hp0 | hp_hi | ⟨z, off', hz1, hz2, hoff', hz_eq⟩
      · exact Or.inl hp0
      · exact Or.inr (Or.inl hp_hi)
      · refine Or.inr (Or.inr ⟨z, off', hz1, hz2, hoff', ?_⟩)
        dsimp only [mem₀', nodeField] at hz_eq ⊢
        simp only [Function.update_of_ne (hfree_ne_ptrs z off' hz1 hz2 (ptrOffs_lt_stride hoff'))]
        exact hz_eq
  have hsafe2 : SafeMem mem₀' nb cap hp_caller
      (Function.update (Function.update mem (b + LCT_HDR_FREE) ed)
        (nb + NODE_STRIDE * (x + 1) + OFF_PARENT) 0) :=
    hsafe1.update_field hnb3 harena (by omega) hx_le (by decide) (fun _ => Nat.zero_le _)
      (fun hptr => absurd hptr (by unfold ptrOffs; decide))
  have hsafe3 : SafeMem mem₀' nb cap hp_caller
      (Function.update (Function.update (Function.update mem (b + LCT_HDR_FREE) ed)
        (nb + NODE_STRIDE * (x + 1) + OFF_PARENT) 0)
        (nb + NODE_STRIDE * (y + 1) + OFF_PARENT) 0) :=
    hsafe2.update_field hnb3 harena (by omega) hy_le (by decide) (fun _ => Nat.zero_le _)
      (fun hptr => absurd hptr (by unfold ptrOffs; decide))
  apply writeNodeOffs_safeMem hnb3 harena hed1 hed2 hsafe3
  intro p hp
  rcases List.mem_map.1 hp with ⟨off, hoff, rfl⟩
  have hlt : off < NODE_STRIDE := List.mem_range.1 hoff
  refine ⟨hlt, ?_, ?_⟩
  · intro hstr
    have hne : off ≠ OFF_EU := fun heq => by
      dsimp only at hstr; rw [heq] at hstr
      rcases hstr with h | h | h <;> exact absurd h (by decide)
    simp [hne]
  · intro hptr
    have hne : off ≠ OFF_EU := fun heq => by
      dsimp only at hptr; rw [heq] at hptr
      exact absurd hptr (by unfold ptrOffs; decide)
    simp [hne]
    exact Or.inl rfl

/-- A node slot whose fields are all zero except `OFF_EU` is a valid one-node auxiliary tree with
no parent and no path parent. -/
theorem treeMemMatch_cleared_slot {w h L : ℕ} {mem : ℕ → ℕ} {nb cap ed oldFree : ℕ}
    (hed1 : 1 ≤ ed) (hed2 : ed ≤ cap) (hfree_w : oldFree < 2 ^ w)
    (hf : ∀ off < NODE_STRIDE, nodeField mem nb ed off = if off = OFF_EU then oldFree else 0) :
    TreeMemMatch w h L mem nb cap (.node ed .leaf .leaf) 0 0 := by
  have hw1 : 0 < 2 ^ w := Nat.two_pow_pos w
  have hz : ∀ off < NODE_STRIDE, off ≠ OFF_EU → nodeField mem nb ed off = 0 := fun off hoff hne => by
    rw [hf off hoff]; simp [hne]
  have hz' : ∀ off, off < NODE_STRIDE → off ≠ OFF_EU → nodeField mem nb ed off = 0 := hz
  refine ⟨hed1, hed2, hz' OFF_LEFT (by decide) (by decide), hz' OFF_RIGHT (by decide) (by decide),
    hz' OFF_PARENT (by decide) (by decide), hz' OFF_PPAR (by decide) (by decide), ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, Or.inl (hz' OFF_CSUM_FWD (by decide) (by decide)),
    Or.inl (hz' OFF_CSUM_BWD (by decide) (by decide)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial, trivial⟩
  · rw [hz' OFF_REV (by decide) (by decide)]; omega
  · rw [hz' OFF_ISV (by decide) (by decide)]; omega
  · rw [hz' OFF_HASE (by decide) (by decide)]; omega
  · rw [hz' OFF_ISV (by decide) (by decide), hz' OFF_HASE (by decide) (by decide)]; omega
  · rw [hz' OFF_DIR (by decide) (by decide)]; omega
  · rw [hz' OFF_HAS_TAG (by decide) (by decide)]; omega
  · rw [hz' OFF_TAG_NEG (by decide) (by decide)]; omega
  · rw [hf OFF_EU (by decide)]; simpa using hfree_w
  · rw [hz' OFF_EV (by decide) (by decide)]; exact hw1
  · rw [hz' OFF_EID (by decide) (by decide)]; exact hw1
  · intro h1; rw [hz' OFF_HASE (by decide) (by decide)] at h1; omega
  · intro _
    exact ⟨hz' OFF_DIR (by decide) (by decide), hz' OFF_FLOW_PTR (by decide) (by decide),
      hz' OFF_AF_PTR (by decide) (by decide), hz' OFF_AB_PTR (by decide) (by decide),
      hz' OFF_COST_FWD (by decide) (by decide), hz' OFF_COST_BWD (by decide) (by decide)⟩
  · intro h1; rw [hz' OFF_HAS_TAG (by decide) (by decide)] at h1; omega
  · intro _
    exact ⟨hz' OFF_TAG_PTR (by decide) (by decide), hz' OFF_TAG_NEG (by decide) (by decide)⟩
  · rw [hz' OFF_MIN1_HAS (by decide) (by decide)]; omega
  · rw [hz' OFF_MIN1_HAS (by decide) (by decide), hz' OFF_MIN2_HAS (by decide) (by decide)]
  · intro h1; rw [hz' OFF_MIN1_HAS (by decide) (by decide)] at h1; omega
  · intro _
    exact ⟨hz' OFF_MIN1_VAL (by decide) (by decide), hz' OFF_MIN1_FIRST (by decide) (by decide),
      hz' OFF_MIN1_LAST (by decide) (by decide), hz' OFF_MIN2_VAL (by decide) (by decide),
      hz' OFF_MIN2_FIRST (by decide) (by decide), hz' OFF_MIN2_LAST (by decide) (by decide)⟩
  · have hown0 : nodeOwnRawStep mem nb h L ed = none := by
      simp [nodeOwnRawStep, hz' OFF_HASE (by decide) (by decide)]
    have hsteps : evalMemSteps mem nb h L (.node ed .leaf .leaf) false 0 = [] := by
      simp [evalMemSteps, hown0]
    have hvc : nodeField mem nb ed OFF_VCNT =
        listVcnt mem nb ((AuxTree.node ed .leaf .leaf).evalInorder (revFlag mem nb) false) := by
      simp only [AuxTree.evalInorder, listVcnt, List.nil_append, List.append_nil, Nat.add_zero]
      rw [hz' OFF_VCNT (by decide) (by decide), hz' OFF_ISV (by decide) (by decide)]
    have hm10 : nodeIntMinAgg1 mem nb h L ed = ⟨false, 0, 0, 0⟩ := by
      simp [nodeIntMinAgg1, hz' OFF_MIN1_HAS (by decide) (by decide),
        hz' OFF_MIN1_VAL (by decide) (by decide), hz' OFF_MIN1_FIRST (by decide) (by decide),
        hz' OFF_MIN1_LAST (by decide) (by decide), optIntVal]
    have hm20 : nodeIntMinAgg2 mem nb h L ed = ⟨false, 0, 0, 0⟩ := by
      simp [nodeIntMinAgg2, hz' OFF_MIN2_HAS (by decide) (by decide),
        hz' OFF_MIN2_VAL (by decide) (by decide), hz' OFF_MIN2_FIRST (by decide) (by decide),
        hz' OFF_MIN2_LAST (by decide) (by decide), optIntVal]
    refine ⟨hvc, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsteps]
      simp [optIntVal, hz' OFF_CSUM_FWD (by decide) (by decide), listRawCost,
        wrap_of_fits (fits_zero h L)]
    · rw [hsteps]
      simp [optIntVal, hz' OFF_CSUM_BWD (by decide) (by decide), listRawCost,
        wrap_of_fits (fits_zero h L)]
    · rw [hsteps, hz' OFF_MIN1_HAS (by decide) (by decide)]; simp
    · rw [hsteps]; simpa [listIntMinAgg] using hm10
    · rw [hsteps]; simpa [listIntMinAgg] using hm20

end CutMemDefs

end MinCostFlow.LinkCut.Prog
