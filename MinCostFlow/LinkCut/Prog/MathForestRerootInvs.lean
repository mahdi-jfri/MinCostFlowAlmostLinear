module

public import MinCostFlow.LinkCut.Prog.MathForestRerootAux

/-!
# Reroot Structural Invariants (`revNode_reroot_sf`, `revNode_reroot_edge_subdiv`)

Proves preservation of the heap/header layout, `SplayForestOk`, free slot chains,
`VertexNodeOk`, `ActiveEdgeNodeOk`, `LctAuxPathOk`, `LctSubdivOk`, and `rootAbove` connected
components when reversing an exposed root tree `AuxTree.node (v + 1) l_fin .leaf`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

theorem revNode_reroot_sf {w h L P b n v : ℕ}
    {freeEdges : List ℕ} {edgeMap : List (ℕ × ForestEdge)}
    {l_fin : AuxTree} {rest_fin : List AuxTree} {mem₁ mem₂ : ℕ → ℕ}
    (hi₁ : LctExposeInvs w h L P b n freeEdges edgeMap
      (AuxTree.node (v + 1) l_fin AuxTree.leaf :: rest_fin) mem₁)
    (hv : v < n)
    (hm₂ : TreeMemMatch w h L mem₂ (lctNodesBase b) (lctCap n)
      (AuxTree.node (v + 1) AuxTree.leaf l_fin) 0 0)
    (hhp₂ : mem₂ (lctNodesBase b - 1) = mem₁ (lctNodesBase b - 1))
    (hstat₂ : ∀ u off, IsStaticPayloadOff off →
      nodeField mem₂ (lctNodesBase b) u off = nodeField mem₁ (lctNodesBase b) u off)
    (hout_x₂ : ∀ addr, addr < lctNodesBase b + NODE_STRIDE * (v + 1) ∨
        lctNodesBase b + NODE_STRIDE * (v + 1) + NODE_STRIDE ≤ addr →
      mem₂ addr = mem₁ addr) :
    mem₂ (b + LCT_HDR_N) = n ∧
    mem₂ (b + LCT_HDR_CAP) = lctCap n ∧
    mem₂ (b + LCT_HDR_L) = L ∧
    mem₂ (b + LCT_HDR_P) = P ∧
    SplayForestOk w h L mem₂ (lctNodesBase b) (lctCap n)
      (AuxTree.node (v + 1) AuxTree.leaf l_fin :: rest_fin) ∧
    FreeSlotChain mem₂ (lctNodesBase b) (mem₂ (b + LCT_HDR_FREE)) freeEdges ∧
    (∀ ed ∈ freeEdges, n + 1 ≤ ed ∧ ed ≤ lctCap n ∧
      AuxTree.node ed AuxTree.leaf AuxTree.leaf ∈
        AuxTree.node (v + 1) AuxTree.leaf l_fin :: rest_fin ∧
      nodeField mem₂ (lctNodesBase b) ed OFF_PPAR = 0 ∧
      nodeField mem₂ (lctNodesBase b) ed OFF_ISV = 0 ∧
      nodeField mem₂ (lctNodesBase b) ed OFF_HASE = 0) ∧
    VertexNodeOk mem₂ (lctNodesBase b) n ∧
    (∀ s ∈ rest_fin, v + 1 ∉ s.toList) ∧
    (∀ s ∈ rest_fin, ∀ u ∈ s.toList, ∀ off < NODE_STRIDE,
      nodeField mem₂ (lctNodesBase b) u off = nodeField mem₁ (lctNodesBase b) u off) ∧
    (∀ a, lctNodesBase b + NODE_STRIDE * (lctCap n + 1) ≤ a →
      a < mem₁ (lctNodesBase b - 1) → mem₂ a = mem₁ a) ∧
    (∀ s ∈ rest_fin,
      nodeField mem₂ (lctNodesBase b) s.rootId OFF_PPAR =
        nodeField mem₁ (lctNodesBase b) s.rootId OFF_PPAR ∧
      s.evalInorder (revFlag mem₂ (lctNodesBase b)) false =
        s.evalInorder (revFlag mem₁ (lctNodesBase b)) false) := by
  have hnb3 : 3 ≤ lctNodesBase b := hi₁.sf.2.2.1
  have hhdr_eq : ∀ a, a < lctNodesBase b → mem₂ a = mem₁ a := fun a ha =>
    hout_x₂ a (Or.inl (by omega))
  have hhN : mem₂ (b + LCT_HDR_N) = n := by
    rw [hhdr_eq _ (by unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_N; omega)]; exact hi₁.hdrN
  have hhC : mem₂ (b + LCT_HDR_CAP) = lctCap n := by
    rw [hhdr_eq _ (by unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_CAP; omega)]; exact hi₁.hdrCap
  have hhL : mem₂ (b + LCT_HDR_L) = L := by
    rw [hhdr_eq _ (by unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_L; omega)]; exact hi₁.hdrL
  have hhP : mem₂ (b + LCT_HDR_P) = P := by
    rw [hhdr_eq _ (by unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_P; omega)]; exact hi₁.hdrP
  have hpp_zero₂ : nodeField mem₂ (lctNodesBase b) (v + 1) OFF_PPAR = 0 := hm₂.2.2.2.2.2.1
  have hnd_all₁ : ((AuxTree.node (v + 1) l_fin AuxTree.leaf :: rest_fin).flatMap AuxTree.toList).Nodup :=
    hi₁.sf.2.2.2.2.2.2.2.2.1.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  have hnin_rest : ∀ s ∈ rest_fin, v + 1 ∉ s.toList := by
    intro s hs hv_mem
    have hsplit : (AuxTree.node (v + 1) l_fin AuxTree.leaf).toList ++ rest_fin.flatMap AuxTree.toList =
        (AuxTree.node (v + 1) l_fin AuxTree.leaf :: rest_fin).flatMap AuxTree.toList := rfl
    rw [← hsplit] at hnd_all₁
    exact (List.nodup_append.1 hnd_all₁).2.2 (v + 1) (by simp [AuxTree.toList]) (v + 1)
      (List.mem_flatMap.2 ⟨s, hs, hv_mem⟩) rfl
  have hslot_rest : ∀ s ∈ rest_fin, ∀ u ∈ s.toList, ∀ off < NODE_STRIDE,
      nodeField mem₂ (lctNodesBase b) u off = nodeField mem₁ (lctNodesBase b) u off := by
    intro s hs u hu off hoff
    have hne : u ≠ v + 1 := fun heq => hnin_rest s hs (heq ▸ hu)
    exact mem_off_slot_eq hout_x₂ hne hoff
  have hv_le_cap : v + 1 ≤ lctCap n := by
    have hm := (hi₁.sf.2.2.2.2.2.2.2.2.2 (AuxTree.node (v + 1) l_fin AuxTree.leaf) (by simp)).2.2
    exact (hm.nodup_perm_mem (y := v + 1) (by simp [AuxTree.toList])).2
  have hheap₂ : ∀ a, lctNodesBase b + NODE_STRIDE * (lctCap n + 1) ≤ a →
      a < mem₁ (lctNodesBase b - 1) → mem₂ a = mem₁ a := by
    intro a ha _
    apply hout_x₂ a (Or.inr _)
    have hle : NODE_STRIDE * (v + 1) + NODE_STRIDE ≤ NODE_STRIDE * (lctCap n + 1) := by
      have : v + 1 + 1 ≤ lctCap n + 1 := by omega
      calc
        NODE_STRIDE * (v + 1) + NODE_STRIDE = NODE_STRIDE * (v + 1 + 1) := by ring
        _ ≤ NODE_STRIDE * (lctCap n + 1) := Nat.mul_le_mul_left _ this
    omega
  have hz0_2 : SlotZeroOk mem₂ (lctNodesBase b) := by
    intro off hoff
    have haddr : lctNodesBase b + off < lctNodesBase b + NODE_STRIDE * (v + 1) := by
      have h1 : NODE_STRIDE ≤ NODE_STRIDE * (v + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    rw [hout_x₂ _ (Or.inl haddr)]
    exact hi₁.sf.2.2.2.2.2.2.2.1 off hoff
  have hzero_from₂ : ZeroFrom mem₂ (mem₂ (lctNodesBase b - 1)) := by
    intro a ha
    rw [hhp₂] at ha
    have harena : lctNodesBase b + NODE_STRIDE * (v + 1) + NODE_STRIDE ≤ a := by
      have h1 := hi₁.sf.2.2.2.1
      have h2 : NODE_STRIDE * (v + 1) + NODE_STRIDE ≤ NODE_STRIDE * (lctCap n + 1) := by
        have : v + 1 + 1 ≤ lctCap n + 1 := by omega
        calc
          NODE_STRIDE * (v + 1) + NODE_STRIDE = NODE_STRIDE * (v + 1 + 1) := by ring
          _ ≤ NODE_STRIDE * (lctCap n + 1) := Nat.mul_le_mul_left _ this
      omega
    rw [hout_x₂ a (Or.inr harena)]
    exact hi₁.sf.2.2.2.2.2.2.1 a ha
  have hperm₂ : ((AuxTree.node (v + 1) AuxTree.leaf l_fin :: rest_fin).flatMap AuxTree.toList).Perm
      ((List.range (lctCap n)).map (· + 1)) := by
    have hp_rev : (AuxTree.node (v + 1) AuxTree.leaf l_fin).toList.Perm
        (AuxTree.node (v + 1) l_fin AuxTree.leaf).toList :=
      (AuxTree.node (v + 1) l_fin AuxTree.leaf).revRoot_toList_perm
    exact (List.Perm.append_right (rest_fin.flatMap AuxTree.toList) hp_rev).trans
      hi₁.sf.2.2.2.2.2.2.2.2.1
  have hsf₂ : SplayForestOk w h L mem₂ (lctNodesBase b) (lctCap n)
      (AuxTree.node (v + 1) AuxTree.leaf l_fin :: rest_fin) := by
    refine ⟨hi₁.sf.1, hi₁.sf.2.1, hnb3, ?_, ?_, ?_, hzero_from₂, hz0_2, hperm₂, ?_⟩
    · rw [hhp₂]; exact hi₁.sf.2.2.2.1
    · rw [hhdr_eq _ (by omega)]; exact hi₁.sf.2.2.2.2.1
    · rw [hhp₂]; exact hi₁.sf.2.2.2.2.2.1
    · intro t ht
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht_rest
      · refine ⟨by simp, ?_, ?_⟩
        · simp only [AuxTree.rootId, hpp_zero₂]
          exact Nat.pow_pos (by decide)
        · simpa [AuxTree.rootId, hpp_zero₂] using hm₂
      · rcases hi₁.sf.2.2.2.2.2.2.2.2.2 t (by simp [ht_rest]) with ⟨hne, hpp_w, htm⟩
        have hrt_mem : t.rootId ∈ t.toList := AuxTree.rootId_mem_toList hne
        have hpp_eq := hslot_rest t ht_rest t.rootId hrt_mem OFF_PPAR (by decide)
        refine ⟨hne, by rw [hpp_eq]; exact hpp_w, ?_⟩
        rw [hpp_eq]
        exact memAgree_treeMemMatch_of_nodeList htm (hslot_rest t ht_rest) (by omega) hheap₂
  have hrest_agree : ∀ s ∈ rest_fin,
      nodeField mem₂ (lctNodesBase b) s.rootId OFF_PPAR =
        nodeField mem₁ (lctNodesBase b) s.rootId OFF_PPAR ∧
      s.evalInorder (revFlag mem₂ (lctNodesBase b)) false =
        s.evalInorder (revFlag mem₁ (lctNodesBase b)) false := by
    intro s hs
    have hne := (hi₁.sf.2.2.2.2.2.2.2.2.2 s (by simp [hs])).1
    refine ⟨hslot_rest s hs s.rootId (AuxTree.rootId_mem_toList hne) OFF_PPAR (by decide), ?_⟩
    exact evalInorder_agree_of_list (fun u hu => hslot_rest s hs u hu OFF_REV (by decide)) false
  have hfree_ne_v : ∀ ed ∈ freeEdges, ed ≠ v + 1 := fun ed hed => by
    have h1 := (hi₁.freeNodeOk ed hed).1
    have : lctCap n = 2 * n := rfl
    omega
  have hfreeChain₂ : FreeSlotChain mem₂ (lctNodesBase b) (mem₂ (b + LCT_HDR_FREE)) freeEdges := by
    rw [hhdr_eq _ (by unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega)]
    exact freeSlotChain_agree' (fun ed hed =>
      mem_off_slot_eq hout_x₂ (hfree_ne_v ed hed) (by decide)) hi₁.freeChain
  have hfreeNode₂ : ∀ ed ∈ freeEdges, n + 1 ≤ ed ∧ ed ≤ lctCap n ∧
      AuxTree.node ed AuxTree.leaf AuxTree.leaf ∈
        AuxTree.node (v + 1) AuxTree.leaf l_fin :: rest_fin ∧
      nodeField mem₂ (lctNodesBase b) ed OFF_PPAR = 0 ∧
      nodeField mem₂ (lctNodesBase b) ed OFF_ISV = 0 ∧
      nodeField mem₂ (lctNodesBase b) ed OFF_HASE = 0 := by
    intro ed hed
    rcases hi₁.freeNodeOk ed hed with ⟨hn1, hcap, hmem, hpp, hisv, hhe⟩
    have hne : ed ≠ v + 1 := hfree_ne_v ed hed
    have hmem_rest : AuxTree.node ed AuxTree.leaf AuxTree.leaf ∈ rest_fin := by
      simp only [List.mem_cons] at hmem
      rcases hmem with heq | hr
      · exact absurd (AuxTree.node.inj heq).1 hne
      · exact hr
    have hpp_eq : nodeField mem₂ (lctNodesBase b) ed OFF_PPAR =
        nodeField mem₁ (lctNodesBase b) ed OFF_PPAR :=
      mem_off_slot_eq hout_x₂ hne (by decide)
    refine ⟨hn1, hcap, by simp [hmem_rest], hpp_eq.trans hpp,
      by rw [hstat₂ ed OFF_ISV (by simp [IsStaticPayloadOff])]; exact hisv,
      by rw [hstat₂ ed OFF_HASE (by simp [IsStaticPayloadOff])]; exact hhe⟩
  have hvert₂ : VertexNodeOk mem₂ (lctNodesBase b) n := by
    intro u hu
    refine ⟨?_, ?_⟩
    · rw [hstat₂ (u + 1) OFF_ISV (by simp [IsStaticPayloadOff])]; exact (hi₁.vertexOk u hu).1
    · rw [hstat₂ (u + 1) OFF_HASE (by simp [IsStaticPayloadOff])]; exact (hi₁.vertexOk u hu).2
  exact ⟨hhN, hhC, hhL, hhP, hsf₂, hfreeChain₂, hfreeNode₂, hvert₂, hnin_rest, hslot_rest, hheap₂,
    hrest_agree⟩

theorem revNode_reroot_edge_subdiv {w h L P b n v : ℕ}
    {freeEdges : List ℕ} {edgeMap : List (ℕ × ForestEdge)}
    {l_fin : AuxTree} {rest_fin : List AuxTree} {mem₁ mem₂ : ℕ → ℕ}
    (hi₁ : LctExposeInvs w h L P b n freeEdges edgeMap
      (AuxTree.node (v + 1) l_fin AuxTree.leaf :: rest_fin) mem₁)
    (hsf₂ : SplayForestOk w h L mem₂ (lctNodesBase b) (lctCap n)
      (AuxTree.node (v + 1) AuxTree.leaf l_fin :: rest_fin))
    (hv : v < n)
    (hpp_zero₁ : nodeField mem₁ (lctNodesBase b) (v + 1) OFF_PPAR = 0)
    (hpp_zero₂ : nodeField mem₂ (lctNodesBase b) (v + 1) OFF_PPAR = 0)
    (hev₁ : (AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder (revFlag mem₁ (lctNodesBase b)) false =
      l_fin.evalInorder (revFlag mem₁ (lctNodesBase b)) false ++ [v + 1])
    (hsteps₂ : evalMemSteps mem₂ (lctNodesBase b) h L (AuxTree.node (v + 1) AuxTree.leaf l_fin) false 0 =
      (evalMemSteps mem₁ (lctNodesBase b) h L
        (AuxTree.node (v + 1) l_fin AuxTree.leaf) false 0).reverse.map RawStep.flip)
    (hev₂ : (AuxTree.node (v + 1) AuxTree.leaf l_fin).evalInorder (revFlag mem₂ (lctNodesBase b)) false =
      ((AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder
        (revFlag mem₁ (lctNodesBase b)) false).reverse)
    (hstat₂ : ∀ u off, IsStaticPayloadOff off →
      nodeField mem₂ (lctNodesBase b) u off = nodeField mem₁ (lctNodesBase b) u off)
    (hnin_rest : ∀ s ∈ rest_fin, v + 1 ∉ s.toList)
    (hslot_rest : ∀ s ∈ rest_fin, ∀ u ∈ s.toList, ∀ off < NODE_STRIDE,
      nodeField mem₂ (lctNodesBase b) u off = nodeField mem₁ (lctNodesBase b) u off)
    (hheap₂ : ∀ a, lctNodesBase b + NODE_STRIDE * (lctCap n + 1) ≤ a →
      a < mem₁ (lctNodesBase b - 1) → mem₂ a = mem₁ a)
    (hrest_agree : ∀ s ∈ rest_fin,
      nodeField mem₂ (lctNodesBase b) s.rootId OFF_PPAR =
        nodeField mem₁ (lctNodesBase b) s.rootId OFF_PPAR ∧
      s.evalInorder (revFlag mem₂ (lctNodesBase b)) false =
        s.evalInorder (revFlag mem₁ (lctNodesBase b)) false)
    (hedge_lt : ∀ p ∈ edgeMap, p.2.u < n ∧ p.2.v < n)
    (hslot_cover : ∀ u, n + 1 ≤ u → u ≤ lctCap n → u ∈ freeEdges ∨ ∃ p ∈ edgeMap, p.1 = u) :
    let seq := (AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder (revFlag mem₁ (lctNodesBase b)) false
    ActiveEdgeNodeOk mem₂ (lctNodesBase b) h L P n
      (AuxTree.node (v + 1) AuxTree.leaf l_fin :: rest_fin) edgeMap ∧
    LctAuxPathOk mem₂ (lctNodesBase b) n freeEdges
      (AuxTree.node (v + 1) AuxTree.leaf l_fin :: rest_fin) ∧
    LctSubdivOk mem₂ (lctNodesBase b) n freeEdges edgeMap ∧
    lctAuxParent mem₂ (lctNodesBase b) (lctCap n) (v + 1) = 0 ∧
    (∀ x y, 1 ≤ x → x ≤ lctCap n → 1 ≤ y → y ≤ lctCap n →
      (rootAbove (lctAuxParent mem₂ (lctNodesBase b) (lctCap n)) (lctCap n) x =
        rootAbove (lctAuxParent mem₂ (lctNodesBase b) (lctCap n)) (lctCap n) y ↔
       rootAbove (lctAuxParent mem₁ (lctNodesBase b) (lctCap n)) (lctCap n) x =
        rootAbove (lctAuxParent mem₁ (lctNodesBase b) (lctCap n)) (lctCap n) y)) ∧
    seq.Nodup ∧ seq ≠ [] ∧
    (∀ u, u ∉ seq → lctAuxParent mem₂ (lctNodesBase b) (lctCap n) u =
      lctAuxParent mem₁ (lctNodesBase b) (lctCap n) u) ∧
    (∀ u, u = 0 ∨ u ∈ seq →
      (lctAuxParent mem₁ (lctNodesBase b) (lctCap n) u = 0 ∨
        lctAuxParent mem₁ (lctNodesBase b) (lctCap n) u ∈ seq) ∧
      (lctAuxParent mem₂ (lctNodesBase b) (lctCap n) u = 0 ∨
        lctAuxParent mem₂ (lctNodesBase b) (lctCap n) u ∈ seq)) ∧
    (∀ i (hi : i + 1 < seq.length),
      lctAuxParent mem₂ (lctNodesBase b) (lctCap n) seq[i] = seq[i + 1]) ∧
    (∀ s ∈ AuxTree.node (v + 1) AuxTree.leaf l_fin :: rest_fin,
      nodeField mem₂ (lctNodesBase b) s.rootId OFF_PPAR ≤ lctCap n) := by
  intro seq
  have hnd_all₁ : ((AuxTree.node (v + 1) l_fin AuxTree.leaf :: rest_fin).flatMap AuxTree.toList).Nodup :=
    hi₁.sf.2.2.2.2.2.2.2.2.1.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  have hpp₁_le : ∀ s ∈ AuxTree.node (v + 1) l_fin AuxTree.leaf :: rest_fin,
      nodeField mem₁ (lctNodesBase b) s.rootId OFF_PPAR ≤ lctCap n :=
    fun s hs => hi₁.ppar_le_cap s hs
  have hpp₂_le : ∀ s ∈ AuxTree.node (v + 1) AuxTree.leaf l_fin :: rest_fin,
      nodeField mem₂ (lctNodesBase b) s.rootId OFF_PPAR ≤ lctCap n := by
    intro s hs
    simp only [List.mem_cons] at hs
    rcases hs with rfl | hs
    · simp only [AuxTree.rootId, hpp_zero₂]; omega
    · rw [(hrest_agree s hs).1]; exact hi₁.ppar_le_cap s (by simp [hs])
  have hlast₁ : ((AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder
      (revFlag mem₁ (lctNodesBase b)) false).getLast? = some (v + 1) := by
    rw [hev₁]; simp
  obtain ⟨hseq_nd, hseq_ne, hout_par, hp0_1, hp0_2, hp_seq1_0, hp_seq1_s, hp_seq2_s, hp_seq2_x⟩ :=
    lctAuxParent_revRoot_summary hi₁.sf hsf₂ hpp₁_le hpp₂_le hpp_zero₁ hpp_zero₂ hev₂ hlast₁ hrest_agree
  change seq.Nodup at hseq_nd
  change seq ≠ [] at hseq_ne
  change ∀ i (hi : i + 1 < seq.length),
    lctAuxParent mem₁ (lctNodesBase b) (lctCap n) seq[i + 1] = seq[i] at hp_seq1_s
  change ∀ i (hi : i + 1 < seq.length),
    lctAuxParent mem₂ (lctNodesBase b) (lctCap n) seq[i] = seq[i + 1] at hp_seq2_s
  have hseq_pos : 0 < seq.length := List.length_pos_of_ne_nil hseq_ne
  have hx_last : seq[seq.length - 1]'(by omega) = v + 1 := by
    have hg : seq.getLast? = seq[seq.length - 1]? := List.getLast?_eq_getElem?
    rw [List.getElem?_eq_getElem (by omega : seq.length - 1 < seq.length), hlast₁] at hg
    exact Option.some.inj hg.symm
  have hpar₁_le := lctAuxParent_le_cap_of_trees hi₁.sf hpp₁_le
  have hpar₂_le := lctAuxParent_le_cap_of_trees hsf₂ hpp₂_le
  obtain ⟨hclosed, hreach_seq_len⟩ := reroot_seq_zero_iff hseq_ne hp0_1 hp0_2 hp_seq1_0 hp_seq1_s
    hp_seq2_s hp_seq2_x hx_last
  have hfree_ne_v : ∀ ed ∈ freeEdges, ed ≠ v + 1 := fun ed hed => by
    have h1 := (hi₁.freeNodeOk ed hed).1; omega
  have hsubdiv_1 : ∀ u, 1 ≤ u → u ≤ lctCap n →
      iterParent (lctAuxParent mem₂ (lctNodesBase b) (lctCap n)) (lctCap n) u = 0 := by
    intro u hu1 hu2
    by_cases hex : ∃ s ≤ lctCap n,
        iterParent (lctAuxParent mem₂ (lctNodesBase b) (lctCap n)) s u ∈ seq
    · rcases hex with ⟨s, _, hs⟩
      exact iterParent_eq_zero_of_exists hp0_2 (fun x _ _ => hpar₂_le x) hu1 hu2
        ⟨s + seq.length, by rw [iterParent_add]; exact hreach_seq_len _ hs⟩
    · have hout_orbit : ∀ s ≤ lctCap n,
          lctAuxParent mem₂ (lctNodesBase b) (lctCap n)
            (iterParent (lctAuxParent mem₂ (lctNodesBase b) (lctCap n)) s u) =
          lctAuxParent mem₁ (lctNodesBase b) (lctCap n)
            (iterParent (lctAuxParent mem₂ (lctNodesBase b) (lctCap n)) s u) :=
        fun s hs => hout_par _ (fun hm => hex ⟨s, hs, hm⟩)
      have heq_orbit : ∀ s ≤ lctCap n,
          iterParent (lctAuxParent mem₂ (lctNodesBase b) (lctCap n)) s u =
          iterParent (lctAuxParent mem₁ (lctNodesBase b) (lctCap n)) s u := by
        intro s hs
        induction s with
        | zero => simp [iterParent]
        | succ s' ih =>
            rw [iterParent_succ_right, iterParent_succ_right,
              hout_orbit s' (by omega), ih (by omega)]
      rw [heq_orbit (lctCap n) le_rfl]
      exact hi₁.subdivOk.1 u hu1 hu2
  have hsubdiv_2 : ∀ ed ∈ freeEdges, lctAuxParent mem₂ (lctNodesBase b) (lctCap n) ed = 0 := by
    intro ed hed
    have hne := hfree_ne_v ed hed
    have hnin_seq : ed ∉ seq := fun hm => by
      have hed_tree : AuxTree.node ed AuxTree.leaf AuxTree.leaf ∈
          AuxTree.node (v + 1) l_fin AuxTree.leaf :: rest_fin :=
        (hi₁.freeNodeOk ed hed).2.2.1
      have hmem_rest : AuxTree.node ed AuxTree.leaf AuxTree.leaf ∈ rest_fin := by
        simp only [List.mem_cons] at hed_tree
        rcases hed_tree with h | h
        · exact absurd (AuxTree.node.inj h).1 hne
        · exact h
      have hmed : ed ∈ (AuxTree.node (v + 1) l_fin AuxTree.leaf).toList :=
        ((AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder_perm _ _).mem_iff.1 hm
      exact hnin_rest _ hmem_rest (by
        have hmed' := unique_tree_of_mem hnd_all₁ (by simp) (List.mem_cons_of_mem _ hmem_rest)
          hmed (by simp [AuxTree.toList])
        exact absurd (AuxTree.node.inj hmed').1.symm hne)
    rw [hout_par ed hnin_seq]
    exact hi₁.subdivOk.2.1 ed hed
  have hsubdiv_3 : ∀ u < n, lctAuxParent mem₂ (lctNodesBase b) (lctCap n) (u + 1) = 0 ∨
      ∃ p ∈ edgeMap, (p.2.u = u ∨ p.2.v = u) ∧
        lctAuxParent mem₂ (lctNodesBase b) (lctCap n) (u + 1) = p.1 := by
    intro u hu
    by_cases hu_seq : u + 1 ∈ seq
    · rcases List.getElem_of_mem hu_seq with ⟨i, hi_lt, heq_u⟩
      by_cases hil : i + 1 < seq.length
      · right
        have hpar2_u : lctAuxParent mem₂ (lctNodesBase b) (lctCap n) (u + 1) = seq[i + 1] := by
          rw [← heq_u]; exact hp_seq2_s i hil
        have hpar1_nxt : lctAuxParent mem₁ (lctNodesBase b) (lctCap n) seq[i + 1] = u + 1 := by
          rw [← heq_u]; exact hp_seq1_s i hil
        have hmem_nxt : seq[i + 1] ∈ (AuxTree.node (v + 1) l_fin AuxTree.leaf).toList :=
          ((AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder_perm _ _).mem_iff.1 (List.getElem_mem hil)
        have hb_nxt := (hi₁.sf.2.2.2.2.2.2.2.2.2 _ (by simp)).2.2.nodup_perm_mem hmem_nxt
        by_cases hn_nxt : seq[i + 1] ≤ n
        · rcases hi₁.subdivOk.2.2.1 (seq[i + 1] - 1) (by omega) with hz | ⟨p, _, _, hp1⟩
          · rw [show seq[i + 1] - 1 + 1 = seq[i + 1] by omega] at hz
            rw [hz] at hpar1_nxt; omega
          · rw [show seq[i + 1] - 1 + 1 = seq[i + 1] by omega] at hp1
            have hp_ge := (hi₁.edgeOk p (by assumption)).1
            rw [hp1] at hpar1_nxt; omega
        · rcases hslot_cover seq[i + 1] (by omega) hb_nxt.2 with hf | ⟨p, hp_mem, hp_eq⟩
          · rw [hi₁.subdivOk.2.1 _ hf] at hpar1_nxt; omega
          · rcases hi₁.subdivOk.2.2.2 p hp_mem with ⟨hpu, _⟩ | ⟨hpv, _⟩
            · have hpu' : p.2.u + 1 = u + 1 := by rw [← hpu, hp_eq, hpar1_nxt]
              exact ⟨p, hp_mem, Or.inl (by omega), hpar2_u.trans hp_eq.symm⟩
            · have hpv' : p.2.v + 1 = u + 1 := by rw [← hpv, hp_eq, hpar1_nxt]
              exact ⟨p, hp_mem, Or.inr (by omega), hpar2_u.trans hp_eq.symm⟩
      · left
        have hi_last : i = seq.length - 1 := by omega
        subst hi_last
        have : seq[seq.length - 1] = v + 1 := hx_last
        rw [← heq_u, this]
        exact hp_seq2_x
    · rw [hout_par _ hu_seq]
      exact hi₁.subdivOk.2.2.1 u hu
  have hedge_both : ActiveEdgeNodeOk mem₂ (lctNodesBase b) h L P n
        (AuxTree.node (v + 1) AuxTree.leaf l_fin :: rest_fin) edgeMap ∧
      (∀ p ∈ edgeMap,
        (lctAuxParent mem₂ (lctNodesBase b) (lctCap n) p.1 = p.2.u + 1 ∧
          lctAuxParent mem₂ (lctNodesBase b) (lctCap n) (p.2.v + 1) = p.1) ∨
        (lctAuxParent mem₂ (lctNodesBase b) (lctCap n) p.1 = p.2.v + 1 ∧
          lctAuxParent mem₂ (lctNodesBase b) (lctCap n) (p.2.u + 1) = p.1)) := by
    have hedge_step : ∀ p ∈ edgeMap,
        let ed := p.1
        let e := p.2
        let par₂ := lctAuxParent mem₂ (lctNodesBase b) (lctCap n)
        n + 1 ≤ ed ∧ ed ≤ lctCap n ∧
        nodeField mem₂ (lctNodesBase b) ed OFF_ISV = 0 ∧
        nodeField mem₂ (lctNodesBase b) ed OFF_HASE = 1 ∧
        nodeField mem₂ (lctNodesBase b) ed OFF_EID = e.eid ∧
        nodeField mem₂ (lctNodesBase b) ed OFF_EU = e.u ∧
        nodeField mem₂ (lctNodesBase b) ed OFF_EV = e.v ∧
        (∃ t ∈ AuxTree.node (v + 1) AuxTree.leaf l_fin :: rest_fin, ed ∈ t.toList ∧
          ∃ s ∈ evalMemSteps mem₂ (lctNodesBase b) h L t false 0,
            stepMatchesEdge P ed e s ∧
            ((s.fwd = true ∧ par₂ ed = e.u + 1 ∧ par₂ (e.v + 1) = ed) ∨
             (s.fwd = false ∧ par₂ ed = e.v + 1 ∧ par₂ (e.u + 1) = ed))) ∧
        ((par₂ ed = e.u + 1 ∧ par₂ (e.v + 1) = ed) ∨
          (par₂ ed = e.v + 1 ∧ par₂ (e.u + 1) = ed)) := by
      intro p hp
      rcases hi₁.edgeOk p hp with ⟨hed_lo, hed_hi, _, _, _, _, _, t, ht, hed_t, s, hs_steps, hmatch, hdir⟩
      have hne_v : p.1 ≠ v + 1 := by omega
      have hsub_t :
          (t = AuxTree.node (v + 1) l_fin AuxTree.leaf ∧ p.1 ∈ seq) ∨
          (t ∈ rest_fin ∧ p.1 ∉ seq) := by
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht_rest
        · left; exact ⟨rfl, ((AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder_perm _ _).mem_iff.2 hed_t⟩
        · right
          refine ⟨ht_rest, fun hed_s => ?_⟩
          have hed_t1 : p.1 ∈ (AuxTree.node (v + 1) l_fin AuxTree.leaf).toList :=
            ((AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder_perm _ _).mem_iff.1 hed_s
          have heq_tr := unique_tree_of_mem hnd_all₁ (by simp) (List.mem_cons_of_mem _ ht_rest) hed_t1 hed_t
          have hnin_v : v + 1 ∉ t.toList := hnin_rest t ht_rest
          rw [← heq_tr] at hnin_v
          exact hnin_v (by simp [AuxTree.toList])
      have hres_dir : ∃ t' ∈ AuxTree.node (v + 1) AuxTree.leaf l_fin :: rest_fin, p.1 ∈ t'.toList ∧
          ∃ s' ∈ evalMemSteps mem₂ (lctNodesBase b) h L t' false 0,
            stepMatchesEdge P p.1 p.2 s' ∧
            ((s'.fwd = true ∧ lctAuxParent mem₂ (lctNodesBase b) (lctCap n) p.1 = p.2.u + 1 ∧
                lctAuxParent mem₂ (lctNodesBase b) (lctCap n) (p.2.v + 1) = p.1) ∨
             (s'.fwd = false ∧ lctAuxParent mem₂ (lctNodesBase b) (lctCap n) p.1 = p.2.v + 1 ∧
                lctAuxParent mem₂ (lctNodesBase b) (lctCap n) (p.2.u + 1) = p.1)) := by
        rcases hsub_t with ⟨rfl, hed_seq⟩ | ⟨ht_rest, hed_nseq⟩
        · refine ⟨AuxTree.node (v + 1) AuxTree.leaf l_fin, by simp,
            (AuxTree.node (v + 1) l_fin AuxTree.leaf).revRoot_toList_perm.mem_iff.2 hed_t, s.flip, ?_,
            stepMatchesEdge_flip hmatch, ?_⟩
          · rw [hsteps₂]
            exact List.mem_map.2 ⟨s, List.mem_reverse.2 hs_steps, rfl⟩
          · rcases List.getElem_of_mem hed_seq with ⟨i, hi_lt, heq_ed⟩
            have hi_not_last : i + 1 < seq.length := by
              by_contra hnl
              have hi_last : i = seq.length - 1 := by omega
              subst hi_last
              rw [hx_last] at heq_ed
              exact absurd heq_ed.symm hne_v
            have hnext_eq : ∀ u_prev w_next : ℕ,
                (u_prev = p.2.u ∧ w_next = p.2.v) ∨ (u_prev = p.2.v ∧ w_next = p.2.u) →
                lctAuxParent mem₁ (lctNodesBase b) (lctCap n) p.1 = u_prev + 1 →
                lctAuxParent mem₁ (lctNodesBase b) (lctCap n) (w_next + 1) = p.1 →
                seq[i + 1] = w_next + 1 ∧ (0 < i ∧ seq[i - 1]! = u_prev + 1) := by
              intro u_prev w_next huv hpu _
              have hi_pos : 0 < i := by
                by_contra hiz
                have hiz0 : i = 0 := by omega
                subst hiz0
                have hz := hp_seq1_0 hseq_pos
                rw [heq_ed] at hz
                omega
              have hi_prev : seq[i - 1]! = u_prev + 1 := by
                have hprev_eq := hp_seq1_s (i - 1) (by omega)
                have hidx_eq : seq[(i - 1) + 1]'(by omega) = seq[i]'hi_lt := by congr 1; omega
                rw [hidx_eq, heq_ed] at hprev_eq
                simpa [List.getElem!_eq_getElem?_getD,
                  List.getElem?_eq_getElem (by omega : i - 1 < seq.length)] using hprev_eq.symm.trans hpu
              have hw_mem : seq[i + 1] ∈ (AuxTree.node (v + 1) l_fin AuxTree.leaf).toList :=
                ((AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder_perm _ _).mem_iff.1
                  (List.getElem_mem hi_not_last)
              have hw_bd := (hi₁.sf.2.2.2.2.2.2.2.2.2 _ (by simp)).2.2.nodup_perm_mem hw_mem
              have hw_ge1 : 1 ≤ seq[i + 1] := hw_bd.1
              have hw_par : lctAuxParent mem₁ (lctNodesBase b) (lctCap n) seq[i + 1] = p.1 := by
                rw [← heq_ed]; exact hp_seq1_s i hi_not_last
              have hw_le_n : seq[i + 1] ≤ n := by
                by_contra hwn
                rcases hslot_cover seq[i + 1] (by omega) hw_bd.2 with hf | ⟨p', hp', hp'_eq⟩
                · rw [hi₁.subdivOk.2.1 _ hf] at hw_par; omega
                · have hlt_p' := hedge_lt p' hp'
                  rcases hi₁.subdivOk.2.2.2 p' hp' with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
                    (rw [hp'_eq, hw_par] at ha; omega)
              rcases hi₁.subdivOk.2.2.1 (seq[i + 1] - 1) (by omega) with hz | ⟨p', hp', hmem_w, hp1_w⟩
              · rw [show seq[i + 1] - 1 + 1 = seq[i + 1] by omega] at hz
                rw [hz] at hw_par; omega
              · rw [show seq[i + 1] - 1 + 1 = seq[i + 1] by omega] at hp1_w
                have hp'_id : p'.1 = p.1 := hp1_w.symm.trans hw_par
                have hed_u : p'.2.u = p.2.u := by
                  have h1 := (hi₁.edgeOk p hp).2.2.2.2.2.1
                  have h2 := (hi₁.edgeOk p' hp').2.2.2.2.2.1
                  rw [hp'_id] at h2; omega
                have hed_v : p'.2.v = p.2.v := by
                  have h1 := (hi₁.edgeOk p hp).2.2.2.2.2.2.1
                  have h2 := (hi₁.edgeOk p' hp').2.2.2.2.2.2.1
                  rw [hp'_id] at h2; omega
                have hcases : seq[i + 1] - 1 = p.2.u ∨ seq[i + 1] - 1 = p.2.v := by
                  rw [← hed_u, ← hed_v]; exact Or.imp Eq.symm Eq.symm hmem_w
                have hget : seq[i - 1]! = seq[i - 1] := by
                  simp [List.getElem!_eq_getElem?_getD,
                    List.getElem?_eq_getElem (by omega : i - 1 < seq.length)]
                have hprev_elem : seq[i - 1] = u_prev + 1 := by rw [← hget]; exact hi_prev
                have hnot_u : seq[i + 1] ≠ seq[i - 1] := fun heq_st => by
                  have : i + 1 = i - 1 := (List.Nodup.getElem_inj_iff hseq_nd).1 heq_st
                  omega
                rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · rcases hcases with hwu | hwv
                  · exact absurd (by omega : seq[i + 1] = seq[i - 1]) hnot_u
                  · exact ⟨by omega, hi_pos, hi_prev⟩
                · rcases hcases with hwu | hwv
                  · exact ⟨by omega, hi_pos, hi_prev⟩
                  · exact absurd (by omega : seq[i + 1] = seq[i - 1]) hnot_u
            rcases hdir with ⟨hs_t, hpu, hpv⟩ | ⟨hs_f, hpv, hpu⟩
            · right
              rcases hnext_eq p.2.u p.2.v (Or.inl ⟨rfl, rfl⟩) hpu hpv with ⟨hsucc_w, hi_pos, hi_prev⟩
              have hpar2_ed : lctAuxParent mem₂ (lctNodesBase b) (lctCap n) p.1 = p.2.v + 1 := by
                rw [← heq_ed, hp_seq2_s i hi_not_last, hsucc_w]
              have hpar2_u : lctAuxParent mem₂ (lctNodesBase b) (lctCap n) (p.2.u + 1) = p.1 := by
                have hprev_eq := hp_seq2_s (i - 1) (by omega)
                have hidx_eq : seq[(i - 1) + 1]'(by omega) = seq[i]'hi_lt := by congr 1; omega
                rw [hidx_eq, heq_ed] at hprev_eq
                have hget : seq[i - 1] = p.2.u + 1 := by
                  simpa [List.getElem!_eq_getElem?_getD,
                    List.getElem?_eq_getElem (by omega : i - 1 < seq.length)] using hi_prev
                simpa [hget] using hprev_eq
              exact ⟨by simp [RawStep.flip, hs_t], hpar2_ed, hpar2_u⟩
            · left
              rcases hnext_eq p.2.v p.2.u (Or.inr ⟨rfl, rfl⟩) hpv hpu with ⟨hsucc_w, hi_pos, hi_prev⟩
              have hpar2_ed : lctAuxParent mem₂ (lctNodesBase b) (lctCap n) p.1 = p.2.u + 1 := by
                rw [← heq_ed, hp_seq2_s i hi_not_last, hsucc_w]
              have hpar2_v : lctAuxParent mem₂ (lctNodesBase b) (lctCap n) (p.2.v + 1) = p.1 := by
                have hprev_eq := hp_seq2_s (i - 1) (by omega)
                have hidx_eq : seq[(i - 1) + 1]'(by omega) = seq[i]'hi_lt := by congr 1; omega
                rw [hidx_eq, heq_ed] at hprev_eq
                have hget : seq[i - 1] = p.2.v + 1 := by
                  simpa [List.getElem!_eq_getElem?_getD,
                    List.getElem?_eq_getElem (by omega : i - 1 < seq.length)] using hi_prev
                simpa [hget] using hprev_eq
              exact ⟨by simp [RawStep.flip, hs_f], hpar2_ed, hpar2_v⟩
        · refine ⟨t, by simp [ht_rest], hed_t, s, ?_, hmatch, ?_⟩
          · have hm_t := (hi₁.sf.2.2.2.2.2.2.2.2.2 t (by simp [ht_rest])).2.2
            rw [evalMemSteps_agree hm_t (hslot_rest t ht_rest) hheap₂]
            exact hs_steps
          · have hnot_seq_child : ∀ w,
                lctAuxParent mem₁ (lctNodesBase b) (lctCap n) w = p.1 → w ∉ seq := fun w hpw hw => by
              rcases List.getElem_of_mem hw with ⟨j, hj_lt, hj_eq⟩
              cases j with
              | zero =>
                  have hz := hp_seq1_0 hseq_pos
                  rw [hj_eq, hpw] at hz
                  omega
              | succ j' =>
                  have hprev := hp_seq1_s j' hj_lt
                  rw [hj_eq, hpw] at hprev
                  exact hed_nseq (hprev ▸ List.getElem_mem (by omega))
            rcases hdir with ⟨hs_t, hpu, hpv⟩ | ⟨hs_f, hpv, hpu⟩
            · left
              exact ⟨hs_t, by rw [hout_par p.1 hed_nseq]; exact hpu,
                by rw [hout_par _ (hnot_seq_child _ hpv)]; exact hpv⟩
            · right
              exact ⟨hs_f, by rw [hout_par p.1 hed_nseq]; exact hpv,
                by rw [hout_par _ (hnot_seq_child _ hpu)]; exact hpu⟩
      refine ⟨hed_lo, hed_hi,
        by rw [hstat₂ p.1 OFF_ISV (by simp [IsStaticPayloadOff])]; exact (hi₁.edgeOk p hp).2.2.1,
        by rw [hstat₂ p.1 OFF_HASE (by simp [IsStaticPayloadOff])]; exact (hi₁.edgeOk p hp).2.2.2.1,
        by rw [hstat₂ p.1 OFF_EID (by simp [IsStaticPayloadOff])]; exact (hi₁.edgeOk p hp).2.2.2.2.1,
        by rw [hstat₂ p.1 OFF_EU (by simp [IsStaticPayloadOff])]; exact (hi₁.edgeOk p hp).2.2.2.2.2.1,
        by rw [hstat₂ p.1 OFF_EV (by simp [IsStaticPayloadOff])]; exact (hi₁.edgeOk p hp).2.2.2.2.2.2.1,
        hres_dir, ?_⟩
      rcases hres_dir with ⟨_, _, _, _, _, _, hopt⟩
      rcases hopt with ⟨_, h⟩ | ⟨_, h⟩
      · exact Or.inl h
      · exact Or.inr h
    refine ⟨fun p hp => (hedge_step p hp).2.2.2.2.2.2.2.1 |> fun h7 =>
        ⟨(hedge_step p hp).1, (hedge_step p hp).2.1, (hedge_step p hp).2.2.1,
          (hedge_step p hp).2.2.2.1, (hedge_step p hp).2.2.2.2.1, (hedge_step p hp).2.2.2.2.2.1,
          (hedge_step p hp).2.2.2.2.2.2.1, h7⟩,
      fun p hp => (hedge_step p hp).2.2.2.2.2.2.2.2⟩
  have haux₂ : LctAuxPathOk mem₂ (lctNodesBase b) n freeEdges
      (AuxTree.node (v + 1) AuxTree.leaf l_fin :: rest_fin) := by
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht_rest
    · have hne2 : (AuxTree.node (v + 1) AuxTree.leaf l_fin).evalInorder
          (revFlag mem₂ (lctNodesBase b)) false ≠ [] := by
        rw [hev₂, ne_eq, List.reverse_eq_nil_iff]; exact hseq_ne
      refine ⟨hne2, Or.inl hpp_zero₂, Or.inr ?_⟩
      let r0 := seq[0]'hseq_pos
      have hr0_mem : r0 ∈ (AuxTree.node (v + 1) l_fin AuxTree.leaf).toList :=
        ((AuxTree.node (v + 1) l_fin AuxTree.leaf).evalInorder_perm _ _).mem_iff.1
          (List.getElem_mem hseq_pos)
      have hr0_bd := (hi₁.sf.2.2.2.2.2.2.2.2.2 _ (by simp)).2.2.nodup_perm_mem hr0_mem
      have hr0_le_n : r0 ≤ n := by
        by_contra hr0_gt
        rcases hslot_cover r0 (by omega) hr0_bd.2 with hf | ⟨p, hp_mem, hp_eq⟩
        · have hf_tree : AuxTree.node r0 AuxTree.leaf AuxTree.leaf ∈
              AuxTree.node (v + 1) l_fin AuxTree.leaf :: rest_fin :=
            (hi₁.freeNodeOk r0 hf).2.2.1
          have heq_t := unique_tree_of_mem hnd_all₁ (by simp) hf_tree hr0_mem (by simp [AuxTree.toList])
          have hnin_v : v + 1 ∈ (AuxTree.node (v + 1) l_fin AuxTree.leaf).toList := by simp [AuxTree.toList]
          rw [heq_t] at hnin_v
          simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hnin_v
          rcases hnin_v with (h | heq) | h
          · exact absurd h List.not_mem_nil
          · omega
          · exact absurd h List.not_mem_nil
        · have hz : lctAuxParent mem₁ (lctNodesBase b) (lctCap n) r0 = 0 := hp_seq1_0 hseq_pos
          rcases hi₁.subdivOk.2.2.2 p hp_mem with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
            (rw [hp_eq, hz] at ha; omega)
      refine ⟨r0 - 1, by omega, ?_⟩
      rw [hev₂, List.getLast?_reverse]
      have hhead : seq.head? = some r0 := by
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hseq_pos]
      rw [hhead, show r0 - 1 + 1 = r0 by omega]
    · rcases hi₁.auxPathOk t (by simp [ht_rest]) with ⟨hne_s, hpp_s, hlast_s⟩
      rcases hrest_agree t ht_rest with ⟨hp_eq, hev_eq⟩
      refine ⟨by rw [hev_eq]; exact hne_s, by rw [hp_eq]; exact hpp_s, ?_⟩
      rcases hlast_s with ⟨hfr, hleaf, hpp0⟩ | ⟨u, hu, hgl⟩
      · exact Or.inl ⟨hfr, hleaf, by rw [hp_eq]; exact hpp0⟩
      · exact Or.inr ⟨u, hu, by rw [hev_eq]; exact hgl⟩
  have hsubdiv₂ : LctSubdivOk mem₂ (lctNodesBase b) n freeEdges edgeMap :=
    ⟨hsubdiv_1, hsubdiv_2, hsubdiv_3, hedge_both.2⟩
  have hcomp : ∀ x y, 1 ≤ x → x ≤ lctCap n → 1 ≤ y → y ≤ lctCap n →
      (rootAbove (lctAuxParent mem₂ (lctNodesBase b) (lctCap n)) (lctCap n) x =
        rootAbove (lctAuxParent mem₂ (lctNodesBase b) (lctCap n)) (lctCap n) y ↔
       rootAbove (lctAuxParent mem₁ (lctNodesBase b) (lctCap n)) (lctCap n) x =
        rootAbove (lctAuxParent mem₁ (lctNodesBase b) (lctCap n)) (lctCap n) y) := by
    have hundir12 : ∀ a b_1, 1 ≤ a → a ≤ lctCap n → 1 ≤ b_1 → b_1 ≤ lctCap n →
        lctAuxParent mem₁ (lctNodesBase b) (lctCap n) a = b_1 →
        lctAuxParent mem₂ (lctNodesBase b) (lctCap n) a = b_1 ∨
          lctAuxParent mem₂ (lctNodesBase b) (lctCap n) b_1 = a := by
      intro a b_1 _ _ hb1 _ hpa
      by_cases ha : a ∈ seq
      · rcases List.getElem_of_mem ha with ⟨i, hi_lt, heq_a⟩
        cases i with
        | zero =>
            have hz := hp_seq1_0 hseq_pos
            have h0 : seq[0]'hseq_pos = a := heq_a
            rw [h0, hpa] at hz
            omega
        | succ i' =>
            have hb_eq : b_1 = seq[i'] := by rw [← hpa, ← heq_a]; exact hp_seq1_s i' hi_lt
            right; rw [hb_eq, ← heq_a]; exact hp_seq2_s i' hi_lt
      · left; rw [hout_par a ha, hpa]
    have hundir21 : ∀ a b_1, 1 ≤ a → a ≤ lctCap n → 1 ≤ b_1 → b_1 ≤ lctCap n →
        lctAuxParent mem₂ (lctNodesBase b) (lctCap n) a = b_1 →
        lctAuxParent mem₁ (lctNodesBase b) (lctCap n) a = b_1 ∨
          lctAuxParent mem₁ (lctNodesBase b) (lctCap n) b_1 = a := by
      intro a b_1 _ _ hb1 _ hpa
      by_cases ha : a ∈ seq
      · rcases List.getElem_of_mem ha with ⟨i, hi_lt, heq_a⟩
        by_cases hil : i + 1 < seq.length
        · have hb_eq : b_1 = seq[i + 1] := by rw [← hpa, ← heq_a]; exact hp_seq2_s i hil
          right; rw [hb_eq, ← heq_a]; exact hp_seq1_s i hil
        · have hi_last : i = seq.length - 1 := by omega
          subst hi_last
          have hla : seq[seq.length - 1]'(by omega) = v + 1 := hx_last
          rw [← heq_a, hla, hp_seq2_x] at hpa
          omega
      · left; rw [← hout_par a ha, hpa]
    have h12 := reroot_rootAbove_congr_step hp0_1 hp0_2 (fun x _ _ => hpar₁_le x)
      (fun x _ _ => hpar₂_le x) hi₁.subdivOk.1 hsubdiv_1 hundir12
    have h21 := reroot_rootAbove_congr_step hp0_2 hp0_1 (fun x _ _ => hpar₂_le x)
      (fun x _ _ => hpar₁_le x) hsubdiv_1 hi₁.subdivOk.1 hundir21
    intro x y hx1 hx2 hy1 hy2
    constructor
    · intro heq; rw [h21 x hx1 hx2, h21 y hy1 hy2, heq]
    · intro heq; rw [h12 x hx1 hx2, h12 y hy1 hy2, heq]
  exact ⟨hedge_both.1, haux₂, hsubdiv₂, hp_seq2_x, hcomp, hseq_nd, hseq_ne, hout_par, hclosed,
    hp_seq2_s, hpp₂_le⟩

end MinCostFlow.LinkCut.Prog
