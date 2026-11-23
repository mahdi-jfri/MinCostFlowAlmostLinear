module

public import MinCostFlow.LinkCut.Prog.MathForestInit

/-!
# Entry/Exit Framing and Forest-Level Safe Splay Wrapper

Provides:
- `LctMemRep.hp_le_of_foot`: bounds `x.hpHi ≤ hp_caller` from footprint containment;
- `enterOp_ready`: sets `mem (nb - 1) := hp_eff` preserving `SplayForestOk`, `SafeMem.refl`,
  `lctPhi`, and all tree/edge/free-slot invariants;
- `exitOp_rep`: closes `LctMemRep` (using `SafeMem.ptrFootOk_of_treeMemMatch`), preserves
  `DSRep.Respects` across caller answer writes inside `[hp_caller, hp_eff)`, and preserves `lctPhi`;
- `splayForest_lct_runs`: combines `splayForest_runs` and `splay_safeExec`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section EntryExitAndSplay

theorem LctMemRep.hp_le_of_foot {w h L P b hp_caller : ℕ} {F : MathForest} {x : LctConc}
    {mem : ℕ → ℕ} (hrep : LctMemRep w h L P b F x mem)
    (hfoot : ∀ a, lctFoot b x a → a < hp_caller) :
    lctArenaHi b (lctCap F.n) ≤ mem (b + LCT_HDR_HP) ∧
    mem (b + LCT_HDR_HP) ≤ hp_caller ∧
    x.hpHi ≤ hp_caller := by
  rcases hrep with ⟨_, _, _, _, _, _, _, hfoot_last, _, _, _, _, _, hhp_lo, hhp_le_hi, _⟩
  have hlt := hfoot (x.hpHi - 1) hfoot_last
  omega

private theorem transfer_struct_of_agree_ptrs {w h L P b n : ℕ}
    {mem₁ mem₂ : ℕ → ℕ} {trees : List AuxTree} {freeEdges : List ℕ} {edgeMap : List (ℕ × ForestEdge)}
    (hag_nb : MemAgreeOn (lctNodesBase b) (lctArenaHi b (lctCap n)) mem₁ mem₂)
    (hhdr_free : mem₂ (b + LCT_HDR_FREE) = mem₁ (b + LCT_HDR_FREE))
    (hperm_trees : (trees.flatMap AuxTree.toList).Perm ((List.range (lctCap n)).map (· + 1)))
    (htrees_ok : ∀ t ∈ trees, t ≠ .leaf ∧ nodeField mem₁ (lctNodesBase b) t.rootId OFF_PPAR < 2 ^ w ∧
      TreeMemMatch w h L mem₁ (lctNodesBase b) (lctCap n) t 0
        (nodeField mem₁ (lctNodesBase b) t.rootId OFF_PPAR))
    (hptrs : ∀ u ≤ lctCap n, ∀ off ∈ ptrOffs,
      let ptr := nodeField mem₁ (lctNodesBase b) u off
      ptr = 0 ∨ ∀ i < L, mem₂ (ptr + i) = mem₁ (ptr + i))
    (hfree_bd : ∀ ed ∈ freeEdges, ed ≤ lctCap n)
    (hfc : FreeSlotChain mem₁ (lctNodesBase b) (mem₁ (b + LCT_HDR_FREE)) freeEdges)
    (hv_ok : VertexNodeOk mem₁ (lctNodesBase b) n)
    (hae_ok : ActiveEdgeNodeOk mem₁ (lctNodesBase b) h L P n trees edgeMap)
    (haux_ok : LctAuxPathOk mem₁ (lctNodesBase b) n freeEdges trees)
    (hsub_ok : LctSubdivOk mem₁ (lctNodesBase b) n freeEdges edgeMap) :
    FreeSlotChain mem₂ (lctNodesBase b) (mem₂ (b + LCT_HDR_FREE)) freeEdges ∧
    VertexNodeOk mem₂ (lctNodesBase b) n ∧
    ActiveEdgeNodeOk mem₂ (lctNodesBase b) h L P n trees edgeMap ∧
    LctAuxPathOk mem₂ (lctNodesBase b) n freeEdges trees ∧
    LctSubdivOk mem₂ (lctNodesBase b) n freeEdges edgeMap := by
  let nb := lctNodesBase b
  let cap := lctCap n
  have hnb_ar : MemAgreeOn nb (nb + NODE_STRIDE * (cap + 1)) mem₁ mem₂ := by
    simpa [nb, cap, lctArenaHi] using hag_nb
  have hfield : ∀ u ≤ cap, ∀ off < NODE_STRIDE,
      nodeField mem₂ nb u off = nodeField mem₁ nb u off := fun u hu off hoff => by
    symm
    apply hag_nb
    · dsimp only [nb]; omega
    · dsimp only [nb, cap]; unfold lctArenaHi
      have hmul : NODE_STRIDE * u + off < NODE_STRIDE * (lctCap n + 1) := by
        have h1 : NODE_STRIDE * u ≤ NODE_STRIDE * lctCap n := Nat.mul_le_mul_left _ hu
        rw [Nat.mul_add, Nat.mul_one]; omega
      omega
  have ht_mem_le : ∀ {t : AuxTree}, t ∈ trees → ∀ u ∈ t.toList, u ≤ cap := fun {t} ht u hu => by
    have hm := hperm_trees.mem_iff.1 (List.mem_flatMap.2 ⟨t, ht, hu⟩)
    rcases List.mem_map.1 hm with ⟨y, hy, rfl⟩
    rw [List.mem_range] at hy; omega
  have hpar_eq : ∀ u, lctAuxParent mem₂ nb cap u = lctAuxParent mem₁ nb cap u :=
    lctAuxParent_agree hnb_ar
  have hpar_eq' : ∀ u, lctAuxParent mem₂ (lctNodesBase b) (lctCap n) u =
      lctAuxParent mem₁ (lctNodesBase b) (lctCap n) u := hpar_eq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hhdr_free]
    exact (freeSlotChain_agree (fun ed hed => (hfield ed (hfree_bd ed hed) OFF_EU (by decide)).symm)).mp hfc
  · intro v hv
    rcases hv_ok v hv with ⟨hiv, hhe⟩
    have hule : v + 1 ≤ cap := by unfold cap lctCap; omega
    exact ⟨by rw [hfield (v + 1) hule OFF_ISV (by decide)]; exact hiv,
      by rw [hfield (v + 1) hule OFF_HASE (by decide)]; exact hhe⟩
  · intro pr hpr
    rcases hae_ok pr hpr with ⟨h1, h2, hisv, hhe, heid, heu, hev, t, ht, hed_t, s, hs_mem, hsm, hor⟩
    refine ⟨h1, h2,
      by rw [hfield pr.1 h2 OFF_ISV (by decide)]; exact hisv,
      by rw [hfield pr.1 h2 OFF_HASE (by decide)]; exact hhe,
      by rw [hfield pr.1 h2 OFF_EID (by decide)]; exact heid,
      by rw [hfield pr.1 h2 OFF_EU (by decide)]; exact heu,
      by rw [hfield pr.1 h2 OFF_EV (by decide)]; exact hev,
      t, ht, hed_t, s, ?_, hsm, ?_⟩
    · have htm := (htrees_ok t ht).2.2
      rw [evalMemSteps_agree_ptrs htm
        (fun u hu off hoff => hfield u (ht_mem_le ht u hu) off hoff)
        (fun u hu off hoff => hptrs u (ht_mem_le ht u hu) off hoff) false 0]
      exact hs_mem
    · simpa only [hpar_eq'] using hor
  · intro t ht
    rcases haux_ok t ht with ⟨hne_s, hpp_s, hlast_s⟩
    have hrt : t.rootId ≤ cap := ht_mem_le ht t.rootId (AuxTree.rootId_mem_toList (htrees_ok t ht).1)
    have hrev_t : t.evalInorder (revFlag mem₂ nb) false = t.evalInorder (revFlag mem₁ nb) false := by
      apply evalInorder_agree_of_list
      intro u hu
      exact hfield u (ht_mem_le ht u hu) OFF_REV (by decide)
    rw [hrev_t, hfield t.rootId hrt OFF_PPAR (by decide)]
    exact ⟨hne_s, hpp_s, hlast_s⟩
  · rcases hsub_ok with ⟨h1, h2, h3, h4⟩
    have hiter : ∀ k u, iterParent (lctAuxParent mem₂ nb cap) k u =
        iterParent (lctAuxParent mem₁ nb cap) k u := by
      intro k
      induction k with
      | zero => intro u; rfl
      | succ k ih => intro u; simp only [iterParent, hpar_eq, ih]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u hu1 hu2; rw [hiter]; exact h1 u hu1 hu2
    · intro ed hed; rw [hpar_eq']; exact h2 ed hed
    · intro v hv; rw [hpar_eq']; exact h3 v hv
    · intro pr hpr; simp only [hpar_eq']; exact h4 pr hpr

private theorem treeMemMatch_struct_le {w h L : ℕ} {mem : ℕ → ℕ} {nb cap : ℕ}
    {t : AuxTree} {p pp : ℕ} (ht : TreeMemMatch w h L mem nb cap t p pp) (hp : p ≤ cap)
    {u : ℕ} (hu : u ∈ t.toList) :
    nodeField mem nb u OFF_LEFT ≤ cap ∧
    nodeField mem nb u OFF_RIGHT ≤ cap ∧
    nodeField mem nb u OFF_PARENT ≤ cap := by
  induction t generalizing p pp with
  | leaf => simp [AuxTree.toList] at hu
  | node x l r ihl ihr =>
      rcases ht with ⟨hx1, hx2, hL, hR, hpar, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, _, _, _, _, _, hl, hr⟩
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hu
      rcases hu with (hul | rfl) | hur
      · exact ihl hl hx2 hul
      · have hroot : ∀ {c : AuxTree} {q : ℕ}, TreeMemMatch w h L mem nb cap c u q → c.rootId ≤ cap := by
          intro c q hc
          cases c with
          | leaf => exact Nat.zero_le _
          | node _ _ _ => exact hc.2.1
        rw [hL, hR, hpar]; exact ⟨hroot hl, hroot hr, hp⟩
      · exact ihr hr hx2 hur

/-- Pre-entry state invariant right after storing `hp_eff` into `nb - 1`: `SplayForestOk`,
`SafeMem.refl`, unchanged `lctPhi`, and preserved node/free/path/subdiv invariants. -/
theorem enterOp_ready {w h L P b hp_caller hp_eff : ℕ} {F : MathForest} {x : LctConc}
    {mem : ℕ → ℕ} (hrep : LctMemRep w h L P b F x mem)
    (hfoot : ∀ a, lctFoot b x a → a < hp_caller)
    (hz : ZeroFrom mem hp_caller) (hcaller_le : hp_caller ≤ hp_eff) (hhp_w : hp_eff < 2 ^ w) :
    let mem₁ := Function.update mem (lctNodesBase b - 1) hp_eff
    let nb := lctNodesBase b
    let cap := lctCap F.n
    SplayForestOk w h L mem₁ nb cap x.trees ∧
    SafeMem mem₁ nb cap hp_eff mem₁ ∧
    lctPhi L mem₁ b F.n = lctPhi L mem b F.n ∧
    ZeroFrom mem₁ hp_eff ∧
    mem₁ (b + LCT_HDR_N) = F.n ∧
    mem₁ (b + LCT_HDR_CAP) = cap ∧
    mem₁ (b + LCT_HDR_L) = L ∧
    mem₁ (b + LCT_HDR_P) = P ∧
    FreeSlotChain mem₁ nb (mem₁ (b + LCT_HDR_FREE)) x.freeEdges ∧
    VertexNodeOk mem₁ nb F.n ∧
    ActiveEdgeNodeOk mem₁ nb h L P F.n x.trees x.edgeMap ∧
    LctAuxPathOk mem₁ nb F.n x.freeEdges x.trees ∧
    LctSubdivOk mem₁ nb F.n x.freeEdges x.edgeMap ∧
    SlotZeroOk mem₁ nb ∧
    PtrFootOk b mem₁ x L ∧
    (∀ u ≤ cap, ∀ off < NODE_STRIDE, nodeField mem₁ nb u off = nodeField mem nb u off) ∧
    (∀ a, a < b + LCT_HDR_HP ∨ lctArenaHi b cap ≤ a → mem₁ a = mem a) := by
  intro mem₁ nb cap
  have hp_bd := hrep.hp_le_of_foot hfoot
  have hnb3 := lctNodesBase_ge3 b
  have hnb1_eq : nb - 1 = b + LCT_HDR_HP := by
    dsimp only [nb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_HP; omega
  have hne_nb1 : ∀ a ≠ nb - 1, mem₁ a = mem a := fun a hne => Function.update_of_ne hne _ _
  have hag_other : ∀ a, a < b + LCT_HDR_HP ∨ lctArenaHi b cap ≤ a → mem₁ a = mem a := fun a ha =>
    hne_nb1 a (by
      rw [hnb1_eq]
      rcases ha with h | h
      · omega
      · unfold LCT_HDR_HP
        unfold lctArenaHi lctNodesBase LCT_HDR_SIZE NODE_STRIDE at h
        omega)
  have hag_nb : MemAgreeOn nb (lctArenaHi b cap) mem mem₁ := fun a ha1 _ =>
    (hne_nb1 a (by dsimp only [nb] at ha1 ⊢; unfold lctNodesBase LCT_HDR_SIZE at ha1 ⊢; omega)).symm
  have hfld_eq : ∀ u ≤ cap, ∀ off < NODE_STRIDE, nodeField mem₁ nb u off = nodeField mem nb u off :=
    fun u _ off _ => hne_nb1 _ (by dsimp only [nb] at hnb3 ⊢; omega)
  have hm1_hp : mem₁ (nb - 1) = hp_eff := Function.update_self _ _ _
  have hz1 : ZeroFrom mem₁ hp_eff := fun a ha => by
    have har : lctArenaHi b cap ≤ a := by
      unfold lctArenaHi lctNodesBase LCT_HDR_SIZE NODE_STRIDE at hp_bd ⊢; omega
    rw [hag_other a (Or.inr har)]
    exact hz a (le_trans hcaller_le ha)
  rcases hrep with ⟨hh, hw, _, _, hxn, _, _, _, _, hN, hCAP, hL_h, hP_h, _, _, _,
    _, _, hfc, hfree_ok, hslot0, hperm, htrees, hvok, heok, hpok, hsok, hpf⟩
  have hs0_1 : SlotZeroOk mem₁ nb := fun off hoff => by
    rw [← hslot0 off hoff]
    exact hne_nb1 (nb + off) (by dsimp only [nb] at hnb3 ⊢; omega)
  have hstr_1 : ∀ u, 1 ≤ u → u ≤ cap →
      nodeField mem₁ nb u OFF_LEFT ≤ cap ∧
      nodeField mem₁ nb u OFF_RIGHT ≤ cap ∧
      nodeField mem₁ nb u OFF_PARENT ≤ cap := by
    intro u hu1 hu2
    have hum : u ∈ (x.trees.flatMap AuxTree.toList) := by
      rw [hperm.mem_iff]
      refine List.mem_map.2 ⟨u - 1, List.mem_range.2 (by omega), by omega⟩
    rcases List.mem_flatMap.1 hum with ⟨t, ht, hut⟩
    have htm := (htrees t ht).2.2
    have htm1 := memAgree_treeMemMatch
      (fun a ha1 ha2 => hag_nb a ha1 (by simpa [nb, lctArenaHi] using ha2))
      (by rw [hm1_hp, hnb1_eq]; exact le_trans hp_bd.2.1 hcaller_le)
      (fun a ha1 _ => hne_nb1 a (by dsimp only [nb] at hnb3 ⊢; unfold NODE_STRIDE at ha1; omega)) htm
    exact treeMemMatch_struct_le htm1 (Nat.zero_le _) hut
  have hsf1 : SplayForestOk w h L mem₁ nb cap x.trees := by
    refine ⟨hh, hw, lctNodesBase_ge3 b, ?_, ?_, ?_, ?_, hs0_1, hperm, ?_⟩
    · rw [hm1_hp]; exact le_trans hp_bd.1 (le_trans hp_bd.2.1 hcaller_le)
    · rw [hag_other (nb - 3) (Or.inl (by dsimp only [nb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_HP; omega))]
      rw [show nb - 3 = b + LCT_HDR_L by dsimp only [nb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_L; omega]
      exact hL_h
    · rw [hm1_hp]; exact hhp_w
    · rw [hm1_hp]; exact hz1
    · intro t ht
      rcases htrees t ht with ⟨hne, hpp_w, htm⟩
      have hrt : t.rootId ≤ cap := by
        have hm := hperm.mem_iff.1 (List.mem_flatMap.2 ⟨t, ht, AuxTree.rootId_mem_toList hne⟩)
        rcases List.mem_map.1 hm with ⟨y, hy, hyr⟩; rw [List.mem_range] at hy; omega
      rw [hfld_eq t.rootId hrt OFF_PPAR (by decide)]
      refine ⟨hne, hpp_w, memAgree_treeMemMatch
        (fun a ha1 ha2 => hag_nb a ha1 (by simpa [nb, lctArenaHi] using ha2))
        (by rw [hm1_hp, hnb1_eq]; exact le_trans hp_bd.2.1 hcaller_le)
        (fun a ha1 _ => hne_nb1 a (by dsimp only [nb] at hnb3 ⊢; unfold NODE_STRIDE at ha1; omega)) htm⟩
  have hsafe1 : SafeMem mem₁ nb cap hp_eff mem₁ := SafeMem.refl (by rw [hm1_hp]) hstr_1
  have hphi1 : lctPhi L mem₁ b F.n = lctPhi L mem b F.n :=
    lctPhi_agree hag_nb
  have hptrs_1 : ∀ u ≤ cap, ∀ off ∈ ptrOffs,
      let ptr := nodeField mem nb u off
      ptr = 0 ∨ ∀ i < L, mem₁ (ptr + i) = mem (ptr + i) := fun u hu off hoff => by
    rcases hpf u (hxn ▸ hu) off hoff with h0 | ⟨ha, _, _⟩
    · exact Or.inl h0
    · exact Or.inr fun i _ => hne_nb1 (nodeField mem nb u off + i) (by
        have hlt : nb < lctArenaHi b (lctCap x.n) := by
          dsimp only [nb]; unfold lctArenaHi lctNodesBase LCT_HDR_SIZE NODE_STRIDE; omega
        dsimp only [nb] at *; omega)
  have htr := transfer_struct_of_agree_ptrs hag_nb
    (hag_other (b + LCT_HDR_FREE) (Or.inl (by unfold LCT_HDR_FREE LCT_HDR_HP; omega)))
    hperm htrees hptrs_1 (fun ed hed => (hfree_ok ed hed).2.1) hfc hvok heok hpok hsok
  have hpf1 : PtrFootOk b mem₁ x L := fun u hu off hoff => by
    dsimp only
    rw [hfld_eq u (by simpa [hxn] using hu) off (ptrOffs_lt_stride hoff),
      show mem₁ (nb - 1) = hp_eff from hm1_hp]
    rcases hpf u hu off hoff with h0 | ⟨ha, hle, hf⟩
    · exact Or.inl h0
    · exact Or.inr ⟨ha, le_trans hle (by rw [hnb1_eq]; exact le_trans hp_bd.2.1 hcaller_le), hf⟩
  refine ⟨hsf1, hsafe1, hphi1, hz1, ?_, ?_, ?_, ?_,
    htr.1, htr.2.1, htr.2.2.1, htr.2.2.2.1, htr.2.2.2.2, hs0_1, hpf1, hfld_eq, hag_other⟩
  · rw [hag_other (b + LCT_HDR_N) (Or.inl (by unfold LCT_HDR_N LCT_HDR_HP; omega))]; exact hN
  · rw [hag_other (b + LCT_HDR_CAP) (Or.inl (by unfold LCT_HDR_CAP LCT_HDR_HP; omega))]; exact hCAP
  · rw [hag_other (b + LCT_HDR_L) (Or.inl (by unfold LCT_HDR_L LCT_HDR_HP; omega))]; exact hL_h
  · rw [hag_other (b + LCT_HDR_P) (Or.inl (by unfold LCT_HDR_P LCT_HDR_HP; omega))]; exact hP_h

/-- Exit bridge converting post-operation Word-RAM memory `mem_end` and optional answer buffer
write inside `[hp_caller, hp_eff)` (`mem_fin`) into `LctMemRep` and `DSRep.Respects`. -/
theorem exitOp_rep {w h L P b hp_caller hp_eff space : ℕ}
    {F0 F1 : MathForest} {x0 : LctConc} {mem0 mem_safe mem_end mem_fin : ℕ → ℕ}
    {trees1 : List AuxTree} {freeEdges1 : List ℕ} {edgeMap1 : List (ℕ × ForestEdge)}
    (hrep0 : LctMemRep w h L P b F0 x0 mem0)
    (hfoot0 : ∀ a, lctFoot b x0 a → a < hp_caller)
    (hcaller_le : hp_caller ≤ hp_eff)
    (hFn : F1.n = F0.n)
    (hval1 : F1.Valid)
    (hfits1 : ∀ e ∈ F1.edges, EdgeFits h L P e)
    (hmem_safe_slot0 : SlotZeroOk mem_safe (lctNodesBase b))
    (hmem_safe_ptr : PtrFootOk b mem_safe x0 L)
    (hmem_safe_out : ∀ a, (a < b ∨ (lctArenaHi b (lctCap F0.n) ≤ a ∧ a < hp_caller)) →
      mem_safe a = mem0 a)
    (hsafe : SafeMem mem_safe (lctNodesBase b) (lctCap F0.n) hp_eff mem_end)
    (hsf : SplayForestOk w h L mem_end (lctNodesBase b) (lctCap F1.n) trees1)
    (hN1 : mem_end (b + LCT_HDR_N) = F1.n)
    (hCAP1 : mem_end (b + LCT_HDR_CAP) = lctCap F1.n)
    (hL1 : mem_end (b + LCT_HDR_L) = L)
    (hP1 : mem_end (b + LCT_HDR_P) = P)
    (hperme : (edgeMap1.map Prod.snd).Perm F1.edges)
    (hpermsl : ((edgeMap1.map Prod.fst) ++ freeEdges1).Perm ((List.range F1.n).map (F1.n + 1 + ·)))
    (hfree : FreeSlotChain mem_end (lctNodesBase b) (mem_end (b + LCT_HDR_FREE)) freeEdges1)
    (hfree_nd : ∀ ed ∈ freeEdges1, F1.n + 1 ≤ ed ∧ ed ≤ lctCap F1.n ∧
      AuxTree.node ed .leaf .leaf ∈ trees1 ∧
      nodeField mem_end (lctNodesBase b) ed OFF_PPAR = 0 ∧
      nodeField mem_end (lctNodesBase b) ed OFF_ISV = 0 ∧
      nodeField mem_end (lctNodesBase b) ed OFF_HASE = 0)
    (hvok : VertexNodeOk mem_end (lctNodesBase b) F1.n)
    (heok : ActiveEdgeNodeOk mem_end (lctNodesBase b) h L P F1.n trees1 edgeMap1)
    (hpok : LctAuxPathOk mem_end (lctNodesBase b) F1.n freeEdges1 trees1)
    (hsok : LctSubdivOk mem_end (lctNodesBase b) F1.n freeEdges1 edgeMap1)
    (hfin_lt : mem_end (lctNodesBase b - 1) + 1 < 2 ^ w)
    (hfin_sp : mem_end (lctNodesBase b - 1) + 1 ≤ hp_caller + space)
    (hag_fin : ∀ a, a < hp_caller ∨ hp_eff ≤ a → mem_fin a = mem_end a) :
    let hp_final := mem_end (lctNodesBase b - 1) + 1
    let x1 : LctConc :=
      { n := F1.n
        trees := trees1
        freeEdges := freeEdges1
        edgeMap := edgeMap1
        regions := x0.regions ++ [(hp_caller, hp_final)]
        hpHi := hp_final }
    LctMemRep w h L P b F1 x1 mem_fin ∧
    (lctDSRep w h L P).Respects (lctFoot b x0) hp_caller space mem0 hp_final b x1 mem_fin ∧
    lctPhi L mem_fin b F1.n = lctPhi L mem_end b F1.n := by
  intro hp_final x1
  let nb := lctNodesBase b
  let cap := lctCap F1.n
  let arenaHi := lctArenaHi b cap
  have hp_bd0 := hrep0.hp_le_of_foot hfoot0
  have hnb1_eq : nb - 1 = b + LCT_HDR_HP := by
    unfold nb lctNodesBase LCT_HDR_SIZE LCT_HDR_HP; omega
  have harena01 : lctArenaHi b (lctCap F0.n) = arenaHi := by
    simp [arenaHi, cap, lctArenaHi, lctCap, hFn]
  have har_le_caller : arenaHi ≤ hp_caller := by
    rw [← harena01]; exact le_trans hp_bd0.1 hp_bd0.2.1
  have hp_eff_le_end : hp_eff ≤ mem_end (nb - 1) := hsafe.1
  have har_le_end : arenaHi ≤ mem_end (nb - 1) := le_trans har_le_caller (le_trans hcaller_le hp_eff_le_end)
  have hbelow_ar : ∀ a < arenaHi, mem_fin a = mem_end a := fun a ha =>
    hag_fin a (Or.inl (lt_of_lt_of_le ha har_le_caller))
  have hag_ar : MemAgreeOn b arenaHi mem_end mem_fin := fun a _ ha => (hbelow_ar a ha).symm
  have hag_nb : MemAgreeOn nb arenaHi mem_end mem_fin := fun a ha1 ha2 =>
    hag_ar a (by unfold nb lctNodesBase at ha1; omega) ha2
  have hfld_fin : ∀ u ≤ cap, ∀ off < NODE_STRIDE,
      nodeField mem_fin nb u off = nodeField mem_end nb u off := fun u hu off hoff =>
    nodeField_agree_of_memAgree rfl hag_ar hu hoff
  have hhp_fin : mem_fin (nb - 1) = mem_end (nb - 1) := by
    apply hbelow_ar
    unfold arenaHi lctArenaHi nb lctNodesBase LCT_HDR_SIZE NODE_STRIDE; omega
  have hxn0 : x0.n = F0.n := hrep0.2.2.2.2.1
  have hpf_end : PtrFootOk b mem_end x1 L := by
    refine SafeMem.ptrFootOk_of_treeMemMatch (w := w) (h := h) (L := L) (b := b)
      (hp0 := hp_eff) (hp_caller := hp_caller) (x0 := x0) (x1 := x1)
      (hFn.trans hxn0.symm)
      (by simpa [nb, hxn0] using hsafe)
      hmem_safe_slot0 hmem_safe_ptr
      (by simpa [x1, hFn, hxn0] using hsf.perm)
      (fun t ht => by simpa [x1, hFn, hxn0] using (hsf.trees_ok t ht).2.2)
      hcaller_le hsafe.1
      (fun iv hiv => List.mem_append_left _ hiv)
      (List.mem_append_right _ (List.mem_singleton.2 rfl))
  have hptrs_fin : ∀ u ≤ cap, ∀ off ∈ ptrOffs,
      let ptr := nodeField mem_end nb u off
      ptr = 0 ∨ ∀ i < L, mem_fin (ptr + i) = mem_end (ptr + i) := fun u hu off hoff => by
    rcases hpf_end u (by simpa [x1] using hu) off hoff with h0 | ⟨harena_ptr, _, _⟩
    · exact Or.inl h0
    · refine Or.inr fun i hi => ?_
      have hu_eq : u ≤ lctCap F0.n := by simpa [cap, lctCap, hFn] using hu
      have har_pos : 0 < lctArenaHi b (lctCap F1.n) := by
        unfold lctArenaHi lctNodesBase LCT_HDR_SIZE NODE_STRIDE; omega
      dsimp only [x1] at harena_ptr
      by_cases hu0 : u = 0
      · subst hu0
        have hlt := ptrOffs_lt_stride hoff
        have h00 : nodeField mem_end (lctNodesBase b) 0 off = 0 := by
          simpa [nodeField] using hsf.2.2.2.2.2.2.2.1 off hlt
        omega
      · have hu1 : 1 ≤ u := Nat.pos_of_ne_zero hu0
        rcases hsafe.2.2.2 u off hu1 hu_eq hoff with h0 | hge | ⟨y, off', _, hy2, hoff', hy_eq⟩
        · omega
        · dsimp only [nb]; exact hag_fin _ (Or.inr (by omega))
        · rcases hmem_safe_ptr y (hxn0 ▸ hy2) off' hoff' with h0 | ⟨_, _, hpf_y⟩
          · rw [h0] at hy_eq; omega
          · have hlt_i : i < max 1 L := lt_of_lt_of_le hi (le_max_right 1 L)
            have hfoot_y := hpf_y (nodeField mem_safe (lctNodesBase b) y off' + i) (by omega) (by omega)
            rw [← hy_eq] at hfoot_y
            dsimp only [nb]; exact hag_fin _ (Or.inl (hfoot0 _ hfoot_y))
  have hs0_end : SlotZeroOk mem_end nb := hsf.2.2.2.2.2.2.2.1
  have hs0_fin : SlotZeroOk mem_fin nb := fun off hoff => by
    rw [show mem_fin (nb + off) = nodeField mem_fin nb 0 off by rfl,
      hfld_fin 0 (Nat.zero_le _) off hoff]
    exact hs0_end off hoff
  have hfree_bd : ∀ ed ∈ freeEdges1, ed ≤ cap := fun ed hed => (hfree_nd ed hed).2.1
  have htr_fin := transfer_struct_of_agree_ptrs hag_nb
    (hbelow_ar (b + LCT_HDR_FREE) (by
      dsimp only [arenaHi]; unfold lctArenaHi lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE NODE_STRIDE; omega))
    hsf.perm hsf.trees_ok hptrs_fin hfree_bd hfree hvok heok hpok hsok
  have hht_le : ∀ {t}, t ∈ trees1 → ∀ u ∈ t.toList, u ≤ cap := fun {t} ht u hu => by
    have hm := hsf.perm.mem_iff.1 (List.mem_flatMap.2 ⟨t, ht, hu⟩)
    rcases List.mem_map.1 hm with ⟨y, hy, rfl⟩; rw [List.mem_range] at hy; omega
  have htrees_fin : ∀ t ∈ trees1, t ≠ .leaf ∧ nodeField mem_fin nb t.rootId OFF_PPAR < 2 ^ w ∧
      TreeMemMatch w h L mem_fin nb cap t 0 (nodeField mem_fin nb t.rootId OFF_PPAR) := by
    intro t ht
    rcases hsf.trees_ok t ht with ⟨hne, hppw, htm⟩
    have hrt : t.rootId ≤ cap := hht_le ht t.rootId (AuxTree.rootId_mem_toList hne)
    rw [hfld_fin t.rootId hrt OFF_PPAR (by decide)]
    refine ⟨hne, hppw, memAgree_treeMemMatch_of_ptrs htm hhp_fin
      (fun u hu off hoff => hfld_fin u (hht_le ht u hu) off hoff)
      (fun u hu off hoff => hptrs_fin u (hht_le ht u hu) off hoff)⟩
  have hz_fin : ZeroFrom mem_fin hp_final := fun a ha => by
    have ha_end : mem_end (nb - 1) + 1 ≤ a := by dsimp only [hp_final, nb] at ha ⊢; exact ha
    have ha_eff : hp_eff ≤ a := le_trans hp_eff_le_end (by omega)
    rw [hag_fin a (Or.inr ha_eff)]
    exact hsf.2.2.2.2.2.2.1 a (by omega)
  have hpf_fin : PtrFootOk b mem_fin x1 L := fun u hu off hoff => by
    have hu' : u ≤ cap := by simpa [x1] using hu
    dsimp only
    rw [hfld_fin u hu' off (ptrOffs_lt_stride hoff), hhp_fin]
    exact hpf_end u hu off hoff
  have hphi_fin : lctPhi L mem_fin b F1.n = lctPhi L mem_end b F1.n :=
    lctPhi_agree hag_nb
  have hhdr_read : ∀ off < LCT_HDR_SIZE, mem_fin (b + off) = mem_end (b + off) := fun off hoff =>
    hbelow_ar (b + off) (by unfold arenaHi lctArenaHi nb lctNodesBase LCT_HDR_SIZE NODE_STRIDE at *; omega)
  have hrep_fin : LctMemRep w h L P b F1 x1 mem_fin := by
    refine ⟨hrep0.1, hrep0.2.1, hval1, hfits1, rfl, ?_, Nat.succ_pos _, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, hperme, hpermsl, htr_fin.1, ?_, hs0_fin, hsf.perm,
      htrees_fin, htr_fin.2.1, htr_fin.2.2.1, htr_fin.2.2.2.1, htr_fin.2.2.2.2, hpf_fin⟩
    · simp only [x1]; exact le_trans har_le_end (Nat.le_succ _)
    · simp only [x1, lctFoot, List.mem_append, List.mem_singleton]
      right; refine ⟨(hp_caller, hp_final), Or.inr rfl, ?_, ?_⟩
      · exact le_trans hcaller_le hp_eff_le_end
      · simp [hp_final]
    · intro iv hiv
      simp only [x1, List.mem_append, List.mem_singleton] at hiv
      rcases hiv with hiv | rfl
      · rcases hrep0 with ⟨_, _, _, _, _, _, _, _, hreg0, _⟩
        rcases hreg0 iv hiv with ⟨hb1, hb2, hb3⟩
        exact ⟨hb1, hb2, le_trans hb3 (le_trans hp_bd0.2.2 (le_trans hcaller_le (le_trans hp_eff_le_end (Nat.le_succ _))))⟩
      · exact ⟨le_trans (by dsimp only [arenaHi] at har_le_caller; unfold lctArenaHi lctNodesBase LCT_HDR_SIZE NODE_STRIDE at har_le_caller; omega)
            (le_refl _),
          by simp [hp_final]; exact le_trans hcaller_le hp_eff_le_end, le_rfl⟩
    · rw [hhdr_read LCT_HDR_N (by decide)]; exact hN1
    · rw [hhdr_read LCT_HDR_CAP (by decide)]; exact hCAP1
    · rw [hhdr_read LCT_HDR_L (by decide)]; exact hL1
    · rw [hhdr_read LCT_HDR_P (by decide)]; exact hP1
    · rw [← hnb1_eq, hhp_fin]; exact har_le_end
    · rw [← hnb1_eq, hhp_fin]; exact Nat.le_succ _
    · rw [← hnb1_eq, hhp_fin]; exact lt_of_le_of_lt (Nat.le_succ _) hfin_lt
    · intro ed hed
      rcases hfree_nd ed hed with ⟨h1, h2, h3, h4, h5, h6⟩
      exact ⟨h1, h2, h3,
        by rw [hfld_fin ed h2 OFF_PPAR (by decide)]; exact h4,
        by rw [hfld_fin ed h2 OFF_ISV (by decide)]; exact h5,
        by rw [hfld_fin ed h2 OFF_HASE (by decide)]; exact h6⟩
  have hresp : (lctDSRep w h L P).Respects (lctFoot b x0) hp_caller space mem0 hp_final b x1 mem_fin := by
    refine ⟨le_trans hcaller_le (le_trans hp_eff_le_end (Nat.le_succ _)), hfin_sp, hz_fin, ?_, ?_⟩
    · intro a ha_lt ha_not
      rw [hag_fin a (Or.inl ha_lt)]
      have hnot_ar : ¬ (b ≤ a ∧ a < lctArenaHi b (lctCap x0.n)) := fun h =>
        ha_not (Or.inl h)
      have ha_cases : a < b ∨ lctArenaHi b (lctCap F0.n) ≤ a := by
        rw [hxn0] at hnot_ar; omega
      have heq1 : mem_end a = mem_safe a := hsafe.2.1 a (by
        rcases ha_cases with hlt | hge
        · left; unfold lctNodesBase LCT_HDR_SIZE; omega
        · right; right; refine ⟨by simpa [lctArenaHi] using hge, lt_of_lt_of_le ha_lt hcaller_le⟩)
      have heq2 : mem_safe a = mem0 a := hmem_safe_out a (by
        rcases ha_cases with hlt | hge
        · exact Or.inl hlt
        · exact Or.inr ⟨hge, ha_lt⟩)
      exact heq1.trans heq2
    · intro a ha_foot
      simp only [lctDSRep, lctFoot, x1, List.mem_append, List.mem_singleton] at ha_foot
      rcases ha_foot with ⟨ha1, ha2⟩ | ⟨iv, (hiv | rfl), ha1, ha2⟩
      · exact Or.inl (Or.inl ⟨ha1, by simpa [lctArenaHi, lctCap, hFn, hxn0] using ha2⟩)
      · exact Or.inl (Or.inr ⟨iv, hiv, ha1, ha2⟩)
      · exact Or.inr ⟨ha1, ha2⟩
  exact ⟨hrep_fin, hresp, hphi_fin⟩

/-- Run `sp.splay` from any `SplayForestOk` + `SafeMem` state, advancing `SplayForestOk`,
`SafeMem`, and the Sleator–Tarjan potential `splayMemPhi`. -/
theorem splayForest_lct_runs {w h L : ℕ} (p : Program) (sp : SplayProcs)
    (mem_safe mem₀ : ℕ → ℕ) (nb cap hp0 pos : ℕ) {trees : List AuxTree}
    (hp_has : p.HasAt sp.numZero (splayBodies sp h))
    (hp_base : ∃ spB, sp = SplayProcs.atBase spB)
    (hp_ok : SplayProgramOk w h p sp)
    (hz0_safe : SlotZeroOk mem_safe nb)
    (harena_safe : nb + NODE_STRIDE * (cap + 1) ≤ hp0)
    (hsafe : SafeMem mem_safe nb cap hp0 mem₀)
    (hok : SplayForestOk w h L mem₀ nb cap trees)
    {t : AuxTree} {rest : List AuxTree} {x : ℕ}
    (ht_perm : trees.Perm (t :: rest)) (hx : x ∈ t.toList)
    (hhp_lt : mem₀ (nb - 1) + K_PUSH_PATH L * (t.depthOf x + 1) + 8 * L * t.depthOf x < 2 ^ w) :
    ∀ ω, ∃ st' c t',
      Runs w p ω (splayBody sp) (startState [nb, x] mem₀ pos) (.returned x) st' c ∧
      SplayForestOk w h L st'.mem nb cap (t' :: rest) ∧
      SafeMem mem_safe nb cap hp0 st'.mem ∧
      t'.rootId = x ∧
      t'.toList.Perm t.toList ∧
      t'.evalInorder (revFlag st'.mem nb) false = t.evalInorder (revFlag mem₀ nb) false ∧
      evalMemSteps st'.mem nb h L t' false 0 = evalMemSteps mem₀ nb h L t false 0 ∧
      revFlag st'.mem nb x = false ∧
      nodeField st'.mem nb x OFF_HAS_TAG = 0 ∧
      nodeField st'.mem nb x OFF_PPAR = nodeField mem₀ nb t.rootId OFF_PPAR ∧
      (∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
        nodeField st'.mem nb u off = nodeField mem₀ nb u off) ∧
      (∀ u ≤ cap, ∀ off, IsStaticPayloadOff off →
        nodeField st'.mem nb u off = nodeField mem₀ nb u off) ∧
      LctFrame (nb + NODE_STRIDE) (nb + NODE_STRIDE * (cap + 1)) (nb - 1) mem₀ st'.mem ∧
      (∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧
        2 * K_PUSH_PATH L * (t.depthOf x / 2) +
          splayMemPhi (K_SPLAY_STEP L) st'.mem nb cap vSize +
          3 * K_SPLAY_STEP L * Nat.log 2 (1 + vSize x) ≤
          splayMemPhi (K_SPLAY_STEP L) mem₀ nb cap vSize +
            3 * K_SPLAY_STEP L * t.rank vSize + (K_ROTATE L + 42) ∧
        c + (st'.mem (nb - 1) - mem₀ (nb - 1)) +
          splayMemPhi (K_SPLAY_STEP L) st'.mem nb cap vSize +
          3 * K_SPLAY_STEP L * Nat.log 2 (1 + vSize x) ≤
          splayMemPhi (K_SPLAY_STEP L) mem₀ nb cap vSize +
            3 * K_SPLAY_STEP L * t.rank vSize + C_SPLAY_CONST L) := by
  intro ω
  rcases hp_base with ⟨spB, rfl⟩
  rcases splayForest_runs p (SplayProcs.atBase spB) mem₀ pos hp_ok hok ht_perm hx hhp_lt ω with
    ⟨st', c, t', hr, hok', hroot', hperm', hev', hsteps', hrev', hht', hpp', hout', hstat', hlct', hphi'⟩
  rcases hr with ⟨fuel, hex⟩
  have hnb3 := hok.2.2.1
  have hx_le : x ≤ cap := by
    have hm := hok.perm.mem_iff.1 (List.mem_flatMap.2 ⟨t, ht_perm.symm.subset (by simp), hx⟩)
    rcases List.mem_map.1 hm with ⟨y, hy, rfl⟩; rw [List.mem_range] at hy; omega
  have hsafe' : SafeMem mem_safe nb cap hp0 st'.mem :=
    (splay_safeExec (spBase := spB) hp_has hnb3 harena_safe hz0_safe hx_le
      (by simp [startState]) (by simp [startState]) hsafe hex).2
  exact ⟨st', c, t', ⟨fuel, hex⟩, hok', hsafe', hroot', hperm', hev', hsteps', hrev', hht', hpp',
    hout', hstat', hlct', hphi'⟩

end EntryExitAndSplay

end MinCostFlow.LinkCut.Prog
