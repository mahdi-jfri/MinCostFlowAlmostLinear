module

public import MinCostFlow.LinkCut.Prog.MathForestLinkShape

/-!
# Pre-Splice Shape, Field Writes, and `PullPre` for `link`

Shared splay invariant wrapper (`splay_expose_invs_runs`), memory-weakening
(`link_safeMem_weaken`), component-disjointness (`rerootExpose_link_runs`,
`link_not_sameComp_disjoint`, `link_find_u_tree`, `link_splayed_u_leaf_left`),
node-field writer (`writeNodeOffs`, `lctLinkWriteMem`), and `PullPre` (`lctLink_pullPre`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section LinkPreShape

/-- After `splay (u + 1)` with `lctAuxParent st₃.mem nb cap (u + 1) = 0`, the splayed tree `t_u'`
has an empty left child (`t_u' = .node (u + 1) .leaf r_u`) and `OFF_PPAR(u + 1) = 0`. -/
theorem link_splayed_u_leaf_left {w h L P b n u : ℕ} {freeEdges : List ℕ}
    {edgeMap : List (ℕ × ForestEdge)} {t_u' : AuxTree} {rest : List AuxTree} {mem : ℕ → ℕ}
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap (t_u' :: rest) mem)
    (hroot : t_u'.rootId = u + 1)
    (hrev : revFlag mem (lctNodesBase b) (u + 1) = false)
    (hpar_u : lctAuxParent mem (lctNodesBase b) (lctCap n) (u + 1) = 0) :
    ∃ r_u,
      t_u' = AuxTree.node (u + 1) .leaf r_u ∧
      nodeField mem (lctNodesBase b) (u + 1) OFF_PPAR = 0 := by
  let nb := lctNodesBase b
  let cap := lctCap n
  have hrev_nb : revFlag mem nb (u + 1) = false := hrev
  cases ht_eq : t_u' with
  | leaf => exact absurd ht_eq (hi.sf.trees_ok t_u' (by simp)).1
  | node rid l_u r_u =>
      have hrid : rid = u + 1 := by simpa [ht_eq, AuxTree.rootId] using hroot
      subst hrid
      have htu_mem : AuxTree.node (u + 1) l_u r_u ∈ t_u' :: rest := by rw [ht_eq]; exact List.mem_cons_self
      have htu_tok := (hi.sf.trees_ok (AuxTree.node (u + 1) l_u r_u) htu_mem).2.2
      have htree_seq : lctTreeSeq mem nb cap (u + 1) =
          (AuxTree.node (u + 1) l_u r_u).evalInorder (revFlag mem nb) false := by
        simpa [AuxTree.rootId, nb, cap] using
          hi.sf.lctTreeSeq_eq (t := AuxTree.node (u + 1) l_u r_u) htu_mem
      have hseq_split : (AuxTree.node (u + 1) l_u r_u).evalInorder (revFlag mem nb) false =
          l_u.evalInorder (revFlag mem nb) false ++ [u + 1] ++
          r_u.evalInorder (revFlag mem nb) false := by
        rw [AuxTree.evalInorder, hrev_nb]
      have hl_leaf : l_u = .leaf := by
        by_contra hl_ne
        have hl_seq_ne : l_u.evalInorder (revFlag mem nb) false ≠ [] :=
          auxTree_eval_ne_nil_of_ne_leaf hl_ne
        set ls := l_u.evalInorder (revFlag mem nb) false
        have hlen_pos : 0 < ls.length := List.length_pos_of_ne_nil hl_seq_ne
        have hidx_lt : ls.length < (lctTreeSeq mem nb cap (u + 1)).length := by
          rw [htree_seq, hseq_split]
          simp only [List.length_append, List.length_singleton]
          omega
        have hp := lctAuxParent_of_tree hi.sf hi.ppar_le_cap htu_mem ls.length hidx_lt
        have hget_at : (lctTreeSeq mem nb cap (u + 1))[ls.length] = u + 1 := by
          have : (ls ++ [u + 1] ++ r_u.evalInorder (revFlag mem nb) false)[ls.length]'(by
              rw [← hseq_split, ← htree_seq]; exact hidx_lt) = u + 1 := by
            have h1 : ls ++ [u + 1] ++ r_u.evalInorder (revFlag mem nb) false =
                ls ++ ([u + 1] ++ r_u.evalInorder (revFlag mem nb) false) := List.append_assoc _ _ _
            simp only [h1, List.getElem_append_right (le_refl ls.length), Nat.sub_self,
              List.singleton_append, List.getElem_cons_zero]
          simp [htree_seq, hseq_split]
        have hprev_lt : ls.length - 1 < ls.length := Nat.sub_lt hlen_pos (by omega)
        have hget_prev : (lctTreeSeq mem nb cap (u + 1))[ls.length - 1]! = ls[ls.length - 1] := by
          have hlt2 : ls.length - 1 < (lctTreeSeq mem nb cap (u + 1)).length := by omega
          rw [getElem!_def, List.getElem?_eq_getElem hlt2]
          dsimp only [Option.getD]
          have : (ls ++ ([u + 1] ++ r_u.evalInorder (revFlag mem nb) false))[ls.length - 1]'(by
              simpa [htree_seq, hseq_split, List.append_assoc] using hlt2) = ls[ls.length - 1] :=
            List.getElem_append_left hprev_lt
          simpa [htree_seq, hseq_split, List.append_assoc] using this
        have hne0 : ls.length ≠ 0 := by omega
        simp only [AuxTree.rootId, hne0, ↓reduceIte] at hp
        rw [hget_at, hget_prev] at hp
        have hp_ls_mem : ls[ls.length - 1] ∈ (AuxTree.node (u + 1) l_u r_u).toList := by
          have h1 : ls[ls.length - 1] ∈ l_u.toList :=
            (l_u.evalInorder_perm (revFlag mem nb) false).mem_iff.1 (List.getElem_mem hprev_lt)
          simp [AuxTree.toList, h1]
        have hbd := htu_tok.nodup_perm_mem hp_ls_mem
        have : lctAuxParent mem nb cap (u + 1) = ls[ls.length - 1] := hp
        omega
      subst hl_leaf
      have hseq0 : lctTreeSeq mem nb cap (u + 1) =
          (u + 1) :: r_u.evalInorder (revFlag mem nb) false := by
        simpa [AuxTree.evalInorder] using htree_seq.trans hseq_split
      have hlen0 : 0 < (lctTreeSeq mem nb cap (u + 1)).length := by rw [hseq0]; simp
      have hp0 := lctAuxParent_of_tree hi.sf hi.ppar_le_cap htu_mem 0 hlen0
      simp only [↓reduceIte, AuxTree.rootId] at hp0
      have hget0 : (lctTreeSeq mem nb cap (u + 1))[0] = u + 1 := by simp [hseq0]
      rw [hget0] at hp0
      exact ⟨r_u, rfl, by simpa [nb, cap, hpar_u] using hp0.symm⟩

end LinkPreShape

section LinkWriteMemAndPullPre

private lemma nodeAddr_inj_stride {nb u₁ off₁ u₂ off₂ : ℕ}
    (ho₁ : off₁ < NODE_STRIDE) (ho₂ : off₂ < NODE_STRIDE)
    (heq : nb + NODE_STRIDE * u₁ + off₁ = nb + NODE_STRIDE * u₂ + off₂) :
    u₁ = u₂ ∧ off₁ = off₂ := by
  by_contra hne
  rcases Nat.lt_trichotomy u₁ u₂ with hlt | rfl | hgt
  · have hm : NODE_STRIDE * (u₁ + 1) ≤ NODE_STRIDE * u₂ := Nat.mul_le_mul_left _ hlt
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega
  · omega
  · have hm : NODE_STRIDE * (u₂ + 1) ≤ NODE_STRIDE * u₁ := Nat.mul_le_mul_left _ hgt
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega

/-- Applies a sequence of `(off, val)` field updates on node `x` at `nb`. -/
def writeNodeOffs (mem : ℕ → ℕ) (nb x : ℕ) : List (ℕ × ℕ) → (ℕ → ℕ)
  | [] => mem
  | (off, val) :: rest =>
      writeNodeOffs (Function.update mem (nb + NODE_STRIDE * x + off) val) nb x rest

theorem writeNodeOffs_outside {mem : ℕ → ℕ} {nb x : ℕ} {kvs : List (ℕ × ℕ)} {a : ℕ}
    (hoff : ∀ p ∈ kvs, p.1 < NODE_STRIDE)
    (hout : a < nb + NODE_STRIDE * x ∨ nb + NODE_STRIDE * x + NODE_STRIDE ≤ a) :
    writeNodeOffs mem nb x kvs a = mem a := by
  induction kvs generalizing mem with
  | nil => rfl
  | cons hd tl ih =>
      have hhd_lt := hoff hd List.mem_cons_self
      have hne : a ≠ nb + NODE_STRIDE * x + hd.1 := by omega
      rw [writeNodeOffs, ih (fun p hp => hoff p (List.mem_cons_of_mem _ hp)),
        Function.update_of_ne hne]

theorem writeNodeOffs_nodeField_other {mem : ℕ → ℕ} {nb x u off : ℕ} {kvs : List (ℕ × ℕ)}
    (hpk : ∀ p ∈ kvs, p.1 < NODE_STRIDE) (hoff : off < NODE_STRIDE) (hne : u ≠ x) :
    nodeField (writeNodeOffs mem nb x kvs) nb u off = nodeField mem nb u off := by
  induction kvs generalizing mem with
  | nil => rfl
  | cons hd tl ih =>
      have hhd_lt := hpk hd List.mem_cons_self
      have haddr_ne : nb + NODE_STRIDE * u + off ≠ nb + NODE_STRIDE * x + hd.1 := fun heq =>
        hne (nodeAddr_inj_stride hoff hhd_lt heq).1
      rw [writeNodeOffs, ih (fun p hp => hpk p (List.mem_cons_of_mem _ hp))]
      change Function.update mem (nb + NODE_STRIDE * x + hd.1) hd.2 (nb + NODE_STRIDE * u + off) =
        mem (nb + NODE_STRIDE * u + off)
      simp [Function.update_of_ne haddr_ne]

theorem writeNodeOffs_nodeField_notin {mem : ℕ → ℕ} {nb x off : ℕ} {kvs : List (ℕ × ℕ)}
    (hpk : ∀ p ∈ kvs, p.1 < NODE_STRIDE) (hnin : off ∉ kvs.map Prod.fst) :
    nodeField (writeNodeOffs mem nb x kvs) nb x off = nodeField mem nb x off := by
  induction kvs generalizing mem with
  | nil => rfl
  | cons hd tl ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at hnin
      have hne : nb + NODE_STRIDE * x + off ≠ nb + NODE_STRIDE * x + hd.1 := by omega
      rw [writeNodeOffs, ih (fun p hp => hpk p (List.mem_cons_of_mem _ hp)) hnin.2]
      change Function.update mem (nb + NODE_STRIDE * x + hd.1) hd.2 (nb + NODE_STRIDE * x + off) =
        mem (nb + NODE_STRIDE * x + off)
      simp [Function.update_of_ne hne]

theorem writeNodeOffs_nodeField_mem {mem : ℕ → ℕ} {nb x : ℕ} {kvs : List (ℕ × ℕ)}
    (hnd : (kvs.map Prod.fst).Nodup) (hpk : ∀ p ∈ kvs, p.1 < NODE_STRIDE)
    {p : ℕ × ℕ} (hp : p ∈ kvs) :
    nodeField (writeNodeOffs mem nb x kvs) nb x p.1 = p.2 := by
  induction kvs generalizing mem with
  | nil => simp at hp
  | cons hd tl ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.1 hp with rfl | hptl
      · rw [writeNodeOffs,
          writeNodeOffs_nodeField_notin (fun q hq => hpk q (List.mem_cons_of_mem _ hq)) hnd.1]
        exact Function.update_self _ _ _
      · exact ih hnd.2 (fun q hq => hpk q (List.mem_cons_of_mem _ hq)) hptl

theorem writeNodeOffs_safeMem {mem₀ mem : ℕ → ℕ} {nb cap hp0 x : ℕ} {kvs : List (ℕ × ℕ)}
    (hnb3 : 3 ≤ nb) (harena : nb + NODE_STRIDE * (cap + 1) ≤ hp0)
    (hx1 : 1 ≤ x) (hx2 : x ≤ cap)
    (hsafe : SafeMem mem₀ nb cap hp0 mem)
    (hpk : ∀ p ∈ kvs,
      p.1 < NODE_STRIDE ∧
      ((p.1 = OFF_LEFT ∨ p.1 = OFF_RIGHT ∨ p.1 = OFF_PARENT) → p.2 ≤ cap) ∧
      (p.1 ∈ ptrOffs → PtrAllowed mem₀ nb cap hp0 p.2)) :
    SafeMem mem₀ nb cap hp0 (writeNodeOffs mem nb x kvs) := by
  induction kvs generalizing mem with
  | nil => exact hsafe
  | cons hd tl ih =>
      have hhd := hpk hd List.mem_cons_self
      exact ih (SafeMem.update_field hsafe hnb3 harena hx1 hx2 hhd.1 hhd.2.1 hhd.2.2)
        (fun p hp => hpk p (List.mem_cons_of_mem _ hp))

/-- Non-aggregate field updates written to the popped edge slot `ed` during `link`. -/
def lctLinkOffPairs (u v eid p_cf p_cb p_fl p_af p_ab : ℕ) : List (ℕ × ℕ) :=
  [ (OFF_LEFT, 0),
    (OFF_RIGHT, u + 1),
    (OFF_PARENT, 0),
    (OFF_PPAR, v + 1),
    (OFF_REV, 0),
    (OFF_ISV, 0),
    (OFF_HASE, 1),
    (OFF_DIR, 0),
    (OFF_HAS_TAG, 0),
    (OFF_TAG_PTR, 0),
    (OFF_TAG_NEG, 0),
    (OFF_EID, eid),
    (OFF_EU, u),
    (OFF_EV, v),
    (OFF_COST_FWD, p_cb),
    (OFF_COST_BWD, p_cf),
    (OFF_FLOW_PTR, p_fl),
    (OFF_AF_PTR, p_ab),
    (OFF_AB_PTR, p_af) ]

theorem lctLinkOffPairs_nodup (u v eid p_cf p_cb p_fl p_af p_ab : ℕ) :
    ((lctLinkOffPairs u v eid p_cf p_cb p_fl p_af p_ab).map Prod.fst).Nodup := by
  have hmap : (lctLinkOffPairs u v eid p_cf p_cb p_fl p_af p_ab).map Prod.fst =
      [OFF_LEFT, OFF_RIGHT, OFF_PARENT, OFF_PPAR, OFF_REV, OFF_ISV, OFF_HASE, OFF_DIR,
       OFF_HAS_TAG, OFF_TAG_PTR, OFF_TAG_NEG, OFF_EID, OFF_EU, OFF_EV, OFF_COST_FWD,
       OFF_COST_BWD, OFF_FLOW_PTR, OFF_AF_PTR, OFF_AB_PTR] := rfl
  rw [hmap]
  decide

theorem lctLinkOffPairs_lt_stride (u v eid p_cf p_cb p_fl p_af p_ab : ℕ) :
    ∀ p ∈ lctLinkOffPairs u v eid p_cf p_cb p_fl p_af p_ab, p.1 < NODE_STRIDE := by
  intro p hp
  have hfst : p.1 ∈ (lctLinkOffPairs u v eid p_cf p_cb p_fl p_af p_ab).map Prod.fst :=
    List.mem_map.2 ⟨p, hp, rfl⟩
  have hmap : (lctLinkOffPairs u v eid p_cf p_cb p_fl p_af p_ab).map Prod.fst =
      [OFF_LEFT, OFF_RIGHT, OFF_PARENT, OFF_PPAR, OFF_REV, OFF_ISV, OFF_HASE, OFF_DIR,
       OFF_HAS_TAG, OFF_TAG_PTR, OFF_TAG_NEG, OFF_EID, OFF_EU, OFF_EV, OFF_COST_FWD,
       OFF_COST_BWD, OFF_FLOW_PTR, OFF_AF_PTR, OFF_AB_PTR] := rfl
  rw [hmap] at hfst
  have hlt_all : ∀ x ∈ [OFF_LEFT, OFF_RIGHT, OFF_PARENT, OFF_PPAR, OFF_REV, OFF_ISV, OFF_HASE,
      OFF_DIR, OFF_HAS_TAG, OFF_TAG_PTR, OFF_TAG_NEG, OFF_EID, OFF_EU, OFF_EV, OFF_COST_FWD,
      OFF_COST_BWD, OFF_FLOW_PTR, OFF_AF_PTR, OFF_AB_PTR], x < NODE_STRIDE := by decide
  exact hlt_all p.1 hfst

/-- Pure memory state produced by `link`'s free-list pop and pointer-splice writes prior to `pull`. -/
def lctLinkWriteMem (mem : ℕ → ℕ) (nb b u v eid p_cf p_cb p_fl p_af p_ab nextFree ed : ℕ) :
    ℕ → ℕ :=
  let mem_free := Function.update mem (b + LCT_HDR_FREE) nextFree
  let mem_ed := writeNodeOffs mem_free nb ed (lctLinkOffPairs u v eid p_cf p_cb p_fl p_af p_ab)
  Function.update mem_ed (nb + NODE_STRIDE * (u + 1) + OFF_PARENT) ed

theorem lctLinkWriteMem_outside {mem : ℕ → ℕ} {nb b u v eid p_cf p_cb p_fl p_af p_ab nextFree ed a : ℕ}
    (hfree : a ≠ b + LCT_HDR_FREE)
    (hed : a < nb + NODE_STRIDE * ed ∨ nb + NODE_STRIDE * ed + NODE_STRIDE ≤ a)
    (hu : a ≠ nb + NODE_STRIDE * (u + 1) + OFF_PARENT) :
    lctLinkWriteMem mem nb b u v eid p_cf p_cb p_fl p_af p_ab nextFree ed a = mem a := by
  dsimp only [lctLinkWriteMem]
  rw [Function.update_of_ne hu,
    writeNodeOffs_outside (lctLinkOffPairs_lt_stride u v eid p_cf p_cb p_fl p_af p_ab) hed,
    Function.update_of_ne hfree]

theorem lctLinkWriteMem_hdr_free {mem : ℕ → ℕ} {nb b u v eid p_cf p_cb p_fl p_af p_ab nextFree ed : ℕ}
    (hnb : nb = lctNodesBase b) (h1 : 1 ≤ ed) (h2 : 1 ≤ u + 1) :
    lctLinkWriteMem mem nb b u v eid p_cf p_cb p_fl p_af p_ab nextFree ed (b + LCT_HDR_FREE) =
      nextFree := by
  have hlt_ed : b + LCT_HDR_FREE < nb + NODE_STRIDE * ed := by
    have hmul : NODE_STRIDE ≤ NODE_STRIDE * ed := Nat.le_mul_of_pos_right _ h1
    rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE NODE_STRIDE at *; omega
  have hne_u : b + LCT_HDR_FREE ≠ nb + NODE_STRIDE * (u + 1) + OFF_PARENT := by
    have hmul : NODE_STRIDE ≤ NODE_STRIDE * (u + 1) := Nat.le_mul_of_pos_right _ h2
    rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE NODE_STRIDE at *; omega
  dsimp only [lctLinkWriteMem]
  rw [Function.update_of_ne hne_u,
    writeNodeOffs_outside (lctLinkOffPairs_lt_stride u v eid p_cf p_cb p_fl p_af p_ab) (Or.inl hlt_ed),
    Function.update_self]

theorem lctLinkWriteMem_nodeField_other {mem : ℕ → ℕ} {nb b u v eid p_cf p_cb p_fl p_af p_ab nextFree ed z off : ℕ}
    (hnb : nb = lctNodesBase b) (hz1 : 1 ≤ z) (hoff : off < NODE_STRIDE)
    (hne_ed : z ≠ ed) (hne_u : z = u + 1 → off ≠ OFF_PARENT) :
    nodeField (lctLinkWriteMem mem nb b u v eid p_cf p_cb p_fl p_af p_ab nextFree ed) nb z off =
      nodeField mem nb z off := by
  have hfree : nb + NODE_STRIDE * z + off ≠ b + LCT_HDR_FREE := by
    have hmul : NODE_STRIDE ≤ NODE_STRIDE * z := Nat.le_mul_of_pos_right _ hz1
    rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE NODE_STRIDE at *; omega
  have hne_addr : nb + NODE_STRIDE * z + off ≠ nb + NODE_STRIDE * (u + 1) + OFF_PARENT := fun heq => by
    have hinv := nodeAddr_inj_stride hoff (by decide : OFF_PARENT < NODE_STRIDE) heq
    exact hne_u hinv.1 hinv.2
  dsimp only [nodeField, lctLinkWriteMem]
  rw [Function.update_of_ne hne_addr]
  change nodeField (writeNodeOffs (Function.update mem (b + LCT_HDR_FREE) nextFree) nb ed
      (lctLinkOffPairs u v eid p_cf p_cb p_fl p_af p_ab)) nb z off = nodeField mem nb z off
  rw [writeNodeOffs_nodeField_other (lctLinkOffPairs_lt_stride _ _ _ _ _ _ _ _) hoff hne_ed]
  change Function.update mem (b + LCT_HDR_FREE) nextFree (nb + NODE_STRIDE * z + off) =
    mem (nb + NODE_STRIDE * z + off)
  simp [Function.update_of_ne hfree]

theorem lctLinkWriteMem_nodeField_u_parent {mem : ℕ → ℕ}
    {nb b u v eid p_cf p_cb p_fl p_af p_ab nextFree ed : ℕ} :
    nodeField (lctLinkWriteMem mem nb b u v eid p_cf p_cb p_fl p_af p_ab nextFree ed)
      nb (u + 1) OFF_PARENT = ed := by
  dsimp only [nodeField, lctLinkWriteMem]
  exact Function.update_self _ _ _

theorem lctLinkWriteMem_nodeField_ed {mem : ℕ → ℕ}
    {nb b u v eid p_cf p_cb p_fl p_af p_ab nextFree ed : ℕ}
    (hne : ed ≠ u + 1) (off val : ℕ)
    (hp : (off, val) ∈ lctLinkOffPairs u v eid p_cf p_cb p_fl p_af p_ab) :
    nodeField (lctLinkWriteMem mem nb b u v eid p_cf p_cb p_fl p_af p_ab nextFree ed) nb ed off =
      val := by
  have hlt_p := lctLinkOffPairs_lt_stride u v eid p_cf p_cb p_fl p_af p_ab (off, val) hp
  have hne_addr : nb + NODE_STRIDE * ed + off ≠ nb + NODE_STRIDE * (u + 1) + OFF_PARENT := fun heq =>
    hne (nodeAddr_inj_stride hlt_p (by decide : OFF_PARENT < NODE_STRIDE) heq).1
  dsimp only [nodeField, lctLinkWriteMem]
  rw [Function.update_of_ne hne_addr]
  exact writeNodeOffs_nodeField_mem (lctLinkOffPairs_nodup _ _ _ _ _ _ _ _)
    (lctLinkOffPairs_lt_stride _ _ _ _ _ _ _ _) hp

theorem lctLinkWriteMem_safeMem {mem₀ mem : ℕ → ℕ}
    {b nb cap hp_caller u v eid p_cf p_cb p_fl p_af p_ab nextFree ed : ℕ}
    (hnb : nb = lctNodesBase b)
    (harena_safe : nb + NODE_STRIDE * (cap + 1) ≤ hp_caller)
    (hu_le : u + 1 ≤ cap) (hv_le : v + 1 ≤ cap) (hed1 : 1 ≤ ed) (hed2 : ed ≤ cap)
    (hp_cf : hp_caller ≤ p_cf) (hp_cb : hp_caller ≤ p_cb)
    (hp_fl : hp_caller ≤ p_fl) (hp_af : hp_caller ≤ p_af) (hp_ab : hp_caller ≤ p_ab)
    (hsafe : SafeMem mem₀ nb cap hp_caller mem) :
    SafeMem (Function.update mem₀ (b + LCT_HDR_FREE) nextFree) nb cap hp_caller
      (lctLinkWriteMem mem nb b u v eid p_cf p_cb p_fl p_af p_ab nextFree ed) := by
  let mem₀' := Function.update mem₀ (b + LCT_HDR_FREE) nextFree
  have hnb3 : 3 ≤ nb := by rw [hnb]; exact lctNodesBase_ge3 b
  have hfree_lt : b + LCT_HDR_FREE < nb - 1 := by
    rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega
  have hfree_ne_ptrs : ∀ y off, 1 ≤ y → y ≤ cap → off < NODE_STRIDE →
      nb + NODE_STRIDE * y + off ≠ b + LCT_HDR_FREE := fun y off hy1 _ _ => by
    have hmul : NODE_STRIDE ≤ NODE_STRIDE * y := Nat.le_mul_of_pos_right _ hy1
    rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE NODE_STRIDE at *; omega
  have hsafe_free : SafeMem mem₀' nb cap hp_caller (Function.update mem (b + LCT_HDR_FREE) nextFree) := by
    refine ⟨by rw [Function.update_of_ne (by omega : nb - 1 ≠ b + LCT_HDR_FREE)]; exact hsafe.1,
      ?_, ?_, ?_⟩
    · intro a ha
      dsimp only [mem₀']
      by_cases haf : a = b + LCT_HDR_FREE
      · subst haf; simp [Function.update_self]
      · simp only [Function.update_of_ne haf]
        exact hsafe.2.1 a ha
    · intro x hx1 hx2
      dsimp only [nodeField]
      rw [Function.update_of_ne (hfree_ne_ptrs x OFF_LEFT hx1 hx2 (by decide)),
        Function.update_of_ne (hfree_ne_ptrs x OFF_RIGHT hx1 hx2 (by decide)),
        Function.update_of_ne (hfree_ne_ptrs x OFF_PARENT hx1 hx2 (by decide))]
      exact hsafe.2.2.1 x hx1 hx2
    · intro x off hx1 hx2 hoff
      have hne_x := hfree_ne_ptrs x off hx1 hx2 (ptrOffs_lt_stride hoff)
      dsimp only [nodeField]
      rw [Function.update_of_ne hne_x]
      rcases hsafe.2.2.2 x off hx1 hx2 hoff with hp0 | hp_hi | ⟨y, off', hy1, hy2, hoff', hy_eq⟩
      · exact Or.inl hp0
      · exact Or.inr (Or.inl hp_hi)
      · refine Or.inr (Or.inr ⟨y, off', hy1, hy2, hoff', ?_⟩)
        dsimp only [mem₀', nodeField] at hy_eq ⊢
        simp only [Function.update_of_ne (hfree_ne_ptrs y off' hy1 hy2 (ptrOffs_lt_stride hoff'))]
        exact hy_eq
  have hsafe_ed : SafeMem mem₀' nb cap hp_caller
      (writeNodeOffs (Function.update mem (b + LCT_HDR_FREE) nextFree) nb ed
        (lctLinkOffPairs u v eid p_cf p_cb p_fl p_af p_ab)) := by
    apply writeNodeOffs_safeMem hnb3 harena_safe hed1 hed2 hsafe_free
    intro p hp
    have hlt := lctLinkOffPairs_lt_stride u v eid p_cf p_cb p_fl p_af p_ab p hp
    refine ⟨hlt, ?_, ?_⟩
    · intro hstr
      dsimp only [lctLinkOffPairs] at hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;>
        dsimp only at hstr ⊢
      · omega
      · exact hu_le
      · omega
      · exact hv_le
      all_goals exact absurd hstr (by decide)
    · intro hptr
      dsimp only [lctLinkOffPairs] at hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;>
        dsimp only at hptr ⊢
      · exact absurd hptr (by unfold ptrOffs; decide)
      · exact absurd hptr (by unfold ptrOffs; decide)
      · exact absurd hptr (by unfold ptrOffs; decide)
      · exact absurd hptr (by unfold ptrOffs; decide)
      · exact absurd hptr (by unfold ptrOffs; decide)
      · exact absurd hptr (by unfold ptrOffs; decide)
      · exact absurd hptr (by unfold ptrOffs; decide)
      · exact absurd hptr (by unfold ptrOffs; decide)
      · exact absurd hptr (by unfold ptrOffs; decide)
      · exact Or.inl rfl
      · exact absurd hptr (by unfold ptrOffs; decide)
      · exact absurd hptr (by unfold ptrOffs; decide)
      · exact absurd hptr (by unfold ptrOffs; decide)
      · exact absurd hptr (by unfold ptrOffs; decide)
      · exact Or.inr (Or.inl hp_cb)
      · exact Or.inr (Or.inl hp_cf)
      · exact Or.inr (Or.inl hp_fl)
      · exact Or.inr (Or.inl hp_ab)
      · exact Or.inr (Or.inl hp_af)
  exact SafeMem.update_field hsafe_ed hnb3 harena_safe (by omega) hu_le (by decide) (fun _ => hed2)
    (fun hc => absurd (by simpa [ptrOffs] using hc) (by decide))

private lemma listVcnt_congr {m₁ m₂ : ℕ → ℕ} {nb : ℕ} :
    ∀ {xs : List ℕ}, (∀ z ∈ xs, nodeField m₁ nb z OFF_ISV = nodeField m₂ nb z OFF_ISV) →
      listVcnt m₁ nb xs = listVcnt m₂ nb xs
  | [], _ => rfl
  | a :: tl, h => by
      simp only [listVcnt, h a List.mem_cons_self,
        listVcnt_congr (xs := tl) (fun z hz => h z (List.mem_cons_of_mem _ hz))]

/-- Builds `PullPre w h L mem_w nb cap ed .leaf (.node (u + 1) .leaf r_u) 0 (v + 1)` on
`mem_w = lctLinkWriteMem mem ...`. -/
theorem lctLink_pullPre {w h L b nb n u v eid p_cf p_cb p_fl p_af p_ab nextFree ed : ℕ}
    {r_u : AuxTree} {mem : ℕ → ℕ} {e : ForestEdge}
    (hnb : nb = lctNodesBase b)
    (h1 : 1 ≤ ed) (hed_le : ed ≤ lctCap n) (hu : u < n) (_hv : v < n)
    (hhp_lt : mem (nb - 1) < 2 ^ w)
    (harena_hp : nb + NODE_STRIDE * (lctCap n + 1) ≤ mem (nb - 1))
    (hed_w : eid < 2 ^ w) (hu_w : u < 2 ^ w) (hv_w : v < 2 ^ w)
    (hp_cf : nb + NODE_STRIDE * (lctCap n + 1) ≤ p_cf ∧ p_cf + L ≤ mem (nb - 1) ∧
      Valid mem p_cf h L ∧ intVal mem p_cf h L = e.cost)
    (hp_cb : nb + NODE_STRIDE * (lctCap n + 1) ≤ p_cb ∧ p_cb + L ≤ mem (nb - 1) ∧
      Valid mem p_cb h L ∧ intVal mem p_cb h L = wrap h L (-e.cost))
    (hp_fl : nb + NODE_STRIDE * (lctCap n + 1) ≤ p_fl ∧ p_fl + L ≤ mem (nb - 1) ∧ Valid mem p_fl h L)
    (hp_af : nb + NODE_STRIDE * (lctCap n + 1) ≤ p_af ∧ p_af + L ≤ mem (nb - 1) ∧ Valid mem p_af h L)
    (hp_ab : nb + NODE_STRIDE * (lctCap n + 1) ≤ p_ab ∧ p_ab + L ≤ mem (nb - 1) ∧ Valid mem p_ab h L)
    (hfit_cost : Fits h L e.cost)
    (htu_match : TreeMemMatch w h L mem nb (lctCap n) (.node (u + 1) .leaf r_u) 0 0)
    (hupp0 : nodeField mem nb (u + 1) OFF_PPAR = 0)
    (htu_nd : (AuxTree.node (u + 1) .leaf r_u).toList.Nodup)
    (hed_nin_tu : ed ∉ (AuxTree.node (u + 1) .leaf r_u).toList) :
    PullPre w h L (lctLinkWriteMem mem nb b u v eid p_cf p_cb p_fl p_af p_ab nextFree ed) nb
      (lctCap n) ed .leaf (.node (u + 1) .leaf r_u) 0 (v + 1) := by
  let mem_w := lctLinkWriteMem mem nb b u v eid p_cf p_cb p_fl p_af p_ab nextFree ed
  have hne : ed ≠ u + 1 := fun heq => hed_nin_tu (by rw [heq]; simp [AuxTree.toList])
  have hf := fun (off val : ℕ) (hp : (off, val) ∈ lctLinkOffPairs u v eid p_cf p_cb p_fl p_af p_ab) =>
    lctLinkWriteMem_nodeField_ed (mem := mem) (nb := nb) (b := b) (nextFree := nextFree) hne off val hp
  have hmem_hp : mem_w (nb - 1) = mem (nb - 1) := by
    have hnb_pos : 1 ≤ nb := by rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE; omega
    have hfree_ne : nb - 1 ≠ b + LCT_HDR_FREE := by
      rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega
    have hed_lt : nb - 1 < nb + NODE_STRIDE * ed := by
      have hmul : NODE_STRIDE ≤ NODE_STRIDE * ed := Nat.le_mul_of_pos_right _ h1
      unfold NODE_STRIDE at hmul; omega
    have hu_lt : nb - 1 ≠ nb + NODE_STRIDE * (u + 1) + OFF_PARENT := by
      have hmul : NODE_STRIDE ≤ NODE_STRIDE * (u + 1) := Nat.le_mul_of_pos_right _ (by omega)
      unfold NODE_STRIDE at hmul; omega
    exact lctLinkWriteMem_outside hfree_ne (Or.inl hed_lt) hu_lt
  have hheap : ∀ a, nb + NODE_STRIDE * (lctCap n + 1) ≤ a → a < mem (nb - 1) → mem_w a = mem a := by
    intro a ha1 _ha2
    have hfree_ne : a ≠ b + LCT_HDR_FREE := by
      have : b + LCT_HDR_FREE < nb + NODE_STRIDE * (lctCap n + 1) := by
        have hmul : NODE_STRIDE ≤ NODE_STRIDE * (lctCap n + 1) :=
          Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
        rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE NODE_STRIDE at *; omega
      omega
    have hed_hi : nb + NODE_STRIDE * ed + NODE_STRIDE ≤ a := by
      have : NODE_STRIDE * ed + NODE_STRIDE ≤ NODE_STRIDE * (lctCap n + 1) := by
        have := Nat.mul_le_mul_left NODE_STRIDE (by omega : ed + 1 ≤ lctCap n + 1)
        rwa [Nat.mul_add, Nat.mul_one] at this
      omega
    have hu_hi : a ≠ nb + NODE_STRIDE * (u + 1) + OFF_PARENT := by
      have : NODE_STRIDE * (u + 1) + OFF_PARENT < NODE_STRIDE * (lctCap n + 1) := by
        have h1' : u + 1 ≤ lctCap n := by unfold lctCap; omega
        have hmul := Nat.mul_le_mul_left NODE_STRIDE (by omega : (u + 1) + 1 ≤ lctCap n + 1)
        rw [Nat.mul_add, Nat.mul_one] at hmul
        have : OFF_PARENT < NODE_STRIDE := by decide
        omega
      omega
    exact lctLinkWriteMem_outside hfree_ne (Or.inr hed_hi) hu_hi
  have hval_congr : ∀ {ptr} (hlo : nb + NODE_STRIDE * (lctCap n + 1) ≤ ptr)
      (hhi : ptr + L ≤ mem (nb - 1)) (hv_old : Valid mem ptr h L),
      Valid mem_w ptr h L ∧ intVal mem_w ptr h L = intVal mem ptr h L := by
    intro ptr hlo hhi hv_old
    have hag : ∀ i < L, mem_w (ptr + i) = mem (ptr + i) := fun i hi =>
      hheap (ptr + i) (by omega) (by omega)
    refine ⟨fun i hi => by rw [hag i hi]; exact hv_old i hi, intVal_congr hag⟩
  rcases hval_congr hp_cf.1 hp_cf.2.1 hp_cf.2.2.1 with ⟨hcf_v, hcf_i⟩
  rcases hval_congr hp_cb.1 hp_cb.2.1 hp_cb.2.2.1 with ⟨hcb_v, hcb_i⟩
  rcases hval_congr hp_fl.1 hp_fl.2.1 hp_fl.2.2 with ⟨hfl_v, _⟩
  rcases hval_congr hp_af.1 hp_af.2.1 hp_af.2.2 with ⟨haf_v, _⟩
  rcases hval_congr hp_ab.1 hp_ab.2.1 hp_ab.2.2 with ⟨hab_v, _⟩
  have htu_w : TreeMemMatch w h L mem_w nb (lctCap n) (.node (u + 1) .leaf r_u) ed 0 := by
    refine treeMemMatch_reparent_root htu_match htu_nd
      (fun _ => lctLinkWriteMem_nodeField_u_parent)
      (fun _ => (lctLinkWriteMem_nodeField_other (z := u + 1) (off := OFF_PPAR) hnb (by omega)
        (by decide) hne.symm (fun _ => by decide)).trans hupp0)
      (fun z hz off hoff hroot =>
        lctLinkWriteMem_nodeField_other (z := z) (off := off) hnb (htu_match.nodup_perm_mem hz).1 hoff
          (fun heq => hed_nin_tu (heq ▸ hz))
          (fun heq => by simpa [AuxTree.rootId] using (hroot (by simpa [AuxTree.rootId] using heq)).1))
      (by rw [hmem_hp]) hheap
  have hbase_w : nb + NODE_STRIDE * (lctCap n + 1) < 2 ^ w := lt_of_le_of_lt harena_hp hhp_lt
  have hnum : ∀ {ptr} (hlo : nb + NODE_STRIDE * (lctCap n + 1) ≤ ptr)
      (hhi : ptr + L ≤ mem (nb - 1)) (hv' : Valid mem_w ptr h L),
      NumPtrOk mem_w (nb + NODE_STRIDE * (lctCap n + 1)) (mem_w (nb - 1)) h L ptr :=
    fun hlo hhi hv' => ⟨by
      have hnb_pos : 1 ≤ nb := by rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE; omega
      omega, hlo, by rw [hmem_hp]; exact hhi, hv'⟩
  have htu_ev : (AuxTree.node (u + 1) AuxTree.leaf r_u).evalInorder (revFlag mem_w nb) false =
      (AuxTree.node (u + 1) AuxTree.leaf r_u).evalInorder (revFlag mem nb) false := by
    apply AuxTree.evalInorder_agree
    intro z hz
    have hrev_z : nodeField mem_w nb z OFF_REV = nodeField mem nb z OFF_REV :=
      lctLinkWriteMem_nodeField_other (z := z) (off := OFF_REV) (ed := ed) hnb
        (htu_match.nodup_perm_mem hz).1 (by decide) (fun heq => hed_nin_tu (heq ▸ hz))
        (fun _ => by decide)
    simp only [revFlag, hrev_z]
  have hvc_lt : listVcnt mem_w nb
      (AuxTree.evalInorder (revFlag mem_w nb) .leaf false ++ [ed] ++
        AuxTree.evalInorder (revFlag mem_w nb) (.node (u + 1) .leaf r_u) false) < 2 ^ w := by
    have hcongr := listVcnt_congr (m₁ := mem_w) (m₂ := mem) (nb := nb)
      (xs := (AuxTree.node (u + 1) AuxTree.leaf r_u).evalInorder (revFlag mem nb) false) fun z hz =>
        have hzm : z ∈ (AuxTree.node (u + 1) AuxTree.leaf r_u).toList :=
          ((AuxTree.node (u + 1) AuxTree.leaf r_u).evalInorder_perm (revFlag mem nb) false).mem_iff.1 hz
        lctLinkWriteMem_nodeField_other (z := z) (off := OFF_ISV) hnb
          (htu_match.nodup_perm_mem hzm).1 (by decide)
          (fun heq => hed_nin_tu (heq ▸ hzm)) (fun _ => by decide)
    have hstep : listVcnt mem_w nb
        (AuxTree.evalInorder (revFlag mem_w nb) .leaf false ++ [ed] ++
          AuxTree.evalInorder (revFlag mem_w nb) (.node (u + 1) .leaf r_u) false) =
        nodeField mem_w nb ed OFF_ISV +
          listVcnt mem_w nb (AuxTree.evalInorder (revFlag mem_w nb) (.node (u + 1) .leaf r_u) false) := rfl
    rw [hstep, hf OFF_ISV 0 (by simp [lctLinkOffPairs]), Nat.zero_add, htu_ev, hcongr]
    exact htu_match.listVcnt_lt_pow hbase_w htu_nd
  refine
    { hx1 := h1
      hx2 := hed_le
      hL := hf OFF_LEFT 0 (by simp [lctLinkOffPairs])
      hR := hf OFF_RIGHT (u + 1) (by simp [lctLinkOffPairs])
      hP := hf OFF_PARENT 0 (by simp [lctLinkOffPairs])
      hPP := hf OFF_PPAR (v + 1) (by simp [lctLinkOffPairs])
      hrev0 := hf OFF_REV 0 (by simp [lctLinkOffPairs])
      hiv := by rw [hf OFF_ISV 0 (by simp [lctLinkOffPairs])]; decide
      hhe := by rw [hf OFF_HASE 1 (by simp [lctLinkOffPairs])]
      hsum := by
        rw [hf OFF_ISV 0 (by simp [lctLinkOffPairs]), hf OFF_HASE 1 (by simp [lctLinkOffPairs])]
      hdir := by rw [hf OFF_DIR 0 (by simp [lctLinkOffPairs])]; decide
      hht0 := hf OFF_HAS_TAG 0 (by simp [lctLinkOffPairs])
      htp0 := hf OFF_TAG_PTR 0 (by simp [lctLinkOffPairs])
      htn0 := hf OFF_TAG_NEG 0 (by simp [lctLinkOffPairs])
      heu := by rw [hf OFF_EU u (by simp [lctLinkOffPairs])]; exact hu_w
      hev := by rw [hf OFF_EV v (by simp [lctLinkOffPairs])]; exact hv_w
      heid := by rw [hf OFF_EID eid (by simp [lctLinkOffPairs])]; exact hed_w
      he1 := fun _ => ?_
      he0 := fun h0 => by rw [hf OFF_HASE 1 (by simp [lctLinkOffPairs])] at h0; omega
      hl := trivial
      hr := htu_w
      hvcnt_lt := hvc_lt }
  rw [hf OFF_FLOW_PTR p_fl (by simp [lctLinkOffPairs]),
    hf OFF_AF_PTR p_ab (by simp [lctLinkOffPairs]),
    hf OFF_AB_PTR p_af (by simp [lctLinkOffPairs]),
    hf OFF_COST_FWD p_cb (by simp [lctLinkOffPairs]),
    hf OFF_COST_BWD p_cf (by simp [lctLinkOffPairs])]
  refine ⟨hnum hp_fl.1 hp_fl.2.1 hfl_v, hnum hp_ab.1 hp_ab.2.1 hab_v,
    hnum hp_af.1 hp_af.2.1 haf_v, hnum hp_cb.1 hp_cb.2.1 hcb_v, hnum hp_cf.1 hp_cf.2.1 hcf_v, ?_⟩
  rw [hcf_i, hp_cf.2.2.2, hcb_i, hp_cb.2.2.2, wrap_neg_wrap, neg_neg, wrap_of_fits hfit_cost]

end LinkWriteMemAndPullPre

end MinCostFlow.LinkCut.Prog
