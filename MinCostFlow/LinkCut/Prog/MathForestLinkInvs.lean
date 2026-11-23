module

public import MinCostFlow.LinkCut.Prog.MathForestLinkAcyclic

/-!
# Post-Pull Invariants for `link`

Proves component-disjointness parent properties (`lctLink_par_notin_free`, `lctLink_v_no_u`,
`lctLink_iterParent_no_u`) and full preservation of `LctExposeInvs` together with the exact
`lctAuxParent` update formula after splicing and pulling the new edge node (`link_invs_after_pull`).
The amortized `lctPhi` bound lives in `MathForestLinkPhi.lean`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section LinkInvariants

private lemma link_fits_of_isFixedFit {h L P : ℕ} {q : ℚ}
    (hf : IsFixedFit h L P q) : ∀ {k : ℤ}, ((k : ℚ) / (2 : ℚ) ^ P = q) → Fits h L k := by
  intro k hq
  rcases hf with ⟨k', hk', hq'⟩
  have h2P : (2 : ℚ) ^ P ≠ 0 := by positivity
  have hkq : (k : ℚ) = (k' : ℚ) := by
    have := congrArg (· * (2 : ℚ) ^ P) (hq.trans hq')
    simpa [div_mul_cancel₀ _ h2P] using this
  exact Int.cast_inj.1 hkq ▸ hk'

private lemma findSome_lct_cons_pos {mem : ℕ → ℕ} {nb z : ℕ} {s : AuxTree} {ss : List AuxTree}
    (hz : z ∈ s.evalInorder (revFlag mem nb) false) :
    (s :: ss).findSome? (fun t =>
      let seq := t.evalInorder (revFlag mem nb) false
      if z ∈ seq then some (listParentFrom (nodeField mem nb t.rootId OFF_PPAR) seq z) else none) =
      some (listParentFrom (nodeField mem nb s.rootId OFF_PPAR)
        (s.evalInorder (revFlag mem nb) false) z) := by
  simp [List.findSome?, hz]

private lemma findSome_lct_cons_neg {mem : ℕ → ℕ} {nb z : ℕ} {s : AuxTree} {ss : List AuxTree}
    (hz : z ∉ s.evalInorder (revFlag mem nb) false) :
    (s :: ss).findSome? (fun t =>
      let seq := t.evalInorder (revFlag mem nb) false
      if z ∈ seq then some (listParentFrom (nodeField mem nb t.rootId OFF_PPAR) seq z) else none) =
      ss.findSome? (fun t =>
        let seq := t.evalInorder (revFlag mem nb) false
        if z ∈ seq then some (listParentFrom (nodeField mem nb t.rootId OFF_PPAR) seq z) else none) := by
  simp [List.findSome?, hz]

/-- Post-pull `LctExposeInvs` and exact `lctAuxParent` update law for `link`. -/
theorem link_invs_after_pull {w h L P b u v : ℕ} {F : MathForest}
    {e : ForestEdge} {x₃ : LctConc} {r_u l_v : AuxTree} {rest_fin : List AuxTree}
    {free' : List ℕ} {edgeMap : List (ℕ × ForestEdge)}
    {mem₃ mem_w mem_p : ℕ → ℕ} {ed nextFree p_cf p_cb p_fl p_af p_ab : ℕ}
    (hFn : (F.link e).n = F.n)
    (hu_eq : e.u = u) (hv_eq : e.v = v)
    (hu : u < F.n) (hv : v < F.n) (hdisc : ¬ F.SameComp u v) (hfit_e : EdgeFits h L P e)
    (hvalid_F : F.Valid)
    (hedges_snd : (edgeMap.map Prod.snd).Perm F.edges)
    (hslots_perm : (edgeMap.map Prod.fst ++ (ed :: free')).Perm ((List.range F.n).map (F.n + 1 + ·)))
    (hrep₃ : LctMemRep w h L P b F x₃ mem₃)
    (hi₃ : LctExposeInvs w h L P b F.n (ed :: free') edgeMap
      (AuxTree.node (u + 1) .leaf r_u :: AuxTree.node (v + 1) l_v .leaf ::
        AuxTree.node ed .leaf .leaf :: rest_fin) mem₃)
    (hrev_u3 : nodeField mem₃ (lctNodesBase b) (u + 1) OFF_REV = 0)
    (hpar_u3 : lctAuxParent mem₃ (lctNodesBase b) (lctCap F.n) (u + 1) = 0)
    (hmem_w_eq : mem_w = lctLinkWriteMem mem₃ (lctNodesBase b) b u v e.eid p_cf p_cb p_fl p_af p_ab nextFree ed)
    (harena_cf : lctNodesBase b + NODE_STRIDE * (lctCap F.n + 1) ≤ p_cf ∧ p_cf + L ≤ mem_w (lctNodesBase b - 1))
    (harena_cb : lctNodesBase b + NODE_STRIDE * (lctCap F.n + 1) ≤ p_cb ∧ p_cb + L ≤ mem_w (lctNodesBase b - 1))
    (harena_fl : lctNodesBase b + NODE_STRIDE * (lctCap F.n + 1) ≤ p_fl ∧ p_fl + L ≤ mem_w (lctNodesBase b - 1))
    (harena_af : lctNodesBase b + NODE_STRIDE * (lctCap F.n + 1) ≤ p_af ∧ p_af + L ≤ mem_w (lctNodesBase b - 1))
    (harena_ab : lctNodesBase b + NODE_STRIDE * (lctCap F.n + 1) ≤ p_ab ∧ p_ab + L ≤ mem_w (lctNodesBase b - 1))
    (hp_cf_val : intVal mem_w p_cf h L = e.cost)
    (hp_fl_val : ((intVal mem_w p_fl h L : ℤ) : ℚ) / (2 : ℚ) ^ P = e.flow)
    (hp_af_val : ((intVal mem_w p_af h L : ℤ) : ℚ) / (2 : ℚ) ^ P = e.availFwd)
    (hp_ab_val : ((intVal mem_w p_ab h L : ℤ) : ℚ) / (2 : ℚ) ^ P = e.availBwd)
    (hp_lt_w : mem_p (lctNodesBase b - 1) < 2 ^ w)
    (htm_ed : TreeMemMatch w h L mem_p (lctNodesBase b) (lctCap F.n)
      (.node ed .leaf (.node (u + 1) .leaf r_u)) 0 (v + 1))
    (hout_p : ∀ addr, addr ≠ lctNodesBase b - 1 →
      (addr < lctNodesBase b + NODE_STRIDE * ed ∨
        lctNodesBase b + NODE_STRIDE * ed + NODE_STRIDE ≤ addr) →
      addr < mem_w (lctNodesBase b - 1) → mem_p addr = mem_w addr)
    (hnonAgg_ed : ∀ off < NODE_STRIDE,
      off ≠ OFF_VCNT → off ≠ OFF_CSUM_FWD → off ≠ OFF_CSUM_BWD →
      off ≠ OFF_MIN1_HAS → off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN1_FIRST → off ≠ OFF_MIN1_LAST →
      off ≠ OFF_MIN2_HAS → off ≠ OFF_MIN2_VAL → off ≠ OFF_MIN2_FIRST → off ≠ OFF_MIN2_LAST →
      nodeField mem_p (lctNodesBase b) ed off = nodeField mem_w (lctNodesBase b) ed off)
    (hfr_p : LctFrame (lctNodesBase b + NODE_STRIDE)
      (lctNodesBase b + NODE_STRIDE * (lctCap F.n + 1)) (lctNodesBase b - 1) mem_w mem_p)
    (hhdr_free : mem₃ (b + LCT_HDR_FREE) = ed)
    (hnext_free : nodeField mem₃ (lctNodesBase b) ed OFF_EU = nextFree) :
    let nb := lctNodesBase b
    let cap := lctCap F.n
    let t_u := AuxTree.node (u + 1) .leaf r_u
    let t_v := AuxTree.node (v + 1) l_v .leaf
    let t_ed := AuxTree.node ed .leaf t_u
    let trees_fin := t_ed :: t_v :: rest_fin
    LctExposeInvs w h L P b (F.link e).n free' ((ed, e) :: edgeMap) trees_fin mem_p ∧
    (∀ z, lctAuxParent mem_p nb cap z =
      if z = ed then v + 1 else if z = u + 1 then ed else lctAuxParent mem₃ nb cap z) ∧
    (t_v.evalInorder (revFlag mem_p nb) false = t_v.evalInorder (revFlag mem₃ nb) false) ∧
    (∀ s ∈ rest_fin,
      nodeField mem_p nb s.rootId OFF_PPAR = nodeField mem₃ nb s.rootId OFF_PPAR ∧
      s.evalInorder (revFlag mem_p nb) false = s.evalInorder (revFlag mem₃ nb) false) ∧
    (t_u.evalInorder (revFlag mem_p nb) false = t_u.evalInorder (revFlag mem₃ nb) false) ∧
    nodeField mem_p nb ed OFF_PPAR = v + 1 := by
  intro nb cap t_u t_v t_ed trees_fin
  have hnb : nb = lctNodesBase b := rfl
  have hnb_ge3 : 3 ≤ nb := by rw [hnb]; exact lctNodesBase_ge3 b
  have hstr : NODE_STRIDE = 30 := rfl
  have hed_free : ed ∈ (ed :: free') := by simp
  have hed_bd := hi₃.freeNodeOk ed hed_free
  have hed1 : 1 ≤ ed := by omega
  have hed2 : ed ≤ cap := hed_bd.2.1
  have hne_ed_u : ed ≠ u + 1 := by omega
  have hnd_all3 : ((t_u :: t_v :: .node ed .leaf .leaf :: rest_fin).flatMap AuxTree.toList).Nodup :=
    hi₃.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  have hfree_nd : (ed :: free').Nodup := by
    have hfull_nd : (edgeMap.map Prod.fst ++ (ed :: free')).Nodup :=
      hslots_perm.nodup_iff.2 ((List.nodup_range).map (fun _ _ h => by omega))
    exact (List.nodup_append.1 hfull_nd).2.1
  have hedge_lt : ∀ p ∈ edgeMap, p.2.u < F.n ∧ p.2.v < F.n := fun p hp => by
    have he := hvalid_F.1 p.2 (hedges_snd.mem_iff.1 (List.mem_map.2 ⟨p, hp, rfl⟩))
    exact ⟨he.1, he.2.1⟩
  have hmem_w_hp : mem_w (nb - 1) = mem₃ (nb - 1) := by
    subst hmem_w_eq
    have hfree_ne : nb - 1 ≠ b + LCT_HDR_FREE := by
      rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega
    have hed_lt_a : nb - 1 < nb + NODE_STRIDE * ed := by
      have hmul : NODE_STRIDE ≤ NODE_STRIDE * ed := Nat.le_mul_of_pos_right _ hed1
      omega
    have hu_lt : nb - 1 ≠ nb + NODE_STRIDE * (u + 1) + OFF_PARENT := by
      have hmul : NODE_STRIDE ≤ NODE_STRIDE * (u + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    exact lctLinkWriteMem_outside hfree_ne (Or.inl hed_lt_a) hu_lt
  have hed_addr_out : ∀ z off, 1 ≤ z → z ≤ cap → off < NODE_STRIDE → z ≠ ed →
      (nb + NODE_STRIDE * z + off < nb + NODE_STRIDE * ed ∨
       nb + NODE_STRIDE * ed + NODE_STRIDE ≤ nb + NODE_STRIDE * z + off) := by
    intro z off _ _ hoff hzne
    rcases Nat.lt_trichotomy z ed with hlt | rfl | hgt
    · left
      have : NODE_STRIDE * (z + 1) ≤ NODE_STRIDE * ed := Nat.mul_le_mul_left _ hlt
      rw [Nat.mul_add, Nat.mul_one] at this; omega
    · exact absurd rfl hzne
    · right
      have : NODE_STRIDE * (ed + 1) ≤ NODE_STRIDE * z := Nat.mul_le_mul_left _ hgt
      rw [Nat.mul_add, Nat.mul_one] at this; omega
  have haddr_lt_hp3 : ∀ z off, z ≤ cap → off < NODE_STRIDE →
      nb + NODE_STRIDE * z + off < mem₃ (nb - 1) := by
    intro z off hz2 hoff
    have h1 : nb + NODE_STRIDE * z + off < nb + NODE_STRIDE * (cap + 1) := by
      have : NODE_STRIDE * (z + 1) ≤ NODE_STRIDE * (cap + 1) := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_add, Nat.mul_one] at this; omega
    exact lt_of_lt_of_le h1 hi₃.sf.2.2.2.1
  have hfield_p_w_non_ed : ∀ z off, 1 ≤ z → z ≤ cap → off < NODE_STRIDE → z ≠ ed →
      nodeField mem_p nb z off = nodeField mem_w nb z off := by
    intro z off hz1 hz2 hoff hzne
    have h1 : nb + NODE_STRIDE * z + off ≠ nb - 1 := by
      have hmul : NODE_STRIDE ≤ NODE_STRIDE * z := Nat.le_mul_of_pos_right _ hz1
      omega
    exact hout_p _ h1 (hed_addr_out z off hz1 hz2 hoff hzne)
      (by rw [hmem_w_hp]; exact haddr_lt_hp3 z off hz2 hoff)
  have hfield_p_3_other : ∀ z off, 1 ≤ z → z ≤ cap → off < NODE_STRIDE → z ≠ ed →
      (z = u + 1 → off ≠ OFF_PARENT) → nodeField mem_p nb z off = nodeField mem₃ nb z off := by
    intro z off hz1 hz2 hoff hzne hneu
    rw [hfield_p_w_non_ed z off hz1 hz2 hoff hzne, hmem_w_eq]
    exact lctLinkWriteMem_nodeField_other hnb hz1 hoff hzne hneu
  have hed_fields : ∀ off val, (off, val) ∈ lctLinkOffPairs u v e.eid p_cf p_cb p_fl p_af p_ab →
      off ≠ OFF_VCNT → off ≠ OFF_CSUM_FWD → off ≠ OFF_CSUM_BWD →
      off ≠ OFF_MIN1_HAS → off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN1_FIRST → off ≠ OFF_MIN1_LAST →
      off ≠ OFF_MIN2_HAS → off ≠ OFF_MIN2_VAL → off ≠ OFF_MIN2_FIRST → off ≠ OFF_MIN2_LAST →
      nodeField mem_p nb ed off = val := by
    intro off val hp h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    have hlt := lctLinkOffPairs_lt_stride u v e.eid p_cf p_cb p_fl p_af p_ab (off, val) hp
    rw [hnonAgg_ed off hlt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11, hmem_w_eq]
    exact lctLinkWriteMem_nodeField_ed hne_ed_u off val hp
  have hheap_p_w : ∀ a, nb + NODE_STRIDE * (cap + 1) ≤ a → a < mem_w (nb - 1) → mem_p a = mem_w a := by
    intro a ha1 ha2
    have hne1 : a ≠ nb - 1 := by
      have : nb - 1 < nb + NODE_STRIDE * (cap + 1) := by
        have hmul : NODE_STRIDE ≤ NODE_STRIDE * (cap + 1) :=
          Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
        omega
      omega
    have hed_hi : nb + NODE_STRIDE * ed + NODE_STRIDE ≤ a := by
      have : NODE_STRIDE * (ed + 1) ≤ NODE_STRIDE * (cap + 1) := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_add, Nat.mul_one] at this; omega
    exact hout_p a hne1 (Or.inr hed_hi) ha2
  have hheap_p_3 : ∀ a, nb + NODE_STRIDE * (cap + 1) ≤ a → a < mem₃ (nb - 1) → mem_p a = mem₃ a := by
    intro a ha1 ha2
    rw [hheap_p_w a ha1 (by rw [hmem_w_hp]; exact ha2), hmem_w_eq]
    have hfree_ne : a ≠ b + LCT_HDR_FREE := by
      have : b + LCT_HDR_FREE < nb + NODE_STRIDE * (cap + 1) := by
        have hmul : NODE_STRIDE ≤ NODE_STRIDE * (cap + 1) :=
          Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
        rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega
      omega
    have hed_hi : nb + NODE_STRIDE * ed + NODE_STRIDE ≤ a := by
      have : NODE_STRIDE * (ed + 1) ≤ NODE_STRIDE * (cap + 1) := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_add, Nat.mul_one] at this; omega
    have hu_hi : a ≠ nb + NODE_STRIDE * (u + 1) + OFF_PARENT := by
      have h1' : u + 1 ≤ cap := by unfold cap lctCap; omega
      have hmul := Nat.mul_le_mul_left NODE_STRIDE (by omega : (u + 1) + 1 ≤ cap + 1)
      rw [Nat.mul_add, Nat.mul_one] at hmul
      have : OFF_PARENT < NODE_STRIDE := by decide
      omega
    exact lctLinkWriteMem_outside hfree_ne (Or.inr hed_hi) hu_hi
  have hhdr_w : mem_w (b + LCT_HDR_N) = F.n ∧ mem_w (b + LCT_HDR_CAP) = cap ∧
      mem_w (b + LCT_HDR_FREE) = nextFree ∧ mem_w (b + LCT_HDR_L) = L ∧
      mem_w (b + LCT_HDR_P) = P := by
    have hne_out : ∀ off, off = LCT_HDR_N ∨ off = LCT_HDR_CAP ∨ off = LCT_HDR_L ∨ off = LCT_HDR_P →
        mem_w (b + off) = mem₃ (b + off) := by
      intro off hoff
      rw [hmem_w_eq]
      apply lctLinkWriteMem_outside
      · rcases hoff with rfl | rfl | rfl | rfl <;>
          (dsimp only [LCT_HDR_N, LCT_HDR_CAP, LCT_HDR_L, LCT_HDR_P, LCT_HDR_FREE]; omega)
      · left
        have hmul : NODE_STRIDE ≤ NODE_STRIDE * ed := Nat.le_mul_of_pos_right _ hed1
        have : b + off < nb := by
          rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE
          rcases hoff with rfl | rfl | rfl | rfl <;>
            (dsimp only [LCT_HDR_N, LCT_HDR_CAP, LCT_HDR_L, LCT_HDR_P]; omega)
        omega
      · have hmul : NODE_STRIDE ≤ NODE_STRIDE * (u + 1) := Nat.le_mul_of_pos_right _ (by omega)
        have : b + off < nb := by
          rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE
          rcases hoff with rfl | rfl | rfl | rfl <;>
            (dsimp only [LCT_HDR_N, LCT_HDR_CAP, LCT_HDR_L, LCT_HDR_P]; omega)
        omega
    refine ⟨(hne_out _ (Or.inl rfl)).trans hi₃.hdrN,
      (hne_out _ (Or.inr (Or.inl rfl))).trans hi₃.hdrCap,
      ?_, (hne_out _ (Or.inr (Or.inr (Or.inl rfl)))).trans hi₃.hdrL,
      (hne_out _ (Or.inr (Or.inr (Or.inr rfl)))).trans hi₃.hdrP⟩
    rw [hmem_w_eq]
    exact lctLinkWriteMem_hdr_free hnb hed1 (by omega)
  have hhdr_p := lctFrame_hdr_eq hfr_p
  have hhdrN_p : mem_p (b + LCT_HDR_N) = (F.link e).n := hFn ▸ hhdr_p.1.trans hhdr_w.1
  have hhdrCap_p : mem_p (b + LCT_HDR_CAP) = lctCap (F.link e).n := hFn ▸ hhdr_p.2.1.trans hhdr_w.2.1
  have hhdrFree_p : mem_p (b + LCT_HDR_FREE) = nextFree := hhdr_p.2.2.1.trans hhdr_w.2.2.1
  have hhdrL_p : mem_p (b + LCT_HDR_L) = L := hhdr_p.2.2.2.1.trans hhdr_w.2.2.2.1
  have hhdrP_p : mem_p (b + LCT_HDR_P) = P := hhdr_p.2.2.2.2.trans hhdr_w.2.2.2.2
  have hslot0_p : SlotZeroOk mem_p nb := by
    intro off hoff
    have hne_hp0 : nb + off ≠ nb - 1 := by omega
    have heq_pw : mem_p (nb + off) = mem_w (nb + off) := by
      have hlt_w : nb + off < mem_w (nb - 1) := by
        have hlt_ar : nb + NODE_STRIDE ≤ nb + NODE_STRIDE * (cap + 1) :=
          Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) nb
        have h3 : nb + NODE_STRIDE * (cap + 1) ≤ mem₃ (nb - 1) := hi₃.sf.2.2.2.1
        rw [hmem_w_hp]
        omega
      have hed_lo : nb + off < nb + NODE_STRIDE * ed := by
        have hmul : NODE_STRIDE ≤ NODE_STRIDE * ed := Nat.le_mul_of_pos_right _ hed1
        omega
      exact hout_p _ hne_hp0 (Or.inl hed_lo) hlt_w
    have heq_w3 : mem_w (nb + off) = mem₃ (nb + off) := by
      rw [hmem_w_eq]
      apply lctLinkWriteMem_outside
      · rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega
      · left; have hmul : NODE_STRIDE ≤ NODE_STRIDE * ed := Nat.le_mul_of_pos_right _ hed1; omega
      · have hmul : NODE_STRIDE ≤ NODE_STRIDE * (u + 1) := Nat.le_mul_of_pos_right _ (by omega); omega
    rw [heq_pw, heq_w3]
    exact hi₃.sf.2.2.2.2.2.2.2.1 off hoff
  have hdisj_other : ∀ {s : AuxTree}, s ∈ t_v :: rest_fin → ed ∉ s.toList ∧ u + 1 ∉ s.toList := by
    intro s hs
    have h1 := hnd_all3
    rw [List.flatMap_cons, List.nodup_append, List.flatMap_cons, List.nodup_append,
      List.flatMap_cons, List.nodup_append] at h1
    rcases List.mem_cons.1 hs with rfl | hsr
    · constructor
      · intro hm
        exact h1.2.1.2.2 ed hm ed (by simp [AuxTree.toList]) rfl
      · intro hm
        exact h1.2.2 (u + 1) (by simp [t_u, AuxTree.toList]) (u + 1) (by simp [hm]) rfl
    · constructor
      · intro hm
        exact h1.2.1.2.1.2.2 ed (by simp [AuxTree.toList]) ed (List.mem_flatMap.2 ⟨s, hsr, hm⟩) rfl
      · intro hm
        exact h1.2.2 (u + 1) (by simp [t_u, AuxTree.toList]) (u + 1)
          (by simp [List.mem_flatMap]; exact Or.inr (Or.inr ⟨s, hsr, hm⟩)) rfl
  have hother_agree : ∀ {s : AuxTree}, s ∈ t_v :: rest_fin →
      nodeField mem_p nb s.rootId OFF_PPAR = nodeField mem₃ nb s.rootId OFF_PPAR ∧
      s.evalInorder (revFlag mem_p nb) false = s.evalInorder (revFlag mem₃ nb) false ∧
      TreeMemMatch w h L mem_p nb cap s 0 (nodeField mem_p nb s.rootId OFF_PPAR) ∧
      evalMemSteps mem_p nb h L s false 0 = evalMemSteps mem₃ nb h L s false 0 := by
    intro s hs
    have hs_in3 : s ∈ t_u :: t_v :: .node ed .leaf .leaf :: rest_fin := by
      rcases List.mem_cons.1 hs with rfl | hsr
      · simp
      · simp [hsr]
    have hs_tok := (hi₃.sf.trees_ok s hs_in3).2.2
    have hs_nd := list_nodup_of_flatMap_nodup hnd_all3 hs_in3
    have hds := hdisj_other hs
    have hf_s : ∀ z ∈ s.toList, ∀ off < NODE_STRIDE, nodeField mem_p nb z off = nodeField mem₃ nb z off :=
      fun z hz off hoff =>
        hfield_p_3_other z off (hs_tok.nodup_perm_mem hz).1 (hs_tok.nodup_perm_mem hz).2 hoff
          (fun heq => hds.1 (heq ▸ hz)) (fun heq => False.elim (hds.2 (heq ▸ hz)))
    have hpp_s : nodeField mem_p nb s.rootId OFF_PPAR = nodeField mem₃ nb s.rootId OFF_PPAR :=
      hf_s s.rootId (AuxTree.rootId_mem_toList (hi₃.sf.trees_ok s hs_in3).1) OFF_PPAR (by decide)
    have hpar_s : s ≠ .leaf → nodeField mem_p nb s.rootId OFF_PARENT = 0 := fun hne => by
      rw [hf_s s.rootId (AuxTree.rootId_mem_toList hne) OFF_PARENT (by decide)]
      cases hs_eq : s with
      | leaf => exact absurd hs_eq hne
      | node rid sl sr =>
          have htm := hs_tok
          rw [hs_eq] at htm
          exact htm.parent_eq
    have htm_s : TreeMemMatch w h L mem_p nb cap s 0 (nodeField mem_p nb s.rootId OFF_PPAR) := by
      rw [hpp_s]
      exact treeMemMatch_reparent_root hs_tok hs_nd hpar_s (fun _ => hpp_s)
        (fun z hz off hoff _ => hf_s z hz off hoff)
        (by dsimp only [nb]; rw [← hmem_w_hp]; exact hfr_p.2.2.1) hheap_p_3
    have hev_s : s.evalInorder (revFlag mem_p nb) false = s.evalInorder (revFlag mem₃ nb) false := by
      apply AuxTree.evalInorder_agree
      intro z hz
      simp only [revFlag, hf_s z hz OFF_REV (by decide)]
    have hst_s : evalMemSteps mem_p nb h L s false 0 = evalMemSteps mem₃ nb h L s false 0 :=
      evalMemSteps_agree_of_nonStruct hs_tok hs_nd (fun z hz off hoff _ => hf_s z hz off hoff)
        hheap_p_3 false 0
    exact ⟨hpp_s, hev_s, htm_s, hst_s⟩
  have htu_tok := (hi₃.sf.trees_ok t_u (by simp [t_u])).2.2
  have htu_nd := list_nodup_of_flatMap_nodup (t := t_u) hnd_all3 (by simp [t_u])
  have hed_nin_tu : ed ∉ t_u.toList := fun hm => by
    have h1 := hnd_all3
    rw [List.flatMap_cons, List.nodup_append, List.flatMap_cons, List.nodup_append] at h1
    exact h1.2.2 ed hm ed (by simp [AuxTree.toList]) rfl
  have hf_tu : ∀ z ∈ t_u.toList, ∀ off < NODE_STRIDE,
      (z = t_u.rootId → off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR) →
      nodeField mem_p nb z off = nodeField mem₃ nb z off := fun z hz off hoff hroot =>
    hfield_p_3_other z off (htu_tok.nodup_perm_mem hz).1 (htu_tok.nodup_perm_mem hz).2 hoff
      (fun heq => hed_nin_tu (heq ▸ hz))
      (fun heq => (hroot (by simpa [t_u, AuxTree.rootId] using heq)).1)
  have htu_ev : t_u.evalInorder (revFlag mem_p nb) false = t_u.evalInorder (revFlag mem₃ nb) false := by
    apply AuxTree.evalInorder_agree
    intro z hz
    simp only [revFlag, hf_tu z hz OFF_REV (by decide) (fun _ => ⟨by decide, by decide⟩)]
  have htu_steps : evalMemSteps mem_p nb h L t_u false 0 = evalMemSteps mem₃ nb h L t_u false 0 :=
    evalMemSteps_agree_of_nonStruct htu_tok htu_nd hf_tu hheap_p_3 false 0
  have hed_rev_p : nodeField mem_p nb ed OFF_REV = 0 :=
    hed_fields OFF_REV 0 (by simp [lctLinkOffPairs]) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hed_ht_p : nodeField mem_p nb ed OFF_HAS_TAG = 0 :=
    hed_fields OFF_HAS_TAG 0 (by simp [lctLinkOffPairs]) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hpp_ed_p : nodeField mem_p nb ed OFF_PPAR = v + 1 :=
    hed_fields OFF_PPAR (v + 1) (by simp [lctLinkOffPairs]) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hed_ev_p : t_ed.evalInorder (revFlag mem_p nb) false =
      ed :: t_u.evalInorder (revFlag mem₃ nb) false := by
    have hrf : revFlag mem_p nb ed = false := by simp [revFlag, nb, hed_rev_p]
    simp only [t_ed, AuxTree.evalInorder, hrf, List.nil_append, List.singleton_append, htu_ev]
  have htu_ev_3 : t_u.evalInorder (revFlag mem₃ nb) false =
      (u + 1) :: r_u.evalInorder (revFlag mem₃ nb) false := by
    have hrf : revFlag mem₃ nb (u + 1) = false := by simp [revFlag, nb, hrev_u3]
    simp only [t_u, AuxTree.evalInorder, hrf, List.nil_append, List.singleton_append]
  have hsf_p : SplayForestOk w h L mem_p nb (lctCap (F.link e).n) trees_fin := by
    rw [hFn]
    have hL_p3 : mem_p (nb - 3) = L := by
      have : nb - 3 = b + LCT_HDR_L := by
        rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_L; omega
      rw [this]; exact hhdrL_p
    have hperm_fin : (trees_fin.flatMap AuxTree.toList).Perm ((List.range cap).map (· + 1)) := by
      have hp1 : (t_ed.toList).Perm (t_u.toList ++ [ed]) := by
        change (ed :: t_u.toList).Perm (t_u.toList ++ [ed])
        exact List.perm_append_singleton ed t_u.toList |>.symm
      have hp_base : (t_u :: t_v :: .node ed .leaf .leaf :: rest_fin).flatMap AuxTree.toList =
          t_u.toList ++ t_v.toList ++ [ed] ++ rest_fin.flatMap AuxTree.toList := by
        simp [AuxTree.toList, List.append_assoc]
      have hp_fin : trees_fin.flatMap AuxTree.toList =
          t_ed.toList ++ t_v.toList ++ rest_fin.flatMap AuxTree.toList := by
        simp [trees_fin, List.append_assoc]
      have hp_mid : (trees_fin.flatMap AuxTree.toList).Perm
          ((t_u :: t_v :: .node ed .leaf .leaf :: rest_fin).flatMap AuxTree.toList) := by
        rw [hp_fin, hp_base]
        have hperm1 := hp1.append_right t_v.toList
        have hperm2 : (t_u.toList ++ [ed] ++ t_v.toList).Perm (t_u.toList ++ t_v.toList ++ [ed]) := by
          rw [List.append_assoc, List.append_assoc]
          exact List.Perm.append_left t_u.toList List.perm_append_comm
        simpa [List.append_assoc] using (hperm1.trans hperm2).append_right (rest_fin.flatMap AuxTree.toList)
      exact hp_mid.trans hi₃.sf.perm
    have htok_fin : ∀ s ∈ trees_fin, s ≠ .leaf ∧ nodeField mem_p nb s.rootId OFF_PPAR < 2 ^ w ∧
        TreeMemMatch w h L mem_p nb cap s 0 (nodeField mem_p nb s.rootId OFF_PPAR) := by
      intro s hs
      simp only [trees_fin, List.mem_cons] at hs
      rcases hs with rfl | hsr
      · have hv1_w : v + 1 < 2 ^ w := by
          have : v + 1 ≤ cap := by unfold cap lctCap; omega
          have h1 : v + 1 < nb + NODE_STRIDE * (cap + 1) := by
            have : cap + 1 ≤ NODE_STRIDE * (cap + 1) :=
              Nat.le_mul_of_pos_left _ (by unfold NODE_STRIDE; omega)
            rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE; omega
          exact lt_of_lt_of_le (lt_of_lt_of_le h1 (le_trans hfr_p.2.1 hfr_p.2.2.1)) (le_of_lt hp_lt_w)
        refine ⟨by simp, by dsimp [t_ed, AuxTree.rootId]; rw [hpp_ed_p]; exact hv1_w, ?_⟩
        simpa [t_ed, AuxTree.rootId, hpp_ed_p] using htm_ed
      · have hsr' : s ∈ t_v :: rest_fin := List.mem_cons.2 hsr
        have hs_in3 : s ∈ t_u :: t_v :: .node ed .leaf .leaf :: rest_fin := by
          rcases hsr with rfl | hsr''
          · simp [t_v]
          · simp [hsr'']
        have htok3 := hi₃.sf.trees_ok s hs_in3
        have ho := hother_agree hsr'
        exact ⟨htok3.1, by rw [ho.1]; exact htok3.2.1, ho.2.2.1⟩
    exact ⟨hi₃.sf.1, hi₃.sf.2.1, hi₃.sf.2.2.1, le_trans hfr_p.2.1 hfr_p.2.2.1, hL_p3, hp_lt_w,
      hfr_p.2.2.2.2.1, hslot0_p, hperm_fin, htok_fin⟩
  have hpp_p_le : ∀ s ∈ trees_fin, nodeField mem_p nb s.rootId OFF_PPAR ≤ cap := by
    intro s hs
    simp only [trees_fin, List.mem_cons] at hs
    rcases hs with rfl | hsr
    · simp only [t_ed, AuxTree.rootId]; rw [hpp_ed_p]; unfold cap lctCap; omega
    · have hsr' : s ∈ t_v :: rest_fin := List.mem_cons.2 hsr
      rw [(hother_agree hsr').1]
      exact hi₃.ppar_le_cap s (by
        rcases hsr with rfl | hsr''
        · simp [t_v]
        · simp [hsr''])
  have hpar_eq : ∀ z, lctAuxParent mem_p nb cap z =
      if z = ed then v + 1 else if z = u + 1 then ed else lctAuxParent mem₃ nb cap z := by
    intro z
    have hsf_p' : SplayForestOk w h L mem_p nb cap trees_fin := by simpa [hFn] using hsf_p
    rw [lctAuxParent_mem_iff_of_trees hsf_p' hpp_p_le z,
      lctAuxParent_mem_iff_of_trees hi₃.sf hi₃.ppar_le_cap z]
    have hrest_eq :
        rest_fin.findSome? (fun s =>
          let seq := s.evalInorder (revFlag mem_p nb) false
          if z ∈ seq then some (listParentFrom (nodeField mem_p nb s.rootId OFF_PPAR) seq z) else none) =
        rest_fin.findSome? (fun s =>
          let seq := s.evalInorder (revFlag mem₃ nb) false
          if z ∈ seq then some (listParentFrom (nodeField mem₃ nb s.rootId OFF_PPAR) seq z) else none) := by
      apply findSome?_congr_left
      intro s hs
      have ho := hother_agree (List.mem_cons_of_mem _ hs)
      simp only [ho.1, ho.2.1]
    by_cases hzed : z = ed
    · rcases hzed.symm with rfl
      have hz_ted : ed ∈ t_ed.evalInorder (revFlag mem_p nb) false := by rw [hed_ev_p]; simp
      dsimp only [trees_fin]
      rw [findSome_lct_cons_pos hz_ted]
      simp [t_ed, AuxTree.rootId, hed_ev_p, hpp_ed_p, listParentFrom]
    · have hzed' : z ≠ ed := hzed
      by_cases hzu : z = u + 1
      · subst z
        have hz_ted : u + 1 ∈ t_ed.evalInorder (revFlag mem_p nb) false := by
          rw [hed_ev_p, htu_ev_3]; simp
        dsimp only [trees_fin]
        rw [findSome_lct_cons_pos hz_ted]
        simp [hed_ev_p, htu_ev_3, listParentFrom, hne_ed_u.symm]
      · have hz_ru : z ∈ t_u.evalInorder (revFlag mem₃ nb) false ↔
            z ∈ t_ed.evalInorder (revFlag mem_p nb) false := by
          rw [hed_ev_p]; simp [hzed']
        by_cases hztu : z ∈ t_u.evalInorder (revFlag mem₃ nb) false
        · have hz_ted : z ∈ t_ed.evalInorder (revFlag mem_p nb) false := hz_ru.1 hztu
          have hlp :
              listParentFrom (nodeField mem_p nb t_ed.rootId OFF_PPAR)
                (t_ed.evalInorder (revFlag mem_p nb) false) z =
              listParentFrom (nodeField mem₃ nb t_u.rootId OFF_PPAR)
                (t_u.evalInorder (revFlag mem₃ nb) false) z := by
            rw [hed_ev_p, htu_ev_3]
            simp [listParentFrom, hzed', hzu]
          dsimp only [trees_fin]
          rw [findSome_lct_cons_pos hz_ted, findSome_lct_cons_pos hztu]
          dsimp only
          rw [hlp]
          simp [hzed', hzu]
        · have hz_nted : z ∉ t_ed.evalInorder (revFlag mem_p nb) false := fun hm =>
            hztu (hz_ru.2 hm)
          have hed_ev3 : (AuxTree.node ed .leaf .leaf).evalInorder (revFlag mem₃ nb) false = [ed] := by
            cases revFlag mem₃ nb ed <;> simp [AuxTree.evalInorder]
          by_cases hzv : z ∈ t_v.evalInorder (revFlag mem₃ nb) false
          · have hzv_p : z ∈ t_v.evalInorder (revFlag mem_p nb) false := by
              rwa [(hother_agree List.mem_cons_self).2.1]
            have hp_tv := (hother_agree List.mem_cons_self).1
            have hev_tv := (hother_agree List.mem_cons_self).2.1
            dsimp only [trees_fin]
            rw [findSome_lct_cons_neg hz_nted, findSome_lct_cons_pos hzv_p,
              findSome_lct_cons_neg hztu, findSome_lct_cons_pos hzv]
            dsimp only
            rw [hp_tv, hev_tv]
            simp [hzed', hzu]
          · have hzv_p : z ∉ t_v.evalInorder (revFlag mem_p nb) false := by
              rwa [(hother_agree List.mem_cons_self).2.1]
            have hnin_ed : z ∉ (AuxTree.node ed .leaf .leaf).evalInorder (revFlag mem₃ nb) false := by
              rw [hed_ev3]; simp [hzed']
            dsimp only [trees_fin]
            rw [findSome_lct_cons_neg hz_nted, findSome_lct_cons_neg hzv_p,
              findSome_lct_cons_neg hztu, findSome_lct_cons_neg hzv,
              findSome_lct_cons_neg hnin_ed, hrest_eq]
            simp [hzed', hzu]
  have hfreeChain_p : FreeSlotChain mem_p nb (mem_p (b + LCT_HDR_FREE)) free' := by
    rw [hhdrFree_p]
    have hch3 := hi₃.freeChain
    rw [hhdr_free] at hch3
    rcases hch3 with ⟨_, htail3⟩
    rw [hnext_free] at htail3
    refine freeSlotChain_agree_of_eu htail3 ?_
    intro ed' hed'
    have hed'_ne : ed' ≠ ed := fun heq => by
      subst heq; simp only [List.nodup_cons] at hfree_nd; exact hfree_nd.1 hed'
    have hed'_bd := hi₃.freeNodeOk ed' (by simp [hed'])
    exact hfield_p_3_other ed' OFF_EU (by omega) hed'_bd.2.1 (by decide) hed'_ne (fun _ => by omega)
  have hfreeNode_p : ∀ ed' ∈ free', (F.link e).n + 1 ≤ ed' ∧ ed' ≤ lctCap (F.link e).n ∧
      AuxTree.node ed' .leaf .leaf ∈ trees_fin ∧
      nodeField mem_p nb ed' OFF_PPAR = 0 ∧
      nodeField mem_p nb ed' OFF_ISV = 0 ∧
      nodeField mem_p nb ed' OFF_HASE = 0 := by
    intro ed' hed'
    have hed'_ne : ed' ≠ ed := fun heq => by
      subst heq; simp only [List.nodup_cons] at hfree_nd; exact hfree_nd.1 hed'
    rcases hi₃.freeNodeOk ed' (by simp [hed']) with ⟨h1, h2, htr3, hpp, hisv, hhe⟩
    have htr_other : AuxTree.node ed' .leaf .leaf ∈ t_v :: rest_fin := by
      simp only [List.mem_cons] at htr3
      rcases htr3 with heq | heq | heq | hrest
      · exfalso; have : ed' = u + 1 := congrArg AuxTree.rootId heq; omega
      · exfalso; have : ed' = v + 1 := congrArg AuxTree.rootId heq; omega
      · exact absurd (congrArg AuxTree.rootId heq) hed'_ne
      · exact List.mem_cons_of_mem _ hrest
    have hf_ed' : ∀ off < NODE_STRIDE, nodeField mem_p nb ed' off = nodeField mem₃ nb ed' off :=
      fun off hoff =>
        hfield_p_3_other ed' off (by omega) h2 hoff hed'_ne (fun _ => by omega)
    rw [hFn]
    refine ⟨h1, h2, List.mem_cons_of_mem _ htr_other,
      by rw [hf_ed' OFF_PPAR (by decide)]; exact hpp,
      by rw [hf_ed' OFF_ISV (by decide)]; exact hisv,
      by rw [hf_ed' OFF_HASE (by decide)]; exact hhe⟩
  have hvert_p : VertexNodeOk mem_p nb (F.link e).n := by
    intro w' hw'
    rw [hFn] at hw'
    have hne_ed_w : w' + 1 ≠ ed := by omega
    have hw_cap : w' + 1 ≤ cap := by unfold cap lctCap; omega
    have hisv := hfield_p_3_other (w' + 1) OFF_ISV (by omega) hw_cap (by decide) hne_ed_w (fun _ => by decide)
    have hhase := hfield_p_3_other (w' + 1) OFF_HASE (by omega) hw_cap (by decide) hne_ed_w (fun _ => by decide)
    have hv3 := hi₃.vertexOk w' hw'
    dsimp only at hv3 ⊢
    rw [hisv, hhase]
    exact hv3
  have hedge_p : ActiveEdgeNodeOk mem_p nb h L P (F.link e).n trees_fin ((ed, e) :: edgeMap) := by
    intro q hq
    rw [hFn]
    rcases List.mem_cons.1 hq with rfl | hqm
    · have hfl_p : intVal mem_p p_fl h L = intVal mem_w p_fl h L :=
        intVal_congr fun i hi => hheap_p_w (p_fl + i) (by dsimp only [nb, cap]; omega)
          (by dsimp only [nb]; omega)
      have haf_p : intVal mem_p p_af h L = intVal mem_w p_af h L :=
        intVal_congr fun i hi => hheap_p_w (p_af + i) (by dsimp only [nb, cap]; omega)
          (by dsimp only [nb]; omega)
      have hab_p : intVal mem_p p_ab h L = intVal mem_w p_ab h L :=
        intVal_congr fun i hi => hheap_p_w (p_ab + i) (by dsimp only [nb, cap]; omega)
          (by dsimp only [nb]; omega)
      have hcf_p : intVal mem_p p_cf h L = e.cost := by
        rw [← hp_cf_val]
        exact intVal_congr fun i hi => hheap_p_w (p_cf + i) (by dsimp only [nb, cap]; omega)
          (by dsimp only [nb]; omega)
      have hfit_fl : Fits h L (intVal mem_w p_fl h L) :=
        link_fits_of_isFixedFit hfit_e.2.1 hp_fl_val
      have hfit_af : Fits h L (intVal mem_w p_af h L) :=
        link_fits_of_isFixedFit hfit_e.2.2.1 hp_af_val
      have hfit_ab : Fits h L (intVal mem_w p_ab h L) :=
        link_fits_of_isFixedFit hfit_e.2.2.2 hp_ab_val
      have hed_isv : nodeField mem_p nb ed OFF_ISV = 0 :=
        hed_fields OFF_ISV 0 (by simp [lctLinkOffPairs]) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have hed_hase : nodeField mem_p nb ed OFF_HASE = 1 :=
        hed_fields OFF_HASE 1 (by simp [lctLinkOffPairs]) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have hed_eid : nodeField mem_p nb ed OFF_EID = e.eid :=
        hed_fields OFF_EID e.eid (by simp [lctLinkOffPairs]) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have hed_eu : nodeField mem_p nb ed OFF_EU = u :=
        hed_fields OFF_EU u (by simp [lctLinkOffPairs]) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have hed_ev : nodeField mem_p nb ed OFF_EV = v :=
        hed_fields OFF_EV v (by simp [lctLinkOffPairs]) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have hed_dir : nodeField mem_p nb ed OFF_DIR = 0 :=
        hed_fields OFF_DIR 0 (by simp [lctLinkOffPairs]) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have hed_cb_ptr : nodeField mem_p nb ed OFF_COST_BWD = p_cf :=
        hed_fields OFF_COST_BWD p_cf (by simp [lctLinkOffPairs]) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have hed_fl_ptr : nodeField mem_p nb ed OFF_FLOW_PTR = p_fl :=
        hed_fields OFF_FLOW_PTR p_fl (by simp [lctLinkOffPairs]) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have hed_af_ptr : nodeField mem_p nb ed OFF_AF_PTR = p_ab :=
        hed_fields OFF_AF_PTR p_ab (by simp [lctLinkOffPairs]) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have hed_ab_ptr : nodeField mem_p nb ed OFF_AB_PTR = p_af :=
        hed_fields OFF_AB_PTR p_af (by simp [lctLinkOffPairs]) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      let s_ed : RawStep :=
        { nodeId := ed
          eid := e.eid
          eu := u
          ev := v
          fwd := false
          cost := e.cost
          flow := intVal mem_w p_fl h L
          availFwd := intVal mem_w p_af h L
          availBwd := intVal mem_w p_ab h L }
      have hown_ed : nodeOwnRawStep mem_p nb h L ed = some s_ed := by
        simp [nodeOwnRawStep, hed_hase, hed_dir, hed_eid, hed_eu, hed_ev, hed_cb_ptr, hed_fl_ptr,
          hed_af_ptr, hed_ab_ptr, hcf_p, hfl_p, haf_p, hab_p, s_ed]
      have hmod_ed : s_ed.addDeltaMod h L 0 = s_ed := by
        simp only [RawStep.addDeltaMod, Bool.false_eq_true, ↓reduceIte, sub_zero, add_zero, s_ed,
          wrap_of_fits hfit_fl, wrap_of_fits hfit_af, wrap_of_fits hfit_ab]
      have hmem_steps : s_ed ∈ evalMemSteps mem_p nb h L t_ed false 0 := by
        have hrf : revFlag mem_p nb ed = false := by simp [revFlag, nb, hed_rev_p]
        rw [evalMemSteps_split_of_root_zero hrf hed_ht_p, hown_ed, Option.map_some, hmod_ed]
        simp
      refine ⟨by omega, hed2, hed_isv, hed_hase, hed_eid, by rw [hed_eu, hu_eq], by rw [hed_ev, hv_eq],
        t_ed, List.mem_cons_self, by simp [t_ed, AuxTree.toList], s_ed, hmem_steps, ?_, ?_⟩
      · exact ⟨rfl, rfl, hu_eq.symm, hv_eq.symm, rfl, hp_fl_val, hp_af_val, hp_ab_val⟩
      · right
        refine ⟨rfl, ?_, ?_⟩
        · change lctAuxParent mem_p nb cap ed = e.v + 1
          rw [hpar_eq ed, ite_eq_left rfl, hv_eq]
        · change lctAuxParent mem_p nb cap (e.u + 1) = ed
          rw [hu_eq, hpar_eq (u + 1), ite_eq_right hne_ed_u.symm, ite_eq_left rfl]
    · rcases hi₃.edgeOk q hqm with ⟨h1, h2, hisv, hhe, heid, heu, hev, s_old, hs_mem, hed_in,
        st_old, hst_mem, hmatch, hdir_ok⟩
      have hq_ne_ed : q.1 ≠ ed := by
        have hnd : (edgeMap.map Prod.fst ++ (ed :: free')).Nodup :=
          hslots_perm.nodup_iff.2 ((List.nodup_range).map (fun _ _ h => by omega))
        exact fun heq => List.disjoint_of_nodup_append hnd (List.mem_map.2 ⟨q, hqm, heq⟩) hed_free
      have hq_ne_u : q.1 ≠ u + 1 := by omega
      have hf_q : ∀ off < NODE_STRIDE, nodeField mem_p nb q.1 off = nodeField mem₃ nb q.1 off :=
        fun off hoff => hfield_p_3_other q.1 off (by omega) h2 hoff hq_ne_ed (fun hc => absurd hc hq_ne_u)
      have hq_bd := hedge_lt q hqm
      have hdir_p : (st_old.fwd = true ∧ lctAuxParent mem_p nb cap q.1 = q.2.u + 1 ∧
          lctAuxParent mem_p nb cap (q.2.v + 1) = q.1) ∨
          (st_old.fwd = false ∧ lctAuxParent mem_p nb cap q.1 = q.2.v + 1 ∧
          lctAuxParent mem_p nb cap (q.2.u + 1) = q.1) := by
        have hp_q : lctAuxParent mem_p nb cap q.1 = lctAuxParent mem₃ nb cap q.1 := by
          rw [hpar_eq q.1, ite_eq_right hq_ne_ed, ite_eq_right hq_ne_u]
        rcases hdir_ok with ⟨hf, hpe, hpv⟩ | ⟨hf, hpe, hpu⟩
        · have hne_v_u : q.2.v + 1 ≠ u + 1 := fun heq => by
            rw [heq, hpar_u3] at hpv; omega
          have hne_v_ed : q.2.v + 1 ≠ ed := by omega
          left
          refine ⟨hf, hp_q.trans hpe, ?_⟩
          rw [hpar_eq (q.2.v + 1), ite_eq_right hne_v_ed, ite_eq_right hne_v_u]
          exact hpv
        · have hne_u_u : q.2.u + 1 ≠ u + 1 := fun heq => by
            rw [heq, hpar_u3] at hpu; omega
          have hne_u_ed : q.2.u + 1 ≠ ed := by omega
          right
          refine ⟨hf, hp_q.trans hpe, ?_⟩
          rw [hpar_eq (q.2.u + 1), ite_eq_right hne_u_ed, ite_eq_right hne_u_u]
          exact hpu
      refine ⟨h1, h2, by rw [hf_q OFF_ISV (by decide)]; exact hisv,
        by rw [hf_q OFF_HASE (by decide)]; exact hhe,
        by rw [hf_q OFF_EID (by decide)]; exact heid,
        by rw [hf_q OFF_EU (by decide)]; exact heu,
        by rw [hf_q OFF_EV (by decide)]; exact hev, ?_⟩
      simp only [List.mem_cons] at hs_mem
      rcases hs_mem with rfl | rfl | rfl | hs_rest
      · have hrf : revFlag mem_p nb ed = false := by simp [revFlag, nb, hed_rev_p]
        have hst_ed : st_old ∈ evalMemSteps mem_p nb h L t_ed false 0 := by
          rw [evalMemSteps_split_of_root_zero hrf hed_ht_p, htu_steps]
          exact List.mem_append.2 (Or.inr hst_mem)
        have hq_ted : q.1 ∈ t_ed.toList := by
          change q.1 ∈ AuxTree.leaf.toList ++ [ed] ++ t_u.toList
          simp only [List.mem_append]; right; exact hed_in
        exact ⟨t_ed, List.mem_cons_self, hq_ted, st_old, hst_ed, hmatch, hdir_p⟩
      · have hst_tv : st_old ∈ evalMemSteps mem_p nb h L t_v false 0 := by
          rw [(hother_agree List.mem_cons_self).2.2.2]; exact hst_mem
        exact ⟨t_v, List.mem_cons_of_mem _ List.mem_cons_self, hed_in, st_old, hst_tv, hmatch, hdir_p⟩
      · exfalso
        simp only [AuxTree.toList, List.nil_append, List.append_nil, List.mem_singleton] at hed_in
        exact hq_ne_ed hed_in
      · have hs_in : s_old ∈ t_v :: rest_fin := List.mem_cons_of_mem _ hs_rest
        have hst_s : st_old ∈ evalMemSteps mem_p nb h L s_old false 0 := by
          rw [(hother_agree hs_in).2.2.2]; exact hst_mem
        exact ⟨s_old, List.mem_cons_of_mem _ hs_in, hed_in, st_old, hst_s, hmatch, hdir_p⟩
  have haux_p : LctAuxPathOk mem_p nb (F.link e).n free' trees_fin := by
    rw [hFn]
    intro s hs
    simp only [trees_fin, List.mem_cons] at hs
    rcases hs with rfl | hsr
    · have hax_u := hi₃.auxPathOk t_u (by simp [t_u])
      dsimp only at hax_u ⊢
      have hseq_ne : t_ed.evalInorder (revFlag mem_p nb) false ≠ [] := by
        rw [hed_ev_p]; simp
      have hpp_ok : nodeField mem_p nb ed OFF_PPAR = 0 ∨
          (1 ≤ nodeField mem_p nb ed OFF_PPAR ∧
           nodeField mem_p nb ed OFF_PPAR ≤ lctCap F.n ∧
           nodeField mem_p nb ed OFF_PPAR ∉ free') := by
        rw [hpp_ed_p]
        right
        refine ⟨by omega, by unfold lctCap; omega, fun hm => by
          have := (hi₃.freeNodeOk (v + 1) (List.mem_cons_of_mem _ hm)).1; omega⟩
      have htu_ne : t_u.evalInorder (revFlag mem₃ nb) false ≠ [] := by
        rw [htu_ev_3]; simp
      have hlast_ed : (t_ed.evalInorder (revFlag mem_p nb) false).getLast? =
          (t_u.evalInorder (revFlag mem₃ nb) false).getLast? := by
        rw [hed_ev_p]
        exact List.getLast?_cons_of_ne_nil htu_ne
      rcases hax_u.2.2 with ⟨hu_free, _⟩ | ⟨w', hw', hlast_u⟩
      · exfalso
        have := (hi₃.freeNodeOk (u + 1) hu_free).1
        omega
      · exact ⟨hseq_ne, hpp_ok, Or.inr ⟨w', hw', hlast_ed.trans hlast_u⟩⟩
    · have hsr' : s ∈ t_v :: rest_fin := List.mem_cons.2 hsr
      have ho := hother_agree hsr'
      have hax3 := hi₃.auxPathOk s (by
        rcases hsr with rfl | hsr''
        · simp [t_v]
        · simp [hsr''])
      dsimp only at hax3 ⊢
      rw [ho.1, ho.2.1]
      refine ⟨hax3.1, ?_, ?_⟩
      · rcases hax3.2.1 with h0 | ⟨h1, h2, hnin⟩
        · exact Or.inl h0
        · exact Or.inr ⟨h1, h2, fun hm => hnin (List.mem_cons_of_mem _ hm)⟩
      · rcases hax3.2.2 with ⟨hf_s, hs_leaf, hpp0⟩ | hlast_s
        · have hs_in3 : s ∈ t_u :: t_v :: .node ed .leaf .leaf :: rest_fin := by
            rcases hsr with rfl | hsr''
            · simp [t_v]
            · simp [hsr'']
          have hs_ne : s.rootId ≠ ed := fun heq =>
            (hdisj_other hsr').1 (heq ▸ AuxTree.rootId_mem_toList (hi₃.sf.trees_ok s hs_in3).1)
          rcases List.mem_cons.1 hf_s with heq | hf'
          · exact absurd heq hs_ne
          · exact Or.inl ⟨hf', hs_leaf, hpp0⟩
        · exact Or.inr hlast_s
  have hsub_p : LctSubdivOk mem_p nb (F.link e).n free' ((ed, e) :: edgeMap) := by
    rw [hFn]
    have hno_ed : ∀ z, lctAuxParent mem₃ nb cap z ≠ ed :=
      lctLink_par_notin_free hi₃ hslots_perm hedge_lt hed_free
    have hv_no_u := lctLink_v_no_u hi₃ hrep₃ hu hv hdisc
    have hv_iter : iterParent (lctAuxParent mem_p nb cap) cap (v + 1) = 0 := by
      have hv_ne_ed : v + 1 ≠ ed := by omega
      have h1 := lctLink_iterParent_no_u (par := lctAuxParent mem₃ nb cap)
        (par' := lctAuxParent mem_p nb cap) (ed := ed) (u1 := u + 1)
        (fun z => by rw [hpar_eq z, hpar_eq ed, ite_eq_left rfl])
        hno_ed cap (v + 1) hv_ne_ed hv_no_u
      rw [h1]
      exact hi₃.subdivOk.1 (v + 1) (by omega) (by unfold lctCap; omega)
    have hterm : ∀ q, 1 ≤ q → q ≤ cap → ∃ N, iterParent (lctAuxParent mem_p nb cap) N q = 0 := by
      intro q hq1 hq2
      have hq3 : ∃ k, iterParent (lctAuxParent mem₃ nb cap) k q = 0 := by
        by_cases hq0 : q = 0
        · exact ⟨0, hq0⟩
        · exact ⟨cap, hi₃.subdivOk.1 q hq1 hq2⟩
      clear hq1 hq2
      rcases hq3 with ⟨k, hk⟩
      induction k generalizing q with
      | zero => exact ⟨0, hk⟩
      | succ k ih =>
          by_cases hqed : q = ed
          · rcases hqed.symm with rfl
            refine ⟨1 + cap, ?_⟩
            rw [iterParent_add]
            change iterParent (lctAuxParent mem_p nb cap) cap
              (lctAuxParent mem_p nb cap ed) = 0
            rw [hpar_eq ed, ite_eq_left rfl]
            exact hv_iter
          · by_cases hqu : q = u + 1
            · subst q
              refine ⟨1 + (1 + cap), ?_⟩
              rw [iterParent_add]
              change iterParent (lctAuxParent mem_p nb cap) (1 + cap)
                (lctAuxParent mem_p nb cap (u + 1)) = 0
              rw [hpar_eq (u + 1), ite_eq_right hne_ed_u.symm, ite_eq_left rfl, iterParent_add]
              change iterParent (lctAuxParent mem_p nb cap) cap
                (lctAuxParent mem_p nb cap ed) = 0
              rw [hpar_eq ed, ite_eq_left rfl]
              exact hv_iter
            · have hp_same : lctAuxParent mem_p nb cap q = lctAuxParent mem₃ nb cap q := by
                rw [hpar_eq q, ite_eq_right hqed, ite_eq_right hqu]
              have hk' : iterParent (lctAuxParent mem₃ nb cap) k (lctAuxParent mem₃ nb cap q) = 0 := by
                rw [Nat.add_comm k 1, iterParent_add] at hk
                exact hk
              rcases ih (lctAuxParent mem₃ nb cap q) hk' with ⟨N, hN⟩
              refine ⟨1 + N, ?_⟩
              rw [iterParent_add]
              change iterParent (lctAuxParent mem_p nb cap) N (lctAuxParent mem_p nb cap q) = 0
              rw [hp_same]
              exact hN
    refine ⟨link_acyc_pigeonhole (lctAuxParent_zero mem_p nb cap)
        (fun z _ _ => lctAuxParent_le_cap mem_p nb cap z) hterm, ?_, ?_, ?_⟩
    · intro ed' hed'
      have hed'_ne : ed' ≠ ed := fun heq => by
        subst heq; simp only [List.nodup_cons] at hfree_nd; exact hfree_nd.1 hed'
      have hed'_ne_u : ed' ≠ u + 1 := fun heq => by
        have := (hi₃.freeNodeOk ed' (by simp [hed'])).1; omega
      change lctAuxParent mem_p nb cap ed' = 0
      rw [hpar_eq ed', ite_eq_right hed'_ne, ite_eq_right hed'_ne_u]
      exact hi₃.subdivOk.2.1 ed' (by simp [hed'])
    · intro w' hw'
      by_cases hwu : w' = u
      · rcases hwu.symm with rfl
        right
        refine ⟨(ed, e), by simp, Or.inl hu_eq, ?_⟩
        change lctAuxParent mem_p nb cap (u + 1) = ed
        rw [hpar_eq (u + 1), ite_eq_right hne_ed_u.symm, ite_eq_left rfl]
      · have hne_ed_w : w' + 1 ≠ ed := by omega
        have hne_u_w : w' + 1 ≠ u + 1 := by omega
        have hpw : lctAuxParent mem_p nb cap (w' + 1) = lctAuxParent mem₃ nb cap (w' + 1) := by
          rw [hpar_eq (w' + 1), ite_eq_right hne_ed_w, ite_eq_right hne_u_w]
        rcases hi₃.subdivOk.2.2.1 w' hw' with h0 | ⟨p, hp, hinc, hpe⟩
        · exact Or.inl (by simpa [nb, cap, hpw] using h0)
        · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, hinc, by simpa [nb, cap, hpw] using hpe⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hpm
      · right
        refine ⟨?_, ?_⟩
        · change lctAuxParent mem_p nb cap ed = e.v + 1
          rw [hpar_eq ed, ite_eq_left rfl, hv_eq]
        · change lctAuxParent mem_p nb cap (e.u + 1) = ed
          rw [hu_eq, hpar_eq (u + 1), ite_eq_right hne_ed_u.symm, ite_eq_left rfl]
      · have hp_bd := hedge_lt p hpm
        have hp_slots : p.1 ≠ ed ∧ p.1 ≠ u + 1 := by
          have h1 := (hi₃.edgeOk p hpm).1
          have hnd : (edgeMap.map Prod.fst ++ (ed :: free')).Nodup :=
            hslots_perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => by omega))
          have hdis : p.1 ≠ ed := fun heq =>
            List.disjoint_of_nodup_append hnd (List.mem_map.2 ⟨p, hpm, heq⟩) hed_free
          exact ⟨hdis, by omega⟩
        rcases hi₃.subdivOk.2.2.2 p hpm with ⟨hp_ed, hp_v⟩ | ⟨hp_ed, hp_u⟩
        · left
          have hne_v_u : p.2.v + 1 ≠ u + 1 := fun heq => by
            rw [heq, hpar_u3] at hp_v
            have := (hi₃.edgeOk p hpm).1; omega
          have hne_v_ed : p.2.v + 1 ≠ ed := by omega
          refine ⟨?_, ?_⟩
          · change lctAuxParent mem_p nb cap p.1 = p.2.u + 1
            rw [hpar_eq p.1, ite_eq_right hp_slots.1, ite_eq_right hp_slots.2]; exact hp_ed
          · change lctAuxParent mem_p nb cap (p.2.v + 1) = p.1
            rw [hpar_eq (p.2.v + 1), ite_eq_right hne_v_ed, ite_eq_right hne_v_u]; exact hp_v
        · right
          have hne_u_u : p.2.u + 1 ≠ u + 1 := fun heq => by
            rw [heq, hpar_u3] at hp_u
            have := (hi₃.edgeOk p hpm).1; omega
          have hne_u_ed : p.2.u + 1 ≠ ed := by omega
          refine ⟨?_, ?_⟩
          · change lctAuxParent mem_p nb cap p.1 = p.2.v + 1
            rw [hpar_eq p.1, ite_eq_right hp_slots.1, ite_eq_right hp_slots.2]; exact hp_ed
          · change lctAuxParent mem_p nb cap (p.2.u + 1) = p.1
            rw [hpar_eq (p.2.u + 1), ite_eq_right hne_u_ed, ite_eq_right hne_u_u]; exact hp_u
  exact ⟨⟨hhdrN_p, hhdrCap_p, hhdrL_p, hhdrP_p, hsf_p, hfreeChain_p, hfreeNode_p, hvert_p,
      hedge_p, haux_p, hsub_p⟩,
    hpar_eq, (hother_agree List.mem_cons_self).2.1,
    fun s hs => ⟨(hother_agree (List.mem_cons_of_mem _ hs)).1,
      (hother_agree (List.mem_cons_of_mem _ hs)).2.1⟩,
    htu_ev, hpp_ed_p⟩

end LinkInvariants

end MinCostFlow.LinkCut.Prog
