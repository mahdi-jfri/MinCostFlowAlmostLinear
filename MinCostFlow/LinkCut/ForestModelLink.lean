module

public import MinCostFlow.LinkCut.ForestModelOps
public import MinCostFlow.LinkCut.ForestLink
import Mathlib.Tactic

/-!
# Helpers and `link` in the link-cut model

Helper lemmas on pairs, reroot and expose costs, and the operation `lctLink` with its
specification `lctLink_spec`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut

variable {α σ τ : Type*}

/-! ### Helper lemmas -/

theorem lctRerootCost_n (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) :
    (lctRerootCost P st v).1.n = st.n := rfl

theorem lctExposeCost_n (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) :
    (lctExposeCost P st v).1.n = st.n := rfl

theorem lctExposeCost_freeHead (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) :
    (lctExposeCost P st v).1.freeHead = st.freeHead :=
  lctExposeLoop_freeHead P (2 * st.n + 1)
    { n := st.n
      splay := SplayState.detachRight P (SplayState.splay P st.splay (2 * st.n + 1) v) v
      freeHead := st.freeHead } v

theorem lctRerootCost_freeHead (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) :
    (lctRerootCost P st v).1.freeHead = st.freeHead :=
  lctExposeCost_freeHead P st v

theorem isVertex_ne_zero {n u : ℕ} (hu : isVertex n u) : u ≠ 0 := by
  have := hu.1; omega

theorem isVertex_mem_active {P : LctPayload α σ τ} {st : LctState α σ τ}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {u : ℕ} (hu : isVertex st.n u) :
    u ∈ trees.flatMap AuxTree.toList := by
  have h := W.verticesActive (u - 1) (by have := hu.1; have := hu.2; omega)
  simpa [vid, Nat.sub_add_cancel hu.1] using h

theorem evalPairs_node_rev_false {P : LctPayload α σ τ} (hL : P.Laws)
    {s : SplayState α σ τ} {x : ℕ} {l r : AuxTree}
    (hrev : (s.nodes x).rev = false) (htag : (s.nodes x).tag = P.idTag) :
    SplayState.evalPairs P s (.node x l r) false P.idTag =
      SplayState.evalPairs P s l false P.idTag ++ [(x, (s.nodes x).val)] ++
        SplayState.evalPairs P s r false P.idTag := by
  simp [SplayState.evalPairs, hrev, htag, hL.compTag_id_left, hL.actVal_id, List.append_assoc]

theorem countNodes_eq_toList_length : ∀ t : AuxTree, t.countNodes = t.toList.length
  | .leaf => rfl
  | .node _ l r => by
      simp only [AuxTree.countNodes, AuxTree.toList, List.length_append, List.length_cons,
        List.length_nil]
      rw [countNodes_eq_toList_length l, countNodes_eq_toList_length r]
      omega

private theorem countNodes_eq_zero_iff : ∀ {t : AuxTree}, t.countNodes = 0 ↔ t = .leaf
  | .leaf => by simp [AuxTree.countNodes]
  | .node _ _ _ => by simp [AuxTree.countNodes]

theorem treeIds_perm {P : LctPayload α σ τ} (s : SplayState α σ τ) (t : AuxTree) :
    (treeIds P s t).Perm t.toList := by
  rw [treeIds, SplayState.evalPairs_map_fst]
  exact AuxTree.evalInorder_perm _ t false

private theorem forestPairs_perm_of_perm {P : LctPayload α σ τ} {s : SplayState α σ τ}
    {ts₁ ts₂ : List AuxTree} (hp : ts₁.Perm ts₂) :
    (forestPairs P s ts₁).Perm (forestPairs P s ts₂) := by
  induction hp with
  | nil => exact List.Perm.refl _
  | cons a _ ih =>
      simpa [forestPairs] using ih.append_left (SplayState.evalPairs P s a false P.idTag)
  | swap a b rest =>
      simp only [forestPairs, List.flatMap_cons]
      simpa [List.append_assoc] using List.Perm.append_right _ List.perm_append_comm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem forestPairs_erase_perm {P : LctPayload α σ τ} {s : SplayState α σ τ}
    {ts : List AuxTree} {t : AuxTree} (ht : t ∈ ts) :
    (SplayState.evalPairs P s t false P.idTag ++ forestPairs P s (ts.erase t)).Perm
      (forestPairs P s ts) :=
  (forestPairs_perm_of_perm (List.perm_cons_erase ht)).symm

theorem flatMap_perm_of_perm {ts₁ ts₂ : List AuxTree} (hp : ts₁.Perm ts₂) :
    (ts₁.flatMap AuxTree.toList).Perm (ts₂.flatMap AuxTree.toList) := by
  induction hp with
  | nil => exact List.Perm.refl _
  | cons a _ ih => simpa [List.flatMap_cons] using ih.append_left a.toList
  | swap a b rest =>
      simp only [List.flatMap_cons]
      simpa [List.append_assoc] using List.Perm.append_right _ List.perm_append_comm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem forestPairs_congr_trees {P : LctPayload α σ τ} {s₁ s₂ : SplayState α σ τ}
    {ts : List AuxTree}
    (h : ∀ c ∈ ts, SplayState.evalPairs P s₁ c false P.idTag =
      SplayState.evalPairs P s₂ c false P.idTag) :
    forestPairs P s₁ ts = forestPairs P s₂ ts := by
  induction ts with
  | nil => rfl
  | cons a rest ih =>
      simp only [forestPairs, List.flatMap_cons]
      exact congrArg₂ (· ++ ·) (h a List.mem_cons_self)
        (ih (fun c hc => h c (List.mem_cons_of_mem a hc)))

theorem mem_forestPairs_split {P : LctPayload α σ τ} {s : SplayState α σ τ}
    {ts : List AuxTree} {t : AuxTree} (ht : t ∈ ts)
    {p : ℕ × α} {pre post : List (ℕ × α)}
    (hspl : SplayState.evalPairs P s t false P.idTag = pre ++ [p] ++ post) :
    (p :: (pre ++ post ++ forestPairs P s (ts.erase t))).Perm (forestPairs P s ts) := by
  have hp1 : (pre ++ [p] ++ post ++ forestPairs P s (ts.erase t)).Perm (forestPairs P s ts) := by
    rw [← hspl]
    exact forestPairs_erase_perm ht
  have hp2 : (p :: (pre ++ post)).Perm (pre ++ [p] ++ post) := by
    simpa [List.append_assoc] using (List.perm_middle : (pre ++ p :: post).Perm (p :: (pre ++ post))).symm
  exact (hp2.append_right (forestPairs P s (ts.erase t))).trans hp1

theorem evalPairs_singleton_of_eq {P : LctPayload α σ τ} {s₁ s₂ : SplayState α σ τ}
    {x : ℕ} (hnd : (s₁.nodes x).val = (s₂.nodes x).val ∧
      (s₁.nodes x).tag = (s₂.nodes x).tag ∧
      (s₁.nodes x).rev = (s₂.nodes x).rev) :
    SplayState.evalPairs P s₁ (.node x .leaf .leaf) false P.idTag =
      SplayState.evalPairs P s₂ (.node x .leaf .leaf) false P.idTag := by
  rcases hnd with ⟨hv, _, _⟩
  simp only [SplayState.evalPairs]
  rw [hv]

private theorem lct_subRoot_eq_of_reaches {P : LctPayload α σ τ} {st : LctState α σ τ}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) {m z x : ℕ}
    (hz : z ∈ trees.flatMap AuxTree.toList)
    (hrec : reaches (inducedSubPar P st.splay trees) m z x = true) :
    subRoot (inducedSubPar P st.splay trees) (trees.flatMap AuxTree.toList).length x =
      subRoot (inducedSubPar P st.splay trees) (trees.flatMap AuxTree.toList).length z := by
  let par := inducedSubPar P st.splay trees
  let active := trees.flatMap AuxTree.toList
  induction m generalizing x with
  | zero =>
      simp only [reaches, beq_iff_eq] at hrec
      subst hrec; rfl
  | succ m ih =>
      simp only [reaches] at hrec
      by_cases hxz : x = z
      · subst hxz; rfl
      · have hbxz : (x == z) = false := beq_false_of_ne hxz
        simp only [hbxz, Bool.false_eq_true, ↓reduceIte] at hrec
        by_cases hpx0 : par x = 0
        · dsimp only [par] at hpx0
          simp [hpx0] at hrec
        · have hbp0 : (inducedSubPar P st.splay trees x == 0) = false := beq_false_of_ne hpx0
          simp only [hbp0, Bool.false_eq_true, ↓reduceIte] at hrec
          have hx_act : x ∈ active := by
            by_contra hx_nact
            exact hpx0 (inducedSubPar_eq_zero_of_not_mem hx_nact)
          exact (subRoot_step_eq W hx_act hpx0).trans (ih hrec)

private theorem node_leaf_of_countNodes_one {x : ℕ} {t : AuxTree}
    (hrt : t.rootId = x) (hcnt : t.countNodes = 1) :
    t = .node x .leaf .leaf := by
  cases t with
  | leaf => simp [AuxTree.countNodes] at hcnt
  | node y l r =>
      simp only [AuxTree.rootId] at hrt
      simp only [AuxTree.countNodes] at hcnt
      have hl0 : l.countNodes = 0 := by omega
      have hr0 : r.countNodes = 0 := by omega
      rw [countNodes_eq_zero_iff.mp hl0, countNodes_eq_zero_iff.mp hr0, hrt]

theorem two_nodes_decomp {l0 : ℕ} {Lv : AuxTree}
    (hrt : Lv.rootId = l0) (hcnt : Lv.countNodes = 2) :
    ∃ L1 R1 : AuxTree, Lv = .node l0 L1 R1 ∧
      ((L1 = .leaf ∧ ∃ b, R1 = .node b .leaf .leaf) ∨
       (R1 = .leaf ∧ ∃ a, L1 = .node a .leaf .leaf)) := by
  cases Lv with
  | leaf => simp [AuxTree.countNodes] at hcnt
  | node y L1 R1 =>
      simp only [AuxTree.rootId] at hrt
      subst hrt
      simp only [AuxTree.countNodes] at hcnt
      by_cases hL0 : L1.countNodes = 0
      · have hL : L1 = .leaf := countNodes_eq_zero_iff.mp hL0
        have hR1 : R1.countNodes = 1 := by omega
        have hReq : R1 = .node R1.rootId .leaf .leaf := node_leaf_of_countNodes_one rfl hR1
        exact ⟨L1, R1, rfl, Or.inl ⟨hL, R1.rootId, hReq⟩⟩
      · have hL1 : L1.countNodes = 1 ∧ R1.countNodes = 0 := by
          have : L1.countNodes ≥ 1 := Nat.pos_of_ne_zero hL0
          omega
        have hR : R1 = .leaf := countNodes_eq_zero_iff.mp hL1.2
        have hLeq : L1 = .node L1.rootId .leaf .leaf := node_leaf_of_countNodes_one rfl hL1.1
        exact ⟨L1, R1, rfl, Or.inr ⟨hR, L1.rootId, hLeq⟩⟩

theorem evalPairs_split_three_of_node {P : LctPayload α σ τ} (hL : P.Laws)
    {s : SplayState α σ τ} {ne u v : ℕ} {Lcut Rcut : AuxTree}
    (ht : SplayState.TreeInv P s (.node ne Lcut Rcut))
    (hrev : (s.nodes ne).rev = false) (htag : (s.nodes ne).tag = P.idTag)
    (hids : treeIds P s (.node ne Lcut Rcut) = [u, ne, v]) :
    Lcut = .node u .leaf .leaf ∧ Rcut = .node v .leaf .leaf := by
  have hev := evalPairs_node_rev_false hL hrev htag (s := s) (x := ne) (l := Lcut) (r := Rcut)
  have hmap : treeIds P s (.node ne Lcut Rcut) =
      (SplayState.evalPairs P s Lcut false P.idTag).map Prod.fst ++ [ne] ++
      (SplayState.evalPairs P s Rcut false P.idTag).map Prod.fst := by
    simp [treeIds, hev, List.map_append]
  rw [hids] at hmap
  have hlenL := SplayState.evalPairs_length P s Lcut false P.idTag
  have hlenR := SplayState.evalPairs_length P s Rcut false P.idTag
  rcases AuxTree.nodup_node_unfold ht.nodup with ⟨_, hneL, _, hneR, _⟩
  have hn_L : ne ∉ (SplayState.evalPairs P s Lcut false P.idTag).map Prod.fst := fun hm =>
    hneL ((mem_treeIds_iff P s Lcut ne).mp hm)
  cases hLm : (SplayState.evalPairs P s Lcut false P.idTag).map Prod.fst with
  | nil =>
      exfalso
      simp only [hLm, List.nil_append, List.cons_append] at hmap
      have hhd : u = ne := by simpa using congrArg List.head? hmap
      have hp : ([u, ne, v] : List ℕ).Perm (AuxTree.node ne Lcut Rcut).toList := by
        have h1 := treeIds_perm (P := P) s (.node ne Lcut Rcut)
        rw [hids] at h1
        exact h1
      have hnd3 : ([u, ne, v] : List ℕ).Nodup := hp.nodup_iff.mpr ht.nodup
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd3
      exact hnd3.1.1 hhd
  | cons a lrest =>
      simp only [hLm, List.cons_append] at hmap
      have ha_eq : u = a := by simpa using congrArg List.head? hmap
      have htail := congrArg List.tail hmap
      cases lrest with
      | nil =>
          simp only [List.nil_append, List.cons_append] at htail
          have htail2 := congrArg List.tail htail
          simp only [List.tail_cons] at htail2
          have hR_eq : (SplayState.evalPairs P s Rcut false P.idTag).map Prod.fst = [v] := htail2.symm
          have hLcnt : Lcut.countNodes = 1 := by
            have := congrArg List.length hLm
            simp only [List.length_map, hlenL, List.length_cons, List.length_nil] at this
            exact this
          have hRcnt : Rcut.countNodes = 1 := by
            have := congrArg List.length hR_eq
            simp only [List.length_map, hlenR, List.length_cons, List.length_nil] at this
            exact this
          have hL_rt : Lcut.rootId = a := by
            cases Lcut with
            | leaf => simp [AuxTree.countNodes] at hLcnt
            | node y Ll Rl =>
                have hy_mem : y ∈ (.node y Ll Rl : AuxTree).toList := by simp [AuxTree.toList]
                have hy_ids : y ∈ treeIds P s (.node y Ll Rl) := (mem_treeIds_iff P s _ y).mpr hy_mem
                dsimp only [treeIds] at hy_ids
                rw [hLm] at hy_ids
                simpa [AuxTree.rootId] using hy_ids
          have hR_rt : Rcut.rootId = v := by
            cases Rcut with
            | leaf => simp [AuxTree.countNodes] at hRcnt
            | node y Lr Rr =>
                have hy_mem : y ∈ (.node y Lr Rr : AuxTree).toList := by simp [AuxTree.toList]
                have hy_ids : y ∈ treeIds P s (.node y Lr Rr) := (mem_treeIds_iff P s _ y).mpr hy_mem
                dsimp only [treeIds] at hy_ids
                rw [hR_eq] at hy_ids
                simpa [AuxTree.rootId] using hy_ids
          exact ⟨node_leaf_of_countNodes_one (ha_eq ▸ hL_rt) hLcnt,
            node_leaf_of_countNodes_one hR_rt hRcnt⟩
      | cons b lrest2 =>
          exfalso
          simp only [List.cons_append] at htail
          have hne_b : ne = b := by simpa using congrArg List.head? htail
          apply hn_L
          rw [hLm, ← hne_b]
          simp

theorem reroot_adj_iff {P : LctPayload α σ τ}
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth)
    {u v : ℕ} (hu_v : isVertex st.n u) (hv_v : isVertex st.n v) (huv : u ≠ v)
    {st1 : LctState α σ τ} {trees1 : List AuxTree} {Lu : AuxTree} {depth1 : ℕ → ℕ}
    (ht1_mem : AuxTree.node u .leaf Lu ∈ trees1)
    (hW1 : LctInvWith P st1 trees1 freeList depth1)
    (_hperm1 : (trees1.flatMap AuxTree.toList).Perm (trees.flatMap AuxTree.toList))
    (hpu0 : inducedSubPar P st1.splay trees1 u = 0)
    (hrev_mem : ∀ z, z ∈ (AuxTree.node u .leaf Lu).toList ↔
      reaches (inducedSubPar P st.splay trees) (trees.flatMap AuxTree.toList).length z u = true)
    (hrev_out : ∀ z ∉ (AuxTree.node u .leaf Lu).toList,
      inducedSubPar P st1.splay trees1 z = inducedSubPar P st.splay trees z)
    (hrev_swap : ∀ x ∈ (AuxTree.node u .leaf Lu).toList, ∀ y ∈ (AuxTree.node u .leaf Lu).toList,
      inducedSubPar P st1.splay trees1 x = y ↔ inducedSubPar P st.splay trees y = x)
    (ne : ℕ) :
    (ne ∈ trees.flatMap AuxTree.toList ∧
      ((inducedSubPar P st.splay trees v = ne ∧ inducedSubPar P st.splay trees ne = u) ∨
       (inducedSubPar P st.splay trees u = ne ∧ inducedSubPar P st.splay trees ne = v))) ↔
    (ne ∈ trees.flatMap AuxTree.toList ∧
      inducedSubPar P st1.splay trees1 v = ne ∧ inducedSubPar P st1.splay trees1 ne = u) := by
  let t_rev := AuxTree.node u .leaf Lu
  let active := trees.flatMap AuxTree.toList
  let par := inducedSubPar P st.splay trees
  let par1 := inducedSubPar P st1.splay trees1
  have hu_trev : u ∈ t_rev.toList := by simp [t_rev, AuxTree.toList]
  have hu_act : u ∈ active := isVertex_mem_active W hu_v
  have hv_act : v ∈ active := isVertex_mem_active W hv_v
  constructor
  · rintro ⟨hne_act, hdir | hdir⟩
    · refine ⟨hne_act, ?_, ?_⟩
      · have hne_ntrev : ne ∉ t_rev.toList := fun hm => by
          rw [hrev_mem] at hm
          have hdep_ne := depth_le_of_reaches (fun z hz hp => W.subPar_mem_active hz hp)
            (fun z hz hp => W.acyclic z hz hp) _ _ _ hm hu_act
          have hlt := W.acyclic ne hne_act (by rw [hdir.2]; exact isVertex_ne_zero hu_v)
          rw [hdir.2] at hlt; omega
        have hv_ntrev : v ∉ t_rev.toList := fun hm => by
          rw [hrev_mem] at hm
          have hdep_v := depth_le_of_reaches (fun z hz hp => W.subPar_mem_active hz hp)
            (fun z hz hp => W.acyclic z hz hp) _ _ _ hm hu_act
          have hne_nz : ne ≠ 0 := by have := (W.activeValid ne hne_act).1; omega
          have hlt_ne := W.acyclic ne hne_act (by rw [hdir.2]; exact isVertex_ne_zero hu_v)
          have hlt_v := W.acyclic v hv_act (by rw [hdir.1]; exact hne_nz)
          rw [hdir.2] at hlt_ne
          rw [hdir.1] at hlt_v
          omega
        rw [hrev_out v hv_ntrev]
        exact hdir.1
      · have hne_ntrev : ne ∉ t_rev.toList := fun hm => by
          rw [hrev_mem] at hm
          have hdep_ne := depth_le_of_reaches (fun z hz hp => W.subPar_mem_active hz hp)
            (fun z hz hp => W.acyclic z hz hp) _ _ _ hm hu_act
          have hlt := W.acyclic ne hne_act (by rw [hdir.2]; exact isVertex_ne_zero hu_v)
          rw [hdir.2] at hlt; omega
        rw [hrev_out ne hne_ntrev]
        exact hdir.2
    · refine ⟨hne_act, ?_, ?_⟩
      · have hne_nz : ne ≠ 0 := by have := (W.activeValid ne hne_act).1; omega
        have hne_mem : ne ∈ t_rev.toList := by
          rw [hrev_mem]
          have hact_pos : 0 < active.length := List.length_pos_of_mem hne_act
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hact_pos)
          rw [hk]
          simp [reaches, hdir.1, hne_nz, reaches_self]
        have hv_mem : v ∈ t_rev.toList := by
          rw [hrev_mem]
          have h_edge : isEdgeSlot st.n ne :=
            hdir.1 ▸ W.vertexParEdge u hu_v (by rw [hdir.1]; exact hne_nz)
          have hne_ne : ne ≠ u := fun h0 => not_vertex_and_edge ⟨hu_v, h0 ▸ h_edge⟩
          have hact_ge : 2 ≤ (List.flatMap AuxTree.toList trees).length := by
            cases h_act : List.flatMap AuxTree.toList trees with
            | nil => exact absurd (h_act ▸ hne_act) (by simp)
            | cons a rest =>
                cases rest with
                | nil =>
                    have hu_eq : u = a := by simpa [active, h_act] using hu_act
                    have hne_eq_a : ne = a := by simpa [h_act] using hne_act
                    exact absurd (hne_eq_a.trans hu_eq.symm) hne_ne
                | cons b bs => simp
          obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hact_ge
          change reaches par (List.flatMap AuxTree.toList trees).length v u = true
          rw [hk]
          simp [par, reaches, hdir.1, hdir.2, hne_nz, isVertex_ne_zero hv_v, reaches_self]
        exact (hrev_swap v hv_mem ne hne_mem).mpr hdir.2
      · have hne_nz : ne ≠ 0 := by have := (W.activeValid ne hne_act).1; omega
        have hne_mem : ne ∈ t_rev.toList := by
          rw [hrev_mem]
          have hact_pos : 0 < active.length := List.length_pos_of_mem hne_act
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hact_pos)
          rw [hk]
          simp [reaches, hdir.1, hne_nz, reaches_self]
        exact (hrev_swap ne hne_mem u hu_trev).mpr hdir.1
  · rintro ⟨hne_act, h1v, h1ne⟩
    refine ⟨hne_act, ?_⟩
    by_cases hv_trev : v ∈ t_rev.toList
    · have hne_trev : ne ∈ t_rev.toList := by
        have hv_mem1 := (mem_treeIds_iff P st1.splay t_rev v).mpr hv_trev
        have hpar_eq : par1 v = chainPred (st1.splay.nodes t_rev.rootId).ppar (treeIds P st1.splay t_rev) v :=
          inducedSubPar_eq_of_mem hW1.activeNodup ht1_mem hv_trev
        dsimp [par1] at hpar_eq
        rw [h1v] at hpar_eq
        have hhd_u : listHead0 (treeIds P st1.splay t_rev) = u :=
          (eq_listHead0_of_par_zero hW1 ht1_mem hu_trev hpu0).symm
        have hids_ne : treeIds P st1.splay t_rev ≠ [] := treeIds_ne_nil (hW1.treesNonEmpty t_rev ht1_mem)
        cases hids : treeIds P st1.splay t_rev with
        | nil => exact absurd hids hids_ne
        | cons a rest =>
            rw [hids] at hhd_u hpar_eq hv_mem1
            simp only [listHead0] at hhd_u
            rw [hhd_u] at hpar_eq hv_mem1 hids
            simp only [chainPred, huv.symm, ↓reduceIte] at hpar_eq
            rcases chainPred_mem_or_prev ((List.mem_cons.mp hv_mem1).resolve_left huv.symm) with ha | hr
            · have hne_u : ne = u := hpar_eq.trans ha
              rw [hne_u]; exact hu_trev
            · have hne_r : ne ∈ rest := hpar_eq ▸ hr
              exact (mem_treeIds_iff P st1.splay t_rev ne).mp (by rw [hids]; exact List.mem_cons_of_mem u hne_r)
      right
      exact ⟨(hrev_swap ne hne_trev u hu_trev).mp h1ne, (hrev_swap v hv_trev ne hne_trev).mp h1v⟩
    · by_cases hne_trev : ne ∈ t_rev.toList
      · exfalso
        have hpar_v : inducedSubPar P st.splay trees v = ne := (hrev_out v hv_trev).symm.trans h1v
        have hpar_u_ne : inducedSubPar P st.splay trees u = ne := (hrev_swap ne hne_trev u hu_trev).mp h1ne
        have hne_nz : ne ≠ 0 := by have := (W.activeValid ne hne_act).1; omega
        have hne_slot : isEdgeSlot st.n ne :=
          hpar_u_ne ▸ W.vertexParEdge u hu_v (by rw [hpar_u_ne]; exact hne_nz)
        rcases W.edgeParVertex ne hne_act hne_slot with ⟨hpne_nz, _⟩
        rcases W.edgeUniqueChild ne hne_act hne_slot with ⟨w0, _, hw0_uniq⟩
        have hpar_ne_ntrev : inducedSubPar P st.splay trees ne ≠ v := fun hpv => by
          have h1 := W.acyclic v hv_act (by rw [hpar_v]; exact hne_nz)
          have h2 := W.acyclic ne hne_act hpne_nz
          rw [hpar_v] at h1
          rw [hpv] at h2
          omega
        have hu_neq_p : u ≠ inducedSubPar P st.splay trees ne := fun heq => by
          have h1 := W.acyclic u (isVertex_mem_active W hu_v) (by rw [hpar_u_ne]; exact hne_nz)
          have h2 := W.acyclic ne hne_act hpne_nz
          rw [hpar_u_ne] at h1; rw [← heq] at h2; omega
        have hv_neq_p : v ≠ inducedSubPar P st.splay trees ne := fun heq => hpar_ne_ntrev heq.symm
        have hu_eq : u = w0 := hw0_uniq u ⟨isVertex_mem_active W hu_v, hpar_u_ne, hu_v, hu_neq_p⟩
        have hv_eq : v = w0 := hw0_uniq v ⟨hv_act, hpar_v, hv_v, hv_neq_p⟩
        exact huv (hu_eq.trans hv_eq.symm)
      · left
        exact ⟨(hrev_out v hv_trev).symm.trans h1v, (hrev_out ne hne_trev).symm.trans h1ne⟩

/-! ### `lctLinkCost`, `lctLink`, and `lctLink_spec` -/

/-- Reroot `v` then `u`, pop a free edge slot `ne`, and link `v`'s tree as a virtual child of `ne`
with parent `u`, returning `(st', splayHalves, spliceIters)`. -/
def lctLinkCost (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ) (eVal : α) :
    LctState α σ τ × ℕ × ℕ :=
  if u == 0 || v == 0 || u == v || st.freeHead == 0 then (st, 0, 1)
  else
    let res1 := lctRerootCost P st v
    let st1 := res1.1
    let res2 := lctRerootCost P st1 u
    let st2 := res2.1
    let ne := st2.freeHead
    if ne == 0 then (st2, res1.2.1 + res2.2.1, res1.2.2 + res2.2.2 + 1)
    else
      let nextFree := (st2.splay.nodes ne).par
      let s1 := SplayState.makeSingleton P st2.splay ne eVal u
      let s2 := s1.setPpar v ne
      let st' : LctState α σ τ := { n := st2.n, splay := s2, freeHead := nextFree }
      (st', res1.2.1 + res2.2.1, res1.2.2 + res2.2.2 + 1)

/-- Functional wrapper for `lctLinkCost`. -/
def lctLink (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ) (eVal : α) : LctState α σ τ :=
  (lctLinkCost P st u v eVal).1

theorem lctLink_spec {P : LctPayload α σ τ} (hL : P.Laws)
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth)
    {ne : ℕ} {freeRest : List ℕ} (hfl : freeList = ne :: freeRest)
    {u v : ℕ} (hu_v : isVertex st.n u) (hv_v : isVertex st.n v)
    (hdisc : subRoot (inducedSubPar P st.splay trees) (trees.flatMap AuxTree.toList).length u ≠
      subRoot (inducedSubPar P st.splay trees) (trees.flatMap AuxTree.toList).length v)
    (eVal : α) :
    let res := lctLinkCost P st u v eVal
    let st' := res.1
    let halves := res.2.1
    let iters := res.2.2
    let res1 := lctRerootCost P st v
    let st1 := res1.1
    let res2 := lctRerootCost P st1 u
    let st2 := res2.1
    ∃ trees2 depth2 trees' depth',
      LctInvWith P st2 trees2 (ne :: freeRest) depth2 ∧
      LctInvWith P st' trees' freeRest depth' ∧
      (trees2.flatMap AuxTree.toList).Perm (trees.flatMap AuxTree.toList) ∧
      (trees'.flatMap AuxTree.toList).Perm (ne :: trees2.flatMap AuxTree.toList) ∧
      inducedSubPar P st'.splay trees' v = ne ∧
      inducedSubPar P st'.splay trees' ne = u ∧
      (∀ z ≠ v, z ≠ ne → inducedSubPar P st'.splay trees' z = inducedSubPar P st2.splay trees2 z) ∧
      (forestPairs P st'.splay trees').Perm ((ne, eVal) :: forestPairs P st2.splay trees2) ∧
      halves + sumTreePhi P st' ≤ sumTreePhi P st + 14 * Nat.log 2 (2 * st.n + 1) ∧
      iters + heavyCount P st' ≤ heavyCount P st + 6 * Nat.log 2 (2 * st.n + 1) + 9 := by
  intro res st' halves iters res1 st1 res2 st2
  have huv : u ≠ v := fun h => hdisc (congrArg _ h)
  have hfh_eq : st.freeHead = ne ∧ ne ≠ 0 := by
    have hfl0 : FreeListInv st.splay st.freeHead (ne :: freeRest) := hfl ▸ W.freeListInv
    rcases hfl0 with ⟨hnz, hfh, _⟩
    exact ⟨hfh, by rw [← hfh]; exact hnz⟩
  have hfh2 : st2.freeHead = ne := by
    have h1 : st1.freeHead = st.freeHead := lctRerootCost_freeHead P st v
    have h2 : st2.freeHead = st1.freeHead := lctRerootCost_freeHead P st1 u
    rw [h2, h1, hfh_eq.1]
  have hcond_false : (u == 0 || v == 0 || u == v || st.freeHead == 0) = false := by
    simp [isVertex_ne_zero hu_v, isVertex_ne_zero hv_v, huv, hfh_eq.1, hfh_eq.2]
  have hne_false : (ne == 0) = false := beq_false_of_ne hfh_eq.2
  have hres_eq : res =
      (LctState.mk st2.n
         ((SplayState.makeSingleton P st2.splay ne eVal u).setPpar v ne)
         (st2.splay.nodes ne).par,
        res1.2.1 + res2.2.1, res1.2.2 + res2.2.2 + 1) := by
    simp only [res, lctLinkCost, hcond_false, Bool.false_eq_true, ↓reduceIte,
      res1, st1, res2, st2, hfh2, hne_false]
  have hu_act : u ∈ trees.flatMap AuxTree.toList := isVertex_mem_active W hu_v
  have hv_act : v ∈ trees.flatMap AuxTree.toList := isVertex_mem_active W hv_v
  obtain ⟨tv0, htv0, hv0_mem⟩ := List.mem_flatMap.mp hv_act
  rcases lctReroot_spec hL W htv0 hv0_mem hv_v with
    ⟨trees1, Lv, depth1, ht_v_mem, hW1, hact1_perm, hpp_v1, hpar_v1, _, _, _,
      hev_v1, _, _, _, _, _, hsub_agree1, hpot1, hH1⟩
  have hW1_fl : LctInvWith P st1 trees1 (ne :: freeRest) depth1 := hfl ▸ hW1
  have hu_act1 : u ∈ trees1.flatMap AuxTree.toList := hact1_perm.symm.mem_iff.mp hu_act
  have hv_act1 : v ∈ trees1.flatMap AuxTree.toList := hact1_perm.symm.mem_iff.mp hv_act
  obtain ⟨tu1, htu1, hu1_mem⟩ := List.mem_flatMap.mp hu_act1
  have hu_v1 : isVertex st1.n u := by
    have hn1 : st1.n = st.n := by simpa [st1, res1] using lctRerootCost_n P st v
    exact hn1 ▸ hu_v
  have hdisc1 : subRoot (inducedSubPar P st1.splay trees1) (trees1.flatMap AuxTree.toList).length u ≠
      subRoot (inducedSubPar P st1.splay trees1) (trees1.flatMap AuxTree.toList).length v :=
    mt (hsub_agree1 u hu_act v hv_act).mp hdisc
  rcases lctReroot_spec hL hW1_fl htu1 hu1_mem hu_v1 with
    ⟨trees2, Lu, depth2, ht_u_mem, hW2, hact2_perm, hpp_u2, _, hreach_u2, _, _,
      _, _, _, _, _, hunt2, _, hpot2, hH2⟩
  let t_v := AuxTree.node v .leaf Lv
  let t_u := AuxTree.node u .leaf Lu
  have hhead_v1 : listHead0 (treeIds P st1.splay t_v) = v := by
    let st_expv := (lctExposeCost P st v).1
    have htv_exp := lctExpose_spec hL W htv0 hv0_mem
    -- Take the witnesses of `lctExpose_spec`.
    rcases htv_exp with ⟨trees_ev, Lv_ev, _, _, _, _, _, _, _, hrev_ev, htag_ev, _⟩
    -- `lctReroot_spec` gives `hev_v1`:
    -- `evalPairs P st1.splay (node v leaf Lv) false P.idTag` is the reverse of a map of
    -- `evalPairs P (lctExposeCost P st v).1 (node v Lv leaf) false P.idTag`.
    -- The witness `Lv` there is the witness of `lctExpose_spec`: in `ForestModelOps.lean`,
    -- `t_rev := node v leaf L`, `t_exp := node v L leaf` and
    -- `onPath := evalPairs P st_exp.splay t_exp false P.idTag`.
    -- So we need no fact on the reversal bit of `v`.
    -- The vertex `v` lies in `(node v .leaf Lv).toList`,
    -- and `par1 v = 0` (`hpar_v1`).
    -- So `eq_listHead0_of_par_zero` (`ForestModelOps.lean`)
    -- gives `v = listHead0 (treeIds P st1.splay t_v)`
    -- directly.
    exact (eq_listHead0_of_par_zero hW1 ht_v_mem (by simp [AuxTree.toList]) hpar_v1).symm
  have hno_u_tv : ∀ w ∈ t_v.toList,
      reaches (inducedSubPar P st1.splay trees1) (trees1.flatMap AuxTree.toList).length w u = false := by
    intro w hw
    by_contra hfalse
    have htr : reaches (inducedSubPar P st1.splay trees1) (trees1.flatMap AuxTree.toList).length w u = true :=
      Bool.eq_true_of_not_eq_false hfalse
    have hw_act1 : w ∈ trees1.flatMap AuxTree.toList := List.mem_flatMap.mpr ⟨t_v, ht_v_mem, hw⟩
    have hsub_uw := lct_subRoot_eq_of_reaches hW1 hw_act1 htr
    have hrc_vw : reaches (inducedSubPar P st1.splay trees1) (trees1.flatMap AuxTree.toList).length
        (listHead0 (treeIds P st1.splay t_v)) w = true := tree_reaches_head hW1 ht_v_mem hw
    rw [hhead_v1] at hrc_vw
    have hsub_wv := lct_subRoot_eq_of_reaches hW1 hv_act1 hrc_vw
    exact hdisc1 (hsub_uw.trans hsub_wv)
  rcases hunt2 t_v ht_v_mem hno_u_tv with ⟨ht_v_mem2, hag_tv⟩
  have htu_ne_tv : t_v ≠ t_u := fun h => by
    have hv_inu : v ∈ t_u.toList := h ▸ (by dsimp only [t_v]; simp [AuxTree.toList])
    have hv_rch : reaches (inducedSubPar P st1.splay trees1) (trees1.flatMap AuxTree.toList).length v u = true :=
      (hreach_u2 v).mp hv_inu
    have hfalse := hno_u_tv v (by dsimp only [t_v]; simp [AuxTree.toList])
    rw [hv_rch] at hfalse
    exact Bool.noConfusion hfalse
  have hpp_v2 : (st2.splay.nodes t_v.rootId).ppar = 0 := by
    have hv_tv : t_v.rootId ∈ t_v.toList := by simp [t_v, AuxTree.rootId, AuxTree.toList]
    rw [hag_tv t_v.rootId hv_tv]
    exact hpp_v1
  have hhead_v2 : listHead0 (treeIds P st2.splay t_v) = v := by
    have htr : treeIds P st2.splay t_v = treeIds P st1.splay t_v := by
      simp only [treeIds]
      congr 1
      exact SplayState.evalPairs_agree P (fun w hw => hag_tv w hw) false P.idTag
    rw [htr, hhead_v1]
  have htu_v : isVertex st2.n t_u.rootId := by
    change isVertex st2.n u
    have hn2 : st2.n = st1.n := by simpa [st2, res2] using lctRerootCost_n P st1 u
    exact hn2 ▸ hu_v1
  rcases link_splice_spec hL hW2 rfl ht_v_mem2 ht_u_mem htu_ne_tv hpp_v2 hpp_u2 htu_v eVal with
    ⟨depth', hW', hPhi', hH', hpar'_v, hpar'_ne, hpar'_oth⟩
  have hst'_eq : st' = LctState.mk st2.n
      ((SplayState.makeSingleton P st2.splay ne eVal t_u.rootId).setPpar t_v.rootId ne)
      (st2.splay.nodes ne).par := by
    simpa [st', t_u, t_v, AuxTree.rootId] using congrArg Prod.fst hres_eq
  have hst'_splay : st'.splay =
      ((SplayState.makeSingleton P st2.splay ne eVal t_u.rootId).setPpar t_v.rootId ne) :=
    congrArg LctState.splay hst'_eq
  rw [← hst'_eq] at hW' hPhi' hH'
  rw [← hst'_splay] at hpar'_v hpar'_ne hpar'_oth
  let trees' := AuxTree.node ne .leaf .leaf :: trees2
  have hact'_perm : (trees'.flatMap AuxTree.toList).Perm (ne :: trees2.flatMap AuxTree.toList) := by
    simp [trees', List.flatMap_cons, AuxTree.toList]
  have hpar'_v' : inducedSubPar P st'.splay trees' v = ne := by
    dsimp only [st2, res2] at hhead_v2
    rwa [hhead_v2] at hpar'_v
  have hpar'_ne' : inducedSubPar P st'.splay trees' ne = u := by
    simpa [t_u, AuxTree.rootId] using hpar'_ne
  have hpar'_oth' : ∀ z ≠ v, z ≠ ne →
      inducedSubPar P st'.splay trees' z = inducedSubPar P st2.splay trees2 z := by
    intro z hzv hzne
    dsimp only [st2, res2] at hhead_v2
    exact hpar'_oth z (by rwa [hhead_v2]) hzne
  have hpairs_perm : (forestPairs P st'.splay trees').Perm ((ne, eVal) :: forestPairs P st2.splay trees2) := by
    let s_mk := SplayState.makeSingleton P st2.splay ne eVal t_u.rootId
    let s_sp := s_mk.setPpar t_v.rootId ne
    have hfl2 : FreeListInv st2.splay st2.freeHead (ne :: freeRest) := hW2.freeListInv
    have hne_nz : ne ≠ 0 := by rcases hfl2 with ⟨hnz, hfh, _⟩; rw [← hfh]; exact hnz
    have hne_nin2 : ne ∉ trees2.flatMap AuxTree.toList :=
      hW2.active_of_freeList_disjoint (by simp)
    have htne_mk := SplayState.makeSingleton_treeInv hL st2.splay hne_nz eVal t_u.rootId
    have hev_mk : SplayState.evalPairs P s_mk (.node ne .leaf .leaf) false P.idTag = [(ne, eVal)] :=
      htne_mk.2.2.2.2.1
    have hne_ne_v : ne ≠ t_v.rootId := fun h => hne_nin2 (List.mem_flatMap.mpr
      ⟨t_v, ht_v_mem2, h ▸ by simp [t_v, AuxTree.rootId, AuxTree.toList]⟩)
    have hev_sp : SplayState.evalPairs P s_sp (.node ne .leaf .leaf) false P.idTag = [(ne, eVal)] := by
      rw [← hev_mk]
      exact evalPairs_singleton_of_eq (by simp [s_sp, SplayState.setPpar, hne_ne_v])
    have hev_other : ∀ c ∈ trees2,
        SplayState.evalPairs P s_sp c false P.idTag = SplayState.evalPairs P st2.splay c false P.idTag := by
      intro c hc
      have hne_nc : ne ∉ c.toList := fun hm => hne_nin2 (List.mem_flatMap.mpr ⟨c, hc, hm⟩)
      have hev_c_mk : SplayState.evalPairs P s_mk c false P.idTag = SplayState.evalPairs P st2.splay c false P.idTag :=
        SplayState.evalPairs_agree P (fun w hw => htne_mk.2.2.2.2.2 w (fun h => hne_nc (h ▸ hw))) false P.idTag
      have hc_inv : SplayState.TreeInv P s_mk c :=
        SplayState.TreeInv_agree (hW2.treesInv c hc) (fun w hw =>
          (htne_mk.2.2.2.2.2 w (fun h => hne_nc (h ▸ hw))).symm)
      by_cases hctv : c = t_v
      · subst hctv
        have hsp_tv := (SplayState.setPpar_root_preserves P hc_inv (hW2.treesNonEmpty t_v ht_v_mem2) (pp := ne)).2.1
        change SplayState.evalPairs P s_sp t_v false P.idTag = _
        rw [hsp_tv, hev_c_mk]
      · have hv_nc : t_v.rootId ∉ c.toList := fun hm =>
          hctv (flatMap_mem_unique hW2.activeNodup hc ht_v_mem2 hm (by simp [t_v, AuxTree.rootId, AuxTree.toList]))
        have hsp_c : SplayState.evalPairs P s_sp c false P.idTag = SplayState.evalPairs P s_mk c false P.idTag :=
          SplayState.evalPairs_agree P (fun w hw => by
            have hne_w : w ≠ t_v.rootId := fun h => hv_nc (h ▸ hw)
            simp [s_sp, SplayState.setPpar, hne_w]) false P.idTag
        exact hsp_c.trans hev_c_mk
    have hs'_sp : st'.splay = s_sp := by
      rw [hst'_eq]
    have hp_trees2 : forestPairs P s_sp trees2 = forestPairs P st2.splay trees2 :=
      forestPairs_congr_trees hev_other
    rw [hs'_sp]
    simp only [trees', forestPairs, List.flatMap_cons, hev_sp, List.singleton_append]
    dsimp only [forestPairs] at hp_trees2
    rw [hp_trees2]
  have hphi_fin : halves + sumTreePhi P st' ≤ sumTreePhi P st + 14 * Nat.log 2 (2 * st.n + 1) := by
    have hhalves_eq : halves = res1.2.1 + res2.2.1 := by
      have := congrArg (fun p => p.2.1) hres_eq
      exact this
    have hn1 : st1.n = st.n := lctRerootCost_n P st v
    have hn2 : st2.n = st1.n := lctRerootCost_n P st1 u
    dsimp only [st1, st2, res1, res2] at hpot1 hpot2 hPhi' hhalves_eq hn1 hn2
    rw [hhalves_eq]
    rw [hn2, hn1] at hPhi'
    rw [hn1] at hpot2
    omega
  have hH_fin : iters + heavyCount P st' ≤ heavyCount P st + 6 * Nat.log 2 (2 * st.n + 1) + 9 := by
    have hiters_eq : iters = res1.2.2 + res2.2.2 + 1 := by
      have := congrArg (fun p => p.2.2) hres_eq
      exact this
    have hn1 : st1.n = st.n := lctRerootCost_n P st v
    have hn2 : st2.n = st1.n := lctRerootCost_n P st1 u
    dsimp only [st1, st2, res1, res2] at hH1 hH2 hH' hiters_eq hn1 hn2
    rw [hiters_eq]
    rw [hn1] at hH2
    omega
  exact ⟨trees2, depth2, trees', depth', hW2, hW', hact2_perm.trans hact1_perm,
    hact'_perm, hpar'_v', hpar'_ne', hpar'_oth', hpairs_perm, hphi_fin, hH_fin⟩

end MinCostFlow.LinkCut
end
