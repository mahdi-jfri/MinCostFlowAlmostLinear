module

public import MinCostFlow.LinkCut.ForestModelLink
import Mathlib.Tactic

/-!
# Generic Link-Cut Tree Model: `link` and `cut` Operations and Specifications

This file implements `lctLinkCost` / `lctLink` and `lctCutCost` / `lctCut` over an arbitrary
`(P : LctPayload α σ τ) [P.Laws]`, and proves their full correctness, induced-parent, pair-list
permutation, heavy-edge count, and `O(log n)` amortized Sleator–Tarjan potential bounds against
`LctInvWith`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut

variable {α σ τ : Type*}

private theorem evalPairs_detachRootChildren_setPar_other {P : LctPayload α σ τ}
    {s : SplayState α σ τ} {x a b w : ℕ} (hx : x ≠ 0) (haw : a ≠ x) (hbw : b ≠ x) (hab : a ≠ b)
    (hl : (s.nodes x).left = a) (hr : (s.nodes x).right = b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    let s1 := SplayState.detachRootChildren P s x
    let s2 := s1.setPar x w
    ((s2.nodes a).val = (s.nodes a).val ∧ (s2.nodes a).tag = (s.nodes a).tag ∧ (s2.nodes a).rev = (s.nodes a).rev) ∧
    ((s2.nodes b).val = (s.nodes b).val ∧ (s2.nodes b).tag = (s.nodes b).tag ∧ (s2.nodes b).rev = (s.nodes b).rev) := by
  intro s1 s2
  have hs1 : s1 = SplayState.pull P
      ((((((s.setPar a 0).setPpar a 0).setPar b 0).setPpar b 0).setLeft x 0).setRight x 0) x := by
    simp [s1, SplayState.detachRootChildren, hx, hl, hr, ha0, hb0]
  have hp_a : (s2.nodes a) = { s.nodes a with par := 0, ppar := 0 } := by
    simp [s2, hs1, SplayState.pull, hx, SplayState.updateNode, haw, SplayState.setPar, SplayState.setPpar,
      SplayState.setLeft, SplayState.setRight, hab]
  have hp_b : (s2.nodes b) = { s.nodes b with par := 0, ppar := 0 } := by
    simp [s2, hs1, SplayState.pull, hx, SplayState.updateNode, hbw, SplayState.setPar, SplayState.setPpar,
      SplayState.setLeft, SplayState.setRight, hab.symm]
  simp [hp_a, hp_b]

/-! ### `lctCutCost`, `lctCut`, and `lctCut_spec` -/

/-- Reroot `u`, expose `v`, and if `(u, v)` are joined by a single subdivided edge `ne`,
splay `ne` to root, detach `u` and `v`, and push `ne` onto `freeHead`,
returning `(st', splayHalves, spliceIters)`. -/
def lctCutCost (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ) :
    LctState α σ τ × ℕ × ℕ :=
  if u == 0 || v == 0 || u == v || st.n < u || st.n < v then (st, 0, 1)
  else
    let res1 := lctRerootCost P st u
    let st1 := res1.1
    let res2 := lctExposeCost P st1 v
    let st2 := res2.1
    if (st2.splay.nodes v).sz != 3 then
      (st2, res1.2.1 + res2.2.1, res1.2.2 + res2.2.2 + 1)
    else
      let l0 := (st2.splay.nodes v).left
      let s_pd := SplayState.pushDown P st2.splay l0
      let st_pd : LctState α σ τ := { n := st2.n, splay := s_pd, freeHead := st2.freeHead }
      let r0 := (s_pd.nodes l0).right
      let u_cand := if r0 == 0 then (s_pd.nodes l0).left else l0
      let ne := if r0 == 0 then l0 else r0
      if u_cand != u then
        (st_pd, res1.2.1 + res2.2.1, res1.2.2 + res2.2.2 + 1)
      else
        let s_cut := SplayState.splay P s_pd (2 * st.n + 1) ne
        let d_cut := splayDepth s_pd (2 * st.n + 1) ne
        let s_det := SplayState.detachRootChildren P s_cut ne
        let s_fin := s_det.setPar ne st_pd.freeHead
        let st' : LctState α σ τ := { n := st.n, splay := s_fin, freeHead := ne }
        (st', res1.2.1 + res2.2.1 + d_cut / 2, res1.2.2 + res2.2.2 + d_cut + 2)

/-- Functional wrapper for `lctCutCost`. -/
private theorem nodup_length_le_of_subset {α : Type*} [DecidableEq α] {l₁ l₂ : List α}
    (hnd : l₁.Nodup) (hsub : ∀ x ∈ l₁, x ∈ l₂) : l₁.length ≤ l₂.length := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a rest ih =>
      rw [List.nodup_cons] at hnd
      have ha : a ∈ l₂ := hsub a List.mem_cons_self
      have hih := ih hnd.2 (fun x hx =>
        (List.mem_erase_of_ne (by rintro rfl; exact hnd.1 hx)).mpr (hsub x (List.mem_cons_of_mem a hx)))
      have hlen := List.length_erase_of_mem ha
      have hpos := List.length_pos_of_mem ha
      simp only [List.length_cons]
      omega

private theorem reaches_three_chain {par : ℕ → ℕ} {u ne v : ℕ}
    (hpv : par v = ne) (hpne : par ne = u) (hpu : par u = 0)
    (hne0 : ne ≠ 0) (hu0 : u ≠ 0) (k z : ℕ) :
    reaches par (k + 3) z v = (v == z || ne == z || u == z) := by
  have hs1 : reaches par (k + 3) z v = if v == z then true else reaches par (k + 2) z ne := by
    rw [show k + 3 = (k + 2) + 1 by omega, reaches]
    simp [hpv, beq_false_of_ne hne0]
  have hs2 : reaches par (k + 2) z ne = if ne == z then true else reaches par (k + 1) z u := by
    rw [show k + 2 = (k + 1) + 1 by omega, reaches]
    simp [hpne, beq_false_of_ne hu0]
  have hs3 : reaches par (k + 1) z u = (u == z) := by
    rw [reaches]
    by_cases h : u = z <;> simp [hpu, h]
  rw [hs1, hs2, hs3]
  by_cases h1 : v = z
  · simp [h1]
  · have hb1 : (v == z) = false := beq_false_of_ne h1
    by_cases h2 : ne = z
    · simp [hb1, h2]
    · have hb2 : (ne == z) = false := beq_false_of_ne h2
      simp [hb1, hb2]

def lctCut (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ) : LctState α σ τ :=
  (lctCutCost P st u v).1

open Classical in
theorem lctCut_spec {P : LctPayload α σ τ} (hL : P.Laws)
    {st : LctState α σ τ} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith P st trees freeList depth) (u v : ℕ) :
    let res := lctCutCost P st u v
    let st' := res.1
    let halves := res.2.1
    let iters := res.2.2
    let active := trees.flatMap AuxTree.toList
    let par := inducedSubPar P st.splay trees
    let st1 := (lctRerootCost P st u).1
    halves + sumTreePhi P st' ≤ sumTreePhi P st + 15 * Nat.log 2 (2 * st.n + 1) ∧
    iters + heavyCount P st' ≤ heavyCount P st + 5 * Nat.log 2 (2 * st.n + 1) + 10 ∧
    (if _hAdj : isVertex st.n u ∧ isVertex st.n v ∧ u ≠ v ∧
        ∃ ne ∈ active, (par v = ne ∧ par ne = u) ∨ (par u = ne ∧ par ne = v)
     then
       ∃ trees1 depth1 ne eVal trees' depth',
         LctInvWith P st1 trees1 freeList depth1 ∧
         LctInvWith P st' trees' (ne :: freeList) depth' ∧
         isEdgeSlot st.n ne ∧ ne ∈ active ∧
         ((par v = ne ∧ par ne = u) ∨ (par u = ne ∧ par ne = v)) ∧
         inducedSubPar P st1.splay trees1 v = ne ∧
         inducedSubPar P st1.splay trees1 ne = u ∧
         inducedSubPar P st1.splay trees1 u = 0 ∧
         (trees1.flatMap AuxTree.toList).Perm active ∧
         (ne :: trees'.flatMap AuxTree.toList).Perm active ∧
         inducedSubPar P st'.splay trees' u = 0 ∧
         inducedSubPar P st'.splay trees' v = 0 ∧
         (∀ z ∉ [u, ne, v], inducedSubPar P st'.splay trees' z = inducedSubPar P st1.splay trees1 z) ∧
         ((ne, eVal) :: forestPairs P st'.splay trees').Perm (forestPairs P st1.splay trees1)
     else
       (st' = st ∨
         (∃ trees1 depth1 trees' depth',
           LctInvWith P st1 trees1 freeList depth1 ∧
           LctInvWith P st' trees' freeList depth' ∧
           (trees1.flatMap AuxTree.toList).Perm active ∧
           (trees'.flatMap AuxTree.toList).Perm active ∧
           (∀ z, inducedSubPar P st'.splay trees' z = inducedSubPar P st1.splay trees1 z) ∧
           (forestPairs P st'.splay trees').Perm (forestPairs P st1.splay trees1)))) := by
  intro res st' halves iters active par st1
  by_cases hvalid : 1 ≤ u ∧ 1 ≤ v ∧ u ≠ v ∧ u ≤ st.n ∧ v ≤ st.n
  · rcases hvalid with ⟨hu1, hv1, huv, hu_le, hv_le⟩
    have hu0 : u ≠ 0 := by omega
    have hv0 : v ≠ 0 := by omega
    have hu_v : isVertex st.n u := ⟨hu1, hu_le⟩
    have hv_v : isVertex st.n v := ⟨hv1, hv_le⟩
    have hcond_false : (u == 0 || v == 0 || u == v || st.n < u || st.n < v) = false := by
      simp [hu0, hv0, huv, Nat.not_lt_of_ge hu_le, Nat.not_lt_of_ge hv_le]
    have hu_act : u ∈ active := isVertex_mem_active W hu_v
    have hv_act : v ∈ active := isVertex_mem_active W hv_v
    obtain ⟨tu0, htu0, hu0_mem⟩ := List.mem_flatMap.mp hu_act
    rcases lctReroot_spec hL W htu0 hu0_mem hu_v with
      ⟨trees1, Lu, depth1, ht1_mem, hW1, hact1_perm, _, hpar_u1, hreach_u1, hrev_out1, hrev_swap1,
        _, _, _, _, _, _, _, hpot1, hH1⟩
    let res1 := lctRerootCost P st u
    have hst1_n : st1.n = st.n := lctRerootCost_n P st u
    have hst1_fh : st1.freeHead = st.freeHead := lctRerootCost_freeHead P st u
    have hv_act1 : v ∈ trees1.flatMap AuxTree.toList := hact1_perm.symm.mem_iff.mp hv_act
    obtain ⟨tv1, htv1, hv1_mem⟩ := List.mem_flatMap.mp hv_act1
    rcases lctExpose_spec hL hW1 htv1 hv1_mem with
      ⟨trees2, Lv, ht2_mem, hW2, hact2_perm, hpar2, hpairs2, hpp_v2, hr_v2, hrev_v2, htag_v2,
        hreach2, _, hpot2, hH2⟩
    let res2 := lctExposeCost P st1 v
    let st2 := res2.1
    let t_exp := AuxTree.node v Lv .leaf
    have hst2_n : st2.n = st.n := (lctExposeCost_n P st1 v).trans hst1_n
    have hst2_fh : st2.freeHead = st.freeHead := (lctExposeCost_freeHead P st1 v).trans hst1_fh
    have ht2_inv := hW2.treesInv t_exp ht2_mem
    have hsz_v : (st2.splay.nodes v).sz = 1 + Lv.countNodes := by
      have h := ht2_inv.sub.2.2.2.2.2.1
      simpa [t_exp, AuxTree.countNodes] using h
    have hadj_iff := reroot_adj_iff W hu_v hv_v huv ht1_mem hW1 hact1_perm hpar_u1
      hreach_u1 hrev_out1 hrev_swap1
    have hsz3_of_adj : ∀ ne ∈ active,
        inducedSubPar P st1.splay trees1 v = ne →
        inducedSubPar P st1.splay trees1 ne = u →
        t_exp.toList.Perm [u, ne, v] := by
      intro ne hne_act hp1v hp1ne
      have hne_act1 : ne ∈ trees1.flatMap AuxTree.toList := hact1_perm.symm.mem_iff.mp hne_act
      have hne_nz : ne ≠ 0 := by have := (W.activeValid ne hne_act).1; omega
      have h1_e : isEdgeSlot st1.n ne :=
        hp1v ▸ hW1.vertexParEdge v (hst1_n ▸ hv_v) (by rw [hp1v]; exact hne_nz)
      have hne_ne_v : ne ≠ v := fun h => not_vertex_and_edge ⟨hst1_n ▸ hv_v, h ▸ h1_e⟩
      have hne_ne_u : ne ≠ u := fun h => not_vertex_and_edge ⟨hst1_n ▸ hu_v, h ▸ h1_e⟩
      have hnd3 : ([u, ne, v] : List ℕ).Nodup := by simp [hne_ne_u.symm, huv, hne_ne_v]
      have hlen1_ge : 3 ≤ (trees1.flatMap AuxTree.toList).length := by
        have hle := nodup_length_le_of_subset hnd3 (fun z hz => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl | rfl
          · exact hact1_perm.symm.mem_iff.mp hu_act
          · exact hne_act1
          · exact hv_act1)
        simpa using hle
      have hreach_fn : ∀ z, z ∈ t_exp.toList ↔ z ∈ [u, ne, v] := by
        intro z
        rw [hreach2 z]
        have hu0 : u ≠ 0 := isVertex_ne_zero hu_v
        rcases Nat.exists_eq_add_of_le' hlen1_ge with ⟨k, hk⟩
        rw [hk, reaches_three_chain hp1v hp1ne hpar_u1 hne_nz hu0 k z]
        simp only [Bool.or_eq_true, beq_iff_eq, List.mem_cons, List.not_mem_nil, or_false]
        exact ⟨fun h => by rcases h with (h | h) | h <;> simp [h],
          fun h => by rcases h with h | h | h <;> simp [h]⟩
      have hperm_3 : t_exp.toList.Perm [u, ne, v] := by
        refine List.perm_iff_count.mpr fun a => ?_
        by_cases ha : a ∈ t_exp.toList
        · have ha2 : a ∈ [u, ne, v] := (hreach_fn a).mp ha
          rw [List.count_eq_one_of_mem ht2_inv.nodup ha, List.count_eq_one_of_mem hnd3 ha2]
        · have ha2 : a ∉ [u, ne, v] := fun h => ha ((hreach_fn a).mpr h)
          rw [List.count_eq_zero_of_not_mem ha, List.count_eq_zero_of_not_mem ha2]
      exact hperm_3
    by_cases hsz3 : (st2.splay.nodes v).sz = 3
    · have hsz3_beq : ((st2.splay.nodes v).sz != 3) = false := by simp [hsz3]
      have hLv_cnt : Lv.countNodes = 2 := by omega
      have hLv_ne : Lv ≠ .leaf := fun h => by subst h; simp [AuxTree.countNodes] at hLv_cnt
      have hl0_eq : (st2.splay.nodes v).left = Lv.rootId := by
        simpa [hrev_v2] using ht2_inv.sub.2.1
      let l0 := (st2.splay.nodes v).left
      have hl0_in_Lv : l0 ∈ Lv.toList := by
        dsimp [l0]; rw [hl0_eq]; exact AuxTree.rootId_mem hLv_ne
      have hl0_in_exp : l0 ∈ t_exp.toList := by simp [t_exp, AuxTree.toList, hl0_in_Lv]
      let s_pd := SplayState.pushDown P st2.splay l0
      let st_pd : LctState α σ τ := { n := st2.n, splay := s_pd, freeHead := st2.freeHead }
      let t_pd := SplayState.pushDownTree st2.splay l0 t_exp
      rcases SplayState.pushDown_preserves_TreeInv hL ht2_inv hl0_in_exp with
        ⟨ht_pd_inv, ht_pd_perm, ht_pd_rt, _, _, hpd_sizes, hpd_rev, hpd_tag, hpd_out_sub,
          hpd_ppar, hpd_out, hpd_ev⟩
      have ht_pd_ne : t_pd ≠ .leaf := by
        intro h
        have h1 := ht_pd_perm.length_eq
        change t_pd.toList.length = t_exp.toList.length at h1
        rw [h] at h1
        simp [t_exp, AuxTree.toList] at h1
      have hpd_rep := replaceSameIds_spec hW2 ht2_mem ht_pd_ne ht_pd_inv ht_pd_perm hpd_ev hpd_ppar hpd_out
      rcases hpd_rep with ⟨hW_pd, hH_pd, hPhi_pd, hpar_pd_act⟩
      let trees_pd := t_pd :: trees2.erase t_exp
      have hpar_pd : ∀ z, inducedSubPar P s_pd trees_pd z = inducedSubPar P st2.splay trees2 z := by
        intro z
        by_cases hz : z ∈ trees_pd.flatMap AuxTree.toList
        · exact hpar_pd_act z hz
        · have hz2 : z ∉ trees2.flatMap AuxTree.toList := fun hm =>
            hz ((flatMap_perm_of_replace ht2_mem ht_pd_perm).symm.mem_iff.mp hm)
          rw [inducedSubPar_eq_zero_of_not_mem hz, inducedSubPar_eq_zero_of_not_mem hz2]
      have hpairs_pd : (forestPairs P s_pd trees_pd).Perm (forestPairs P st2.splay trees2) :=
        forestPairs_perm_cons_erase ht2_mem rfl hpd_ev hpd_out hW2.activeNodup
      have hv_nout_find : v ∉ (t_exp.findSubtree l0).toList := by
        have hv_ne_l0 : v ≠ l0 := fun h => by
          have hnd_e := ht2_inv.nodup
          have heq_l : t_exp.toList = Lv.toList ++ [v] := by simp [t_exp, AuxTree.toList]
          rw [heq_l, List.nodup_append] at hnd_e
          exact hnd_e.2.2 l0 hl0_in_Lv v (by simp) h.symm
        intro hm
        have hdx : t_exp.depthOf l0 ≠ 0 := fun h0 =>
          hv_ne_l0 ((AuxTree.depthOf_zero_iff_root hl0_in_exp).mp h0).symm
        have hdv : t_exp.depthOf v = 0 := by simp [t_exp, AuxTree.depthOf]
        exact AuxTree.not_mem_findSubtree_of_ancestor ht2_inv.nodup (by simp [t_exp, AuxTree.toList])
          hl0_in_exp (Nat.lt_of_le_of_lt (Nat.le_of_eq hdv) (Nat.pos_of_ne_zero hdx))
          (AuxTree.self_mem_pathTo (by simp [t_exp, AuxTree.toList])) hm
      have hv_node_pd : s_pd.nodes v = st2.splay.nodes v := hpd_out_sub v hv_nout_find
      have ht_pd_cnt : t_pd.countNodes = 3 := by
        have hlen_pd := ht_pd_perm.length_eq
        change t_pd.toList.length = t_exp.toList.length at hlen_pd
        rw [countNodes_eq_toList_length, hlen_pd]
        simp [t_exp, AuxTree.toList, ← countNodes_eq_toList_length, hLv_cnt]
      obtain ⟨Lp, Rp, ht_pd_eq⟩ : ∃ Lp Rp : AuxTree, t_pd = .node v Lp Rp := by
        cases h_pd : t_pd with
        | leaf => exact absurd h_pd ht_pd_ne
        | node y Lp Rp =>
            have hy : y = v := by
              have hrt := ht_pd_rt
              dsimp only [t_pd, t_exp] at h_pd hrt
              rw [h_pd] at hrt
              simpa [AuxTree.rootId] using hrt
            exact ⟨Lp, Rp, by rw [hy]⟩
      have hRp_leaf : Rp = .leaf := by
        have hsub := ht_pd_inv.sub
        change SplayState.SubtreeInv P s_pd 0 t_pd at hsub
        rw [ht_pd_eq] at hsub
        have hrr := hsub.2.2.1
        rw [hv_node_pd, hr_v2] at hrr
        cases Rp with
        | leaf => rfl
        | node y _ _ => exact absurd hrr.symm hsub.2.2.2.2.2.2.2.2.1
      have hLp_rt : Lp.rootId = l0 := by
        have hsub := ht_pd_inv.sub
        change SplayState.SubtreeInv P s_pd 0 t_pd at hsub
        rw [ht_pd_eq] at hsub
        have hlr := hsub.2.1
        rw [hv_node_pd] at hlr
        exact hlr.symm
      have hLp_cnt : Lp.countNodes = 2 := by
        rw [ht_pd_eq, hRp_leaf] at ht_pd_cnt
        simp [AuxTree.countNodes] at ht_pd_cnt
        omega
      rcases two_nodes_decomp hLp_rt hLp_cnt with ⟨L1, R1, hLp_eq, hcases⟩
      let r0 := (s_pd.nodes l0).right
      let u_cand := if r0 == 0 then (s_pd.nodes l0).left else l0
      let ne := if r0 == 0 then l0 else r0
      have hids_pd : treeIds P s_pd t_pd = [u_cand, ne, v] := by
        have hsub_pd := ht_pd_inv.sub
        change SplayState.SubtreeInv P s_pd 0 t_pd at hsub_pd
        rw [ht_pd_eq, hRp_leaf, hLp_eq] at hsub_pd
        have hv_rev_pd : (s_pd.nodes v).rev = false := by rw [hv_node_pd]; exact hrev_v2
        have hv_tag_pd : (s_pd.nodes v).tag = P.idTag := by rw [hv_node_pd]; exact htag_v2
        have hev_top := evalPairs_node_rev_false hL hv_rev_pd hv_tag_pd
          (s := s_pd) (x := v) (l := .node l0 L1 R1) (r := .leaf)
        have hev_Lp := evalPairs_node_rev_false hL hpd_rev hpd_tag
          (s := s_pd) (x := l0) (l := L1) (r := R1)
        rcases hcases with ⟨rfl, b, rfl⟩ | ⟨rfl, a, rfl⟩
        · have hb_r0 : r0 = b := by
            have := hsub_pd.2.2.2.2.2.2.2.1.2.2.1
            simpa [r0, hpd_rev, AuxTree.rootId] using this
          have hb_nz : b ≠ 0 := by
            have hmem_b : b ∈ t_pd.toList := by simp [ht_pd_eq, hLp_eq, AuxTree.toList]
            exact SplayState.SubtreeInv_nonZero ht_pd_inv.sub hmem_b
          have huc : u_cand = l0 := by simp [u_cand, hb_r0, hb_nz]
          have hne_eq : ne = b := by simp [ne, hb_r0, hb_nz]
          have hb_ev : (SplayState.evalPairs P s_pd (.node b .leaf .leaf) false P.idTag).map Prod.fst = [b] := by
            simp only [SplayState.evalPairs]
            split_ifs <;> simp
          simp only [treeIds]
          rw [ht_pd_eq, hRp_leaf, hLp_eq, hev_top, hev_Lp]
          simp [SplayState.evalPairs, huc, hne_eq]
        · have hr0_zero : r0 = 0 := by
            have := hsub_pd.2.2.2.2.2.2.2.1.2.2.1
            simpa [r0, hpd_rev, AuxTree.rootId] using this
          have ha_l0 : (s_pd.nodes l0).left = a := by
            have := hsub_pd.2.2.2.2.2.2.2.1.2.1
            simpa [hpd_rev, AuxTree.rootId] using this
          have huc : u_cand = a := by simp [u_cand, hr0_zero, ha_l0]
          have hne_eq : ne = l0 := by simp [ne, hr0_zero]
          simp only [treeIds]
          rw [ht_pd_eq, hRp_leaf, hLp_eq, hev_top, hev_Lp]
          simp [SplayState.evalPairs, huc, hne_eq]
      have hpar_v_ne : inducedSubPar P st1.splay trees1 v = ne := by
        have hp2 := inducedSubPar_eq_of_mem (P := P) (s := s_pd) hW_pd.activeNodup (List.mem_cons_self)
          ((mem_treeIds_iff P s_pd t_pd v).mp (by rw [hids_pd]; simp))
        have hpp_v_pd : (s_pd.nodes t_pd.rootId).ppar = 0 := by
          rw [hpd_ppar]
          simpa [t_exp, AuxTree.rootId] using hpp_v2
        rw [← hpar2 v, ← hpar_pd v, hp2, hids_pd, hpp_v_pd]
        have hnd3 : ([u_cand, ne, v] : List ℕ).Nodup :=
          ((treeIds_perm s_pd t_pd).symm.trans (by rw [hids_pd])).nodup_iff.mp ht_pd_inv.nodup
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd3
        simp [chainPred, Ne.symm hnd3.1.2, Ne.symm hnd3.2.1]
      have hpar_ne_uc : inducedSubPar P st1.splay trees1 ne = u_cand := by
        have hp2 := inducedSubPar_eq_of_mem (P := P) (s := s_pd) hW_pd.activeNodup (List.mem_cons_self)
          ((mem_treeIds_iff P s_pd t_pd ne).mp (by rw [hids_pd]; simp))
        have hpp_v_pd : (s_pd.nodes t_pd.rootId).ppar = 0 := by
          rw [hpd_ppar]
          simpa [t_exp, AuxTree.rootId] using hpp_v2
        rw [← hpar2 ne, ← hpar_pd ne, hp2, hids_pd, hpp_v_pd]
        have hnd3 : ([u_cand, ne, v] : List ℕ).Nodup :=
          ((treeIds_perm s_pd t_pd).symm.trans (by rw [hids_pd])).nodup_iff.mp ht_pd_inv.nodup
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd3
        simp [chainPred, Ne.symm hnd3.1.1]
      have hne_act : ne ∈ active := by
        have hm := (mem_treeIds_iff P s_pd t_pd ne).mp (by rw [hids_pd]; simp)
        exact hact1_perm.mem_iff.mp (hact2_perm.mem_iff.mp
          ((flatMap_perm_of_replace ht2_mem ht_pd_perm).mem_iff.mp
            (List.mem_flatMap.mpr ⟨t_pd, List.mem_cons_self, hm⟩)))
      by_cases huc_eq : u_cand = u
      · have hpar_ne_u : inducedSubPar P st1.splay trees1 ne = u := huc_eq ▸ hpar_ne_uc
        have huc_false : (u_cand != u) = false := by simp [huc_eq]
        have hne_mem_pd : ne ∈ t_pd.toList :=
          (mem_treeIds_iff P s_pd t_pd ne).mp (by rw [hids_pd]; simp)
        rcases lctSplayTree_spec hL hW_pd List.mem_cons_self hne_mem_pd with
          ⟨t_cut, ht_cut_ne, ht_cut_rt, ht_cut_perm, hcut_ppar, hcut_rev, hcut_tag,
            hW_cut, hH_cut, hpairs_cut, hpar_cut, _, hev_cut_eq, htsz_cut_eq, _, hpot_cut⟩
        let s_cut := SplayState.splay P s_pd (2 * st_pd.n + 1) ne
        let trees_cut := t_cut :: trees_pd.erase t_pd
        let d_cut := splayDepth s_pd (2 * st_pd.n + 1) ne
        have hst_pd_n : st_pd.n = st.n := hst2_n
        have ht_cut_mem : t_cut ∈ trees_cut := List.mem_cons_self
        have ht_cut_inv := hW_cut.treesInv t_cut ht_cut_mem
        obtain ⟨Lcut, Rcut, ht_cut_eq⟩ : ∃ Lcut Rcut, t_cut = .node ne Lcut Rcut := by
          cases t_cut with
          | leaf => exact absurd rfl ht_cut_ne
          | node y Lcut Rcut =>
              simp only [AuxTree.rootId] at ht_cut_rt
              exact ⟨Lcut, Rcut, by rw [ht_cut_rt]⟩
        have hids_cut : treeIds P s_cut t_cut = [u, ne, v] := by
          dsimp only [treeIds]
          rw [hev_cut_eq]
          change treeIds P s_pd t_pd = [u, ne, v]
          rw [hids_pd, huc_eq]
        have hcut_shape := evalPairs_split_three_of_node hL
          (ht_cut_eq ▸ ht_cut_inv) hcut_rev hcut_tag (ht_cut_eq ▸ hids_cut)
        have ht_cut_node : AuxTree.node ne (.node u .leaf .leaf) (.node v .leaf .leaf) ∈ trees_cut := by
          rw [ht_cut_eq, hcut_shape.1, hcut_shape.2] at ht_cut_mem
          exact ht_cut_mem
        have he_slot : isEdgeSlot st.n ne := by
          rw [← hst1_n]
          have hne_nz' : ne ≠ 0 := by have := (W.activeValid ne hne_act).1; omega
          exact hpar_v_ne ▸ hW1.vertexParEdge v (hst1_n ▸ hv_v) (by rw [hpar_v_ne]; exact hne_nz')
        have hcut_pp0 : (s_cut.nodes ne).ppar = 0 := by
          rw [hcut_ppar, hpd_ppar]
          simpa [t_exp, AuxTree.rootId] using hpp_v2
        have he_slot_cut : isEdgeSlot (LctState.mk st_pd.n s_cut st_pd.freeHead).n ne := by
          simpa [hst_pd_n] using he_slot
        rcases cut_splice_spec hL hW_cut ht_cut_node hcut_rev hcut_tag hcut_pp0 he_slot_cut with
          ⟨hW_fin, hPhi_fin, hH_fin, hpar'_u, hpar'_v, hpar'_oth⟩
        let s_det := SplayState.detachRootChildren P s_cut ne
        let s_fin := s_det.setPar ne st_pd.freeHead
        let trees' := AuxTree.node u .leaf .leaf :: AuxTree.node v .leaf .leaf ::
          trees_cut.erase (.node ne (.node u .leaf .leaf) (.node v .leaf .leaf))
        have hres_cut : res = (LctState.mk st.n s_fin ne,
            res1.2.1 + res2.2.1 + d_cut / 2, res1.2.2 + res2.2.2 + d_cut + 2) := by
          simp only [res, lctCutCost, hcond_false, Bool.false_eq_true, ↓reduceIte,
            hsz3_beq, l0, s_pd, st_pd, r0, u_cand, ne, huc_false, s_cut, d_cut,
            s_det, s_fin, res1, res2, st1, st2, hst2_n]
        have hst'_eq : st' = LctState.mk st.n s_fin ne := congrArg Prod.fst hres_cut
        have hst_mk_eq : LctState.mk st_pd.n s_fin ne = st' := by
          rw [hst'_eq, hst_pd_n]
        have hW_fin' : LctInvWith P st' trees' (ne :: freeList) depth1 := by
          rw [← hst_mk_eq]
          exact hW_fin
        have hd_cut_lt : d_cut < 3 := by
          have hdl : t_pd.depthOf ne < 3 := by
            have h1 := SplayState.depthOf_lt_countNodes hne_mem_pd
            rw [ht_pd_cnt] at h1
            exact h1
          have hlt_k : t_pd.depthOf ne < 2 * st_pd.n + 1 := by omega
          have hdep_eq : splayDepth s_pd (2 * st_pd.n + 1) ne = t_pd.depthOf ne :=
            splayDepth_eq_depthOf (hW_pd.treesInv t_pd List.mem_cons_self) hne_mem_pd hlt_k
          change splayDepth s_pd (2 * st_pd.n + 1) ne < 3
          omega
        have hrank_cut_le : t_cut.rank (vSize P s_pd (trees_pd.flatMap AuxTree.toList)
            (inducedSubPar P s_pd trees_pd) trees_pd) ≤ Nat.log 2 (2 * st.n + 1) := by
          have htsz_le : t_cut.treeSize (vSize P s_pd (trees_pd.flatMap AuxTree.toList)
              (inducedSubPar P s_pd trees_pd) trees_pd) ≤ 2 * st.n := by
            have ht_pd_rep := treeSize_vSize_eq_repSize hW_pd (List.mem_cons_self : t_pd ∈ trees_pd)
            have hact_pd_le := active_length_le_two_mul hW_pd.activeNodup hW_pd.activeValid
            rw [hst_pd_n] at hact_pd_le
            rw [htsz_cut_eq, ht_pd_rep]
            exact (repSize_le_active _).trans hact_pd_le
          exact Nat.log_mono_right (Nat.le_succ_of_le htsz_le)
        have hphi_fin : halves + sumTreePhi P st' ≤ sumTreePhi P st + 15 * Nat.log 2 (2 * st.n + 1) := by
          have hhalves_eq : halves = res1.2.1 + res2.2.1 + d_cut / 2 := congrArg (fun p => p.2.1) hres_cut
          have hPhi_st' : sumTreePhi P st' ≤ sumTreePhi P (LctState.mk st_pd.n s_cut st_pd.freeHead) := by
            rw [hst'_eq, ← hst_pd_n]
            exact hPhi_fin
          have hPhi_pd' : sumTreePhi P st_pd = sumTreePhi P st2 := by
            have hv_eq := (hpd_sizes (vSize P st2.splay (trees2.flatMap AuxTree.toList)
              (inducedSubPar P st2.splay trees2) trees2)).2.1
            have hPhi_pd0 := hPhi_pd
            change sumTreePhi P st_pd +
                t_exp.treePhi (vSize P st2.splay (trees2.flatMap AuxTree.toList)
                  (inducedSubPar P st2.splay trees2) trees2) =
                sumTreePhi P st2 +
                t_pd.treePhi (vSize P st2.splay (trees2.flatMap AuxTree.toList)
                  (inducedSubPar P st2.splay trees2) trees2) at hPhi_pd0
            rw [hv_eq] at hPhi_pd0
            omega
          have hpot1' : res1.2.1 + sumTreePhi P st1 ≤ sumTreePhi P st + 6 * Nat.log 2 (2 * st.n + 1) := hpot1
          have hpot2' : res2.2.1 + sumTreePhi P st2 ≤ sumTreePhi P st1 + 6 * Nat.log 2 (2 * st.n + 1) := by
            have h2 := hpot2
            change res2.2.1 + sumTreePhi P st2 ≤ sumTreePhi P st1 + 6 * Nat.log 2 (2 * st1.n + 1) at h2
            rw [hst1_n] at h2
            exact h2
          have hpot_cut0 : d_cut / 2 + sumTreePhi P (LctState.mk st_pd.n s_cut st_pd.freeHead) +
              3 * (t_pd.findSubtree ne).rank (vSize P s_pd (trees_pd.flatMap AuxTree.toList)
                (inducedSubPar P s_pd trees_pd) trees_pd) ≤
              sumTreePhi P st_pd + 3 * t_cut.rank (vSize P s_pd (trees_pd.flatMap AuxTree.toList)
                (inducedSubPar P s_pd trees_pd) trees_pd) := hpot_cut
          have hrank_cut_le' : t_cut.rank (vSize P s_pd (trees_pd.flatMap AuxTree.toList)
              (inducedSubPar P s_pd trees_pd) trees_pd) ≤ Nat.log 2 (2 * st.n + 1) := hrank_cut_le
          have hpot_cut' : d_cut / 2 + sumTreePhi P (LctState.mk st_pd.n s_cut st_pd.freeHead) ≤
              sumTreePhi P st_pd + 3 * Nat.log 2 (2 * st.n + 1) := by
            omega
          rw [hhalves_eq]
          omega
        have hH_fin : iters + heavyCount P st' ≤ heavyCount P st + 5 * Nat.log 2 (2 * st.n + 1) + 10 := by
          have hiters_eq : iters = res1.2.2 + res2.2.2 + d_cut + 2 := congrArg (fun p => p.2.2) hres_cut
          have hH_st' : heavyCount P st' ≤ heavyCount P (LctState.mk st_pd.n s_cut st_pd.freeHead) + 1 := by
            rw [hst'_eq, ← hst_pd_n]
            exact hH_fin
          have hH_pd' : heavyCount P st_pd = heavyCount P st2 := hH_pd
          have hH_cut' : heavyCount P (LctState.mk st_pd.n s_cut st_pd.freeHead) = heavyCount P st_pd :=
            hH_cut
          have hH1' : res1.2.2 + heavyCount P st1 ≤ heavyCount P st + 3 * Nat.log 2 (2 * st.n + 1) + 3 := hH1
          have hH2' : res2.2.2 + heavyCount P st2 ≤ heavyCount P st1 + 2 * Nat.log 2 (2 * st.n + 1) + 2 := by
            have h2 := hH2
            change res2.2.2 + heavyCount P st2 ≤ heavyCount P st1 + 2 * Nat.log 2 (2 * st1.n + 1) + 2 at h2
            rw [hst1_n] at h2
            exact h2
          rw [hiters_eq]
          omega
        have hpairs_cut_fin : ((ne, (s_cut.nodes ne).val) :: forestPairs P st'.splay trees').Perm
            (forestPairs P st1.splay trees1) := by
          have ht_cut_inv_node : SplayState.TreeInv P s_cut (.node ne (.node u .leaf .leaf) (.node v .leaf .leaf)) := by
            simpa [ht_cut_eq, hcut_shape.1, hcut_shape.2] using ht_cut_inv
          have hsub_cut := ht_cut_inv_node.sub
          have hl_cut : (s_cut.nodes ne).left = u := by
            simpa [hcut_rev, AuxTree.rootId] using hsub_cut.2.1
          have hr_cut : (s_cut.nodes ne).right = v := by
            simpa [hcut_rev, AuxTree.rootId] using hsub_cut.2.2.1
          have hne_nz : ne ≠ 0 := by have := (W.activeValid ne hne_act).1; omega
          have hdet_uv := evalPairs_detachRootChildren_setPar_other (P := P) (s := s_cut)
            (w := st_pd.freeHead) hne_nz (fun h => not_vertex_and_edge ⟨hu_v, by rw [h]; exact he_slot⟩)
            (fun h => not_vertex_and_edge ⟨hv_v, by rw [h]; exact he_slot⟩) huv hl_cut hr_cut hu0 hv0
          have hev_u_eq : SplayState.evalPairs P s_fin (.node u .leaf .leaf) false P.idTag =
              SplayState.evalPairs P s_cut (.node u .leaf .leaf) false P.idTag :=
            evalPairs_singleton_of_eq hdet_uv.1
          have hev_v_eq : SplayState.evalPairs P s_fin (.node v .leaf .leaf) false P.idTag =
              SplayState.evalPairs P s_cut (.node v .leaf .leaf) false P.idTag :=
            evalPairs_singleton_of_eq hdet_uv.2
          have hout_cut : ∀ w ∈ (trees_cut.erase (.node ne (.node u .leaf .leaf) (.node v .leaf .leaf))).flatMap AuxTree.toList,
              s_fin.nodes w = s_cut.nodes w := fun w hw => by
            have hdisj := erase_flatMap_disjoint_of_nodup ht_cut_node hW_cut.activeNodup w hw
            have hdet_out := (SplayState.detachRootChildren_preserves hL ht_cut_inv_node hcut_rev hcut_tag).2.2.2.2.2.2 w
              (by simpa [AuxTree.toList] using hdisj)
            have hw_ne : w ≠ ne := fun h => hdisj (by simp [AuxTree.toList, h])
            simp [s_fin, s_det, SplayState.setPar, hw_ne, hdet_out]
          have hp_er_eq : forestPairs P s_fin (trees_cut.erase (.node ne (.node u .leaf .leaf) (.node v .leaf .leaf))) =
              forestPairs P s_cut (trees_cut.erase (.node ne (.node u .leaf .leaf) (.node v .leaf .leaf))) := by
            apply forestPairs_congr_trees
            intro c hc
            exact SplayState.evalPairs_agree P (fun w hw => hout_cut w (List.mem_flatMap.mpr ⟨c, hc, hw⟩)) false P.idTag
          have hev_tcut : SplayState.evalPairs P s_cut (.node ne (.node u .leaf .leaf) (.node v .leaf .leaf)) false P.idTag =
              SplayState.evalPairs P s_cut (.node u .leaf .leaf) false P.idTag ++
              [(ne, (s_cut.nodes ne).val)] ++
              SplayState.evalPairs P s_cut (.node v .leaf .leaf) false P.idTag :=
            evalPairs_node_rev_false hL hcut_rev hcut_tag
          have hp_fin_cut : ((ne, (s_cut.nodes ne).val) :: forestPairs P st'.splay trees').Perm (forestPairs P s_cut trees_cut) := by
            have hst_splay : st'.splay = s_fin := by rw [hst'_eq]
            rw [hst_splay]
            dsimp only [trees', forestPairs]
            rw [List.flatMap_cons, List.flatMap_cons, hev_u_eq, hev_v_eq]
            change ((ne, (s_cut.nodes ne).val) ::
              (SplayState.evalPairs P s_cut (.node u .leaf .leaf) false P.idTag ++
               SplayState.evalPairs P s_cut (.node v .leaf .leaf) false P.idTag ++
               forestPairs P s_fin (trees_cut.erase (.node ne (.node u .leaf .leaf) (.node v .leaf .leaf))))).Perm _
            rw [hp_er_eq]
            exact mem_forestPairs_split ht_cut_node hev_tcut
          exact hp_fin_cut.trans (hpairs_cut.trans (hpairs_pd.trans hpairs2))
        have hpar_ori : (par v = ne ∧ par ne = u) ∨ (par u = ne ∧ par ne = v) :=
          ((hadj_iff ne).mpr ⟨hne_act, hpar_v_ne, hpar_ne_u⟩).2
        have hAdj_true : isVertex st.n u ∧ isVertex st.n v ∧ u ≠ v ∧
            ∃ ne ∈ active, (par v = ne ∧ par ne = u) ∨ (par u = ne ∧ par ne = v) :=
          ⟨hu_v, hv_v, huv, ne, hne_act, hpar_ori⟩
        have hact'_perm : (ne :: trees'.flatMap AuxTree.toList).Perm active := by
          have hp_cut : (trees_cut.flatMap AuxTree.toList).Perm
              ([u, ne, v] ++ (trees_cut.erase (.node ne (.node u .leaf .leaf) (.node v .leaf .leaf))).flatMap AuxTree.toList) := by
            have h1 := flatMap_perm_of_perm (List.perm_cons_erase ht_cut_node)
            simpa [List.flatMap_cons, AuxTree.toList] using h1
          have hp_mid : (ne :: trees'.flatMap AuxTree.toList).Perm (trees_cut.flatMap AuxTree.toList) := by
            refine List.Perm.trans ?_ hp_cut.symm
            simp only [trees', List.flatMap_cons, AuxTree.toList, List.nil_append,
              List.append_nil, List.cons_append]
            exact List.Perm.swap u ne _
          have hp_to_act : (trees_cut.flatMap AuxTree.toList).Perm active :=
            (flatMap_perm_of_replace (List.mem_cons_self : t_pd ∈ trees_pd) ht_cut_perm).trans
              ((flatMap_perm_of_replace ht2_mem ht_pd_perm).trans (hact2_perm.trans hact1_perm))
          exact hp_mid.trans hp_to_act
        have hpar'_u' : inducedSubPar P st'.splay trees' u = 0 := by
          convert hpar'_u using 2
          rw [hst'_eq]
        have hpar'_v' : inducedSubPar P st'.splay trees' v = 0 := by
          convert hpar'_v using 2
          rw [hst'_eq]
        have hpar'_oth' : ∀ z ∉ [u, ne, v],
            inducedSubPar P st'.splay trees' z = inducedSubPar P st1.splay trees1 z := by
          intro z hz
          have h1 : inducedSubPar P st'.splay trees' z = inducedSubPar P s_cut trees_cut z := by
            convert hpar'_oth z hz using 2
            rw [hst'_eq]
          rw [h1, hpar_cut z, hpar_pd z, hpar2 z]
        refine ⟨hphi_fin, hH_fin, ?_⟩
        rw [dite_eq_left_of_eq_true (eq_true hAdj_true)]
        exact ⟨trees1, depth1, ne, (s_cut.nodes ne).val, trees', depth1,
          hW1, hW_fin', he_slot, hne_act, hpar_ori, hpar_v_ne, hpar_ne_u, hpar_u1,
          hact1_perm, hact'_perm, hpar'_u', hpar'_v', hpar'_oth', hpairs_cut_fin⟩
      · -- `u_cand ≠ u`: no edge `(u, v)` exists; returns `st_pd`!
        have huc_true : (u_cand != u) = true := by simp [huc_eq]
        have hres_pd : res = (st_pd, res1.2.1 + res2.2.1, res1.2.2 + res2.2.2 + 1) := by
          simp only [res, lctCutCost, hcond_false, Bool.false_eq_true, ↓reduceIte,
            hsz3_beq, l0, s_pd, st_pd, r0, u_cand, huc_true, res1, res2, st1, st2]
        have hst'_eq : st' = st_pd := congrArg Prod.fst hres_pd
        have hphi_fin : halves + sumTreePhi P st' ≤ sumTreePhi P st + 15 * Nat.log 2 (2 * st.n + 1) := by
          have hhalves_eq : halves = res1.2.1 + res2.2.1 := congrArg (fun p => p.2.1) hres_pd
          have hPhi_pd' : sumTreePhi P st_pd = sumTreePhi P st2 := by
            have hv_eq := (hpd_sizes (vSize P st2.splay (trees2.flatMap AuxTree.toList)
              (inducedSubPar P st2.splay trees2) trees2)).2.1
            have hPhi_pd0 := hPhi_pd
            change sumTreePhi P st_pd +
                t_exp.treePhi (vSize P st2.splay (trees2.flatMap AuxTree.toList)
                  (inducedSubPar P st2.splay trees2) trees2) =
                sumTreePhi P st2 +
                t_pd.treePhi (vSize P st2.splay (trees2.flatMap AuxTree.toList)
                  (inducedSubPar P st2.splay trees2) trees2) at hPhi_pd0
            rw [hv_eq] at hPhi_pd0
            omega
          have hPhi_st' : sumTreePhi P st' = sumTreePhi P st2 := by rw [hst'_eq]; exact hPhi_pd'
          have hpot1' : res1.2.1 + sumTreePhi P st1 ≤ sumTreePhi P st + 6 * Nat.log 2 (2 * st.n + 1) := hpot1
          have hpot2' : res2.2.1 + sumTreePhi P st2 ≤ sumTreePhi P st1 + 6 * Nat.log 2 (2 * st.n + 1) := by
            have h2 := hpot2
            change res2.2.1 + sumTreePhi P st2 ≤ sumTreePhi P st1 + 6 * Nat.log 2 (2 * st1.n + 1) at h2
            rw [hst1_n] at h2
            exact h2
          rw [hhalves_eq]; omega
        have hH_fin : iters + heavyCount P st' ≤ heavyCount P st + 5 * Nat.log 2 (2 * st.n + 1) + 10 := by
          have hiters_eq : iters = res1.2.2 + res2.2.2 + 1 := congrArg (fun p => p.2.2) hres_pd
          have hH_st' : heavyCount P st' = heavyCount P st2 := by rw [hst'_eq]; exact hH_pd
          have hH1' : res1.2.2 + heavyCount P st1 ≤ heavyCount P st + 3 * Nat.log 2 (2 * st.n + 1) + 3 := hH1
          have hH2' : res2.2.2 + heavyCount P st2 ≤ heavyCount P st1 + 2 * Nat.log 2 (2 * st.n + 1) + 2 := by
            have h2 := hH2
            change res2.2.2 + heavyCount P st2 ≤ heavyCount P st1 + 2 * Nat.log 2 (2 * st1.n + 1) + 2 at h2
            rw [hst1_n] at h2
            exact h2
          rw [hiters_eq]; omega
        have hn_adj : ¬ (isVertex st.n u ∧ isVertex st.n v ∧ u ≠ v ∧
            ∃ ne' ∈ active, (par v = ne' ∧ par ne' = u) ∨ (par u = ne' ∧ par ne' = v)) := by
          rintro ⟨_, _, _, ne', hne'_act, hori'⟩
          rcases (hadj_iff ne').mp ⟨hne'_act, hori'⟩ with ⟨_, h1v', h1ne'⟩
          have hne_eq : ne' = ne := h1v'.symm.trans hpar_v_ne
          rw [hne_eq, hpar_ne_uc] at h1ne'
          exact huc_eq h1ne'
        refine ⟨hphi_fin, hH_fin, ?_⟩
        rw [dite_eq_right_of_eq_false (eq_false hn_adj)]
        right
        refine ⟨trees1, depth1, trees_pd, depth1, hW1, hst'_eq ▸ hW_pd, hact1_perm,
          (flatMap_perm_of_replace ht2_mem ht_pd_perm).trans (hact2_perm.trans hact1_perm), ?_, ?_⟩
        · intro z; rw [hst'_eq]; exact (hpar_pd z).trans (hpar2 z)
        · rw [hst'_eq]; exact hpairs_pd.trans hpairs2
    · -- `(st2.splay.nodes v).sz ≠ 3`: no edge `(u, v)` exists; returns `st2`!
      have hsz3_true : ((st2.splay.nodes v).sz != 3) = true := by simp [hsz3]
      have hres2 : res = (st2, res1.2.1 + res2.2.1, res1.2.2 + res2.2.2 + 1) := by
        simp only [res, lctCutCost, hcond_false, Bool.false_eq_true, ↓reduceIte,
          hsz3_true, res1, res2, st1, st2]
      have hst'_eq : st' = st2 := (congrArg Prod.fst hres2 : res.1 = (st2, res1.2.1 + res2.2.1, res1.2.2 + res2.2.2 + 1).1)
      have hphi_fin : halves + sumTreePhi P st' ≤ sumTreePhi P st + 15 * Nat.log 2 (2 * st.n + 1) := by
        have hhalves_eq : halves = res1.2.1 + res2.2.1 := congrArg (fun p => p.2.1) hres2
        have hpot1' : res1.2.1 + sumTreePhi P st1 ≤ sumTreePhi P st + 6 * Nat.log 2 (2 * st.n + 1) := hpot1
        have hpot2' : res2.2.1 + sumTreePhi P st2 ≤ sumTreePhi P st1 + 6 * Nat.log 2 (2 * st.n + 1) := by
          have h2 := hpot2
          change res2.2.1 + sumTreePhi P st2 ≤ sumTreePhi P st1 + 6 * Nat.log 2 (2 * st1.n + 1) at h2
          rw [hst1_n] at h2
          exact h2
        rw [hhalves_eq, hst'_eq]; omega
      have hH_fin : iters + heavyCount P st' ≤ heavyCount P st + 5 * Nat.log 2 (2 * st.n + 1) + 10 := by
        have hiters_eq : iters = res1.2.2 + res2.2.2 + 1 := congrArg (fun p => p.2.2) hres2
        have hH1' : res1.2.2 + heavyCount P st1 ≤ heavyCount P st + 3 * Nat.log 2 (2 * st.n + 1) + 3 := hH1
        have hH2' : res2.2.2 + heavyCount P st2 ≤ heavyCount P st1 + 2 * Nat.log 2 (2 * st.n + 1) + 2 := by
          have h2 := hH2
          change res2.2.2 + heavyCount P st2 ≤ heavyCount P st1 + 2 * Nat.log 2 (2 * st1.n + 1) + 2 at h2
          rw [hst1_n] at h2
          exact h2
        rw [hiters_eq, hst'_eq]; omega
      have hn_adj : ¬ (isVertex st.n u ∧ isVertex st.n v ∧ u ≠ v ∧
          ∃ ne' ∈ active, (par v = ne' ∧ par ne' = u) ∨ (par u = ne' ∧ par ne' = v)) := by
        rintro ⟨_, _, _, ne', hne'_act, hori'⟩
        rcases (hadj_iff ne').mp ⟨hne'_act, hori'⟩ with ⟨_, h1v', h1ne'⟩
        have hperm3 := hsz3_of_adj ne' hne'_act h1v' h1ne'
        have hlen3 : t_exp.countNodes = 3 := by
          rw [countNodes_eq_toList_length]
          simpa using hperm3.length_eq
        dsimp only [t_exp, AuxTree.countNodes] at hlen3
        omega
      refine ⟨hphi_fin, hH_fin, ?_⟩
      rw [dite_eq_right_of_eq_false (eq_false hn_adj)]
      right
      exact ⟨trees1, depth1, trees2, depth1, hW1, hst'_eq ▸ hW2, hact1_perm,
        hact2_perm.trans hact1_perm, fun z => hst'_eq ▸ hpar2 z, hst'_eq ▸ hpairs2⟩
  · -- Invalid `u` or `v` or `u = v`: no change, returns `st`!
    have hcond_true : (u == 0 || v == 0 || u == v || st.n < u || st.n < v) = true := by
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
      omega
    have hres0 : res = (st, 0, 1) := by simp [res, lctCutCost, hcond_true]
    have hst'_eq : st' = st := congrArg Prod.fst hres0
    have hhalves0 : halves = 0 := congrArg (fun p => p.2.1) hres0
    have hiters0 : iters = 1 := congrArg (fun p => p.2.2) hres0
    have hn_adj : ¬ (isVertex st.n u ∧ isVertex st.n v ∧ u ≠ v ∧
        ∃ ne ∈ active, (par v = ne ∧ par ne = u) ∨ (par u = ne ∧ par ne = v)) := by
      rintro ⟨hu_v, hv_v, huv, _⟩
      exact hvalid ⟨hu_v.1, hv_v.1, huv, hu_v.2, hv_v.2⟩
    refine ⟨by rw [hhalves0, hst'_eq]; omega, by rw [hiters0, hst'_eq]; omega, ?_⟩
    rw [dite_eq_right_of_eq_false (eq_false hn_adj)]
    exact Or.inl hst'_eq

end MinCostFlow.LinkCut
