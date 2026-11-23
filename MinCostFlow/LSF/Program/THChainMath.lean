module

public import MinCostFlow.LSF.AuxiliaryTree

/-!
# Heavy chains, read along the tree

The program for the auxiliary tree `T_H` finds the heavy chains by one walk down the tree: a
vertex that is a heavy child is in the chain of its parent (`chainOf_heavy`), and any other
vertex is the top of its own chain (`chainTop_chainOf_self`). The list `chainList` of a chain
holds the chain from the top down, one vertex per depth: entry `k` has depth `depth top + k`
(`depth_chainList_getElem`). Two vertices of one chain with the same depth are equal
(`chain_eq_of_depth`). These facts let the program store each chain as an array indexed by the
depth below the top.
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

variable {T : MGraph} {r : ℕ}

/-- A heavy child is in the chain of its parent. -/
lemma chainOf_heavy (hT : IsRootedTree T r) {v : ℕ} (hh : IsHeavyChild T r v) :
    chainOf T r v = chainOf T r (parent T r v) :=
  compOf_eq_of_connected (heavyGraph_connected_parent hT hh)

lemma chainOf_conn {v w : ℕ} (hw : w ∈ chainOf T r v) :
    (heavyGraph T r).Connected v w := (mem_compOf_iff.mp hw).2

/-- The root, and a vertex that is not a heavy child, is the top of its chain. -/
lemma chainTop_chainOf_self (hT : IsRootedTree T r) {v : ℕ} (hv : v ∈ T.V)
    (hnh : v = r ∨ ¬ IsHeavyChild T r v) : chainTop T r (chainOf T r v) = v := by
  classical
  set P := chainOf T r v with hPdef
  have hP : P ∈ heavyChains T r := chainOf_mem_heavyChains hv
  obtain ⟨htP, htanc⟩ := chainTop_spec hT hP
  set t := chainTop T r P with htdef
  have hvP : v ∈ P := mem_chainOf_self hv
  have htv : IsAncestor T r t v := htanc v hvP
  have htV : t ∈ T.V := (heavyChain_subset hP).2 htP
  by_contra hne
  rcases hnh with hvr | hnh
  · exact hne (isAncestor_antisymm hT htV hv htv (by rw [hvr]; exact isAncestor_root hT htV))
  · apply hnh
    have hvr : v ≠ r := by
      intro hvr
      exact hne (isAncestor_antisymm hT htV hv htv (by rw [hvr]; exact isAncestor_root hT htV))
    -- the heavy path from `v` to `t` is the tree path, and it starts with the parent edge of `v`
    have hconn : (heavyGraph T r).Connected v t := chainOf_conn htP
    have hPF := forestPath_isPath (heavyGraph_isForest hT) hconn
    have hEq : (heavyGraph T r).forestPath v t = T.forestPath v t :=
      (forestPath_eq_of_isPath hT.isForest (isPath_of_subgraph (heavyGraph_isSubgraph hT) hPF)).symm
    have hpe : parentEdge T r v ∈ walkEdges (T.forestPath v t) := by
      rw [parentEdge_mem_walkEdges_ancestor_iff hT hv hvr hv htv]
      exact ⟨isAncestor_refl T r v, fun h => hne (isAncestor_antisymm hT htV hv htv h)⟩
    rw [← hEq] at hpe
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp (List.mem_toFinset.mp hpe)
    have hin : parentEdge T r v ∈ (heavyGraph T r).E := hxe ▸ IsWalk_edges_mem hPF.1 hx
    simp only [heavyGraph, Finset.mem_image, Finset.mem_filter] at hin
    obtain ⟨c, ⟨hcV, hhc⟩, hce⟩ := hin
    rw [← parentEdge_inj hT hcV hv hhc.2.1 hvr hce]
    exact hhc

/-- A vertex of a chain other than its top is a heavy child. -/
lemma heavy_of_mem_chain (hT : IsRootedTree T r) {P : Finset ℕ} (hP : P ∈ heavyChains T r)
    {u : ℕ} (hu : u ∈ P) (hne : u ≠ chainTop T r P) : IsHeavyChild T r u := by
  have huV := (heavyChain_subset hP).2 hu
  have hPu : chainOf T r u = P := chainOf_eq_of_mem hP hu
  by_contra hnh
  exact hne (by rw [← hPu]; exact (chainTop_chainOf_self hT huV (Or.inr hnh)).symm)

/-- Two vertices of one chain with the same depth are equal. -/
lemma chain_eq_of_depth (hT : IsRootedTree T r) {P : Finset ℕ} (hP : P ∈ heavyChains T r)
    {u v : ℕ} (hu : u ∈ P) (hv : v ∈ P) (hd : depth T r u = depth T r v) : u = v := by
  have huV := (heavyChain_subset hP).2 hu
  have hvV := (heavyChain_subset hP).2 hv
  have hPu : chainOf T r u = P := chainOf_eq_of_mem hP hu
  have hconn : (heavyGraph T r).Connected u v := by
    rw [← hPu] at hv; exact chainOf_conn hv
  rcases heavyGraph_connected_comparable hT huV hvV hconn with h | h
  · exact (isAncestor_eq_iff_depth hT hvV h).mp hd
  · exact ((isAncestor_eq_iff_depth hT huV h).mp hd.symm).symm

/-- The tree path from `u` up to an ancestor `w ≠ u` starts with the step to the parent. -/
lemma forestPath_up_cons (hT : IsRootedTree T r) {u w : ℕ} (hu : u ∈ T.V)
    (hw : IsAncestor T r w u) (hne : u ≠ w) :
    ∃ x, T.forestPath u w = x :: T.forestPath (parent T r u) w ∧ T.dst x = parent T r u := by
  have hur : u ≠ r := by
    intro h
    have hwV := isAncestor_mem hT hu hw
    exact hne (isAncestor_antisymm hT hu hwV (by rw [h]; exact isAncestor_root hT hwV) hw)
  obtain ⟨x, hEq, hp, -, -, -⟩ := forestPath_parent hT hu hur
  have hp_mem := parent_mem hT hu
  have hwp : IsAncestor T r w (parent T r u) := by
    rcases (isAncestor_iff_eq_or_parent hT hu).mp hw with h | ⟨_, h⟩
    · exact absurd h.symm hne
    · exact h
  have hsplit_u := (forestPath_eq_of_isAncestor hT hu hw).1
  have hsplit_p := (forestPath_eq_of_isAncestor hT hp_mem hwp).1
  refine ⟨x, ?_, hp.symm⟩
  refine (List.append_left_inj (T.forestPath w r)).mp ?_
  rw [← hsplit_u, hEq, List.cons_append, ← hsplit_p]

/-- The vertices of the tree path from `u` up to an ancestor `w`: entry `i` is the `i`-th
ancestor of `u`, and there are `depth u - depth w + 1` of them. -/
lemma walkVertices_up (hT : IsRootedTree T r) :
    ∀ d u w, u ∈ T.V → IsAncestor T r w u → depth T r u = depth T r w + d →
      (T.walkVertices u (T.forestPath u w)).length = d + 1 ∧
      ∀ i (hi : i < (T.walkVertices u (T.forestPath u w)).length),
        (T.walkVertices u (T.forestPath u w))[i] = (parent T r)^[i] u := by
  intro d
  induction d with
  | zero =>
    intro u w hu hw hd
    have huw : w = u := (isAncestor_eq_iff_depth hT hu hw).mp (by omega)
    subst huw
    rw [forestPath_self hT.isForest w]
    refine ⟨rfl, fun i hi => ?_⟩
    simp only [MGraph.walkVertices, List.map_nil, List.length_cons, List.length_nil] at hi
    have : i = 0 := by omega
    subst this
    rfl
  | succ d ih =>
    intro u w hu hw hd
    have hne : u ≠ w := by intro h; subst h; omega
    have hur : u ≠ r := by
      intro h
      have hwV := isAncestor_mem hT hu hw
      exact hne (isAncestor_antisymm hT hu hwV (by rw [h]; exact isAncestor_root hT hwV) hw)
    obtain ⟨x, hEq, hdst⟩ := forestPath_up_cons hT hu hw hne
    have hp_mem := parent_mem hT hu
    have hwp : IsAncestor T r w (parent T r u) := by
      rcases (isAncestor_iff_eq_or_parent hT hu).mp hw with h | ⟨_, h⟩
      · exact absurd h.symm hne
      · exact h
    have hdp := depth_parent hT hu hur
    obtain ⟨hlen, hget⟩ := ih (parent T r u) w hp_mem hwp (by omega)
    have hwv : T.walkVertices u (T.forestPath u w) =
        u :: T.walkVertices (parent T r u) (T.forestPath (parent T r u) w) := by
      rw [hEq]
      simp only [MGraph.walkVertices, List.map_cons, hdst]
    rw [hwv]
    refine ⟨by rw [List.length_cons, hlen], fun i hi => ?_⟩
    rcases i with _ | i
    · rfl
    · rw [List.getElem_cons_succ, hget i (by simp only [List.length_cons] at hi; omega),
        Function.iterate_succ_apply]

/-- The chain list has one vertex per depth, from the top down. -/
lemma depth_chainList_getElem (hT : IsRootedTree T r) {P : Finset ℕ}
    (hP : P ∈ heavyChains T r) :
    (chainList T r P).length = depth T r (chainBot T r P) - depth T r (chainTop T r P) + 1 ∧
    ∀ k (hk : k < (chainList T r P).length),
      depth T r ((chainList T r P)[k]) = depth T r (chainTop T r P) + k := by
  obtain ⟨hbP, hbanc⟩ := chainBot_spec hT hP
  obtain ⟨htP, htanc⟩ := chainTop_spec hT hP
  have hsub := (heavyChain_subset hP).2
  have hbV := hsub hbP
  have htb := htanc _ hbP
  have hdle := isAncestor_depth_le hT hbV htb
  set d := depth T r (chainBot T r P) - depth T r (chainTop T r P) with hd
  obtain ⟨hlen, hget⟩ := walkVertices_up hT d _ _ hbV htb (by omega)
  unfold chainList
  refine ⟨by rw [List.length_reverse, hlen], fun k hk => ?_⟩
  have hk' : k < d + 1 := by rw [List.length_reverse, hlen] at hk; exact hk
  rw [List.getElem_reverse, hget _ (by rw [hlen]; omega)]
  simp only [hlen]
  -- the `i`-th ancestor of the bottom has depth `depth bot - i`
  have hiter : ∀ i ≤ d, (parent T r)^[i] (chainBot T r P) ∈ T.V ∧
      depth T r ((parent T r)^[i] (chainBot T r P)) + i = depth T r (chainBot T r P) := by
    intro i
    induction i with
    | zero => intro _; exact ⟨hbV, by simp⟩
    | succ i ih =>
      intro hi
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hne : (parent T r)^[i] (chainBot T r P) ≠ r := by
        intro h
        rw [h] at h2
        have : depth T r r = 0 := by
          unfold depth; rw [forestPath_self hT.isForest r, List.length_nil]
        omega
      rw [Function.iterate_succ_apply']
      refine ⟨parent_mem hT h1, ?_⟩
      have := depth_parent hT h1 hne
      omega
  have := (hiter (d + 1 - 1 - k) (by omega)).2
  omega

/-- The chain list has as many entries as the chain. -/
lemma chainList_length (hT : IsRootedTree T r) {P : Finset ℕ} (hP : P ∈ heavyChains T r) :
    (chainList T r P).length = P.card := by
  classical
  rw [← List.toFinset_card_of_nodup (chainList_nodup hT hP)]
  congr 1
  ext w
  rw [List.mem_toFinset, mem_chainList_iff hT hP]

end MinCostFlow.LSF

end
