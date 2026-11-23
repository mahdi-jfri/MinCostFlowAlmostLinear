module

public import MinCostFlow.LinkCut.Prog.MathForestLinkOps

/-!
# Parent pointers and acyclicity for `link`

Pure facts about parent maps: following parents from a node reaches a root, and `link`
keeps the parent map acyclic (`link_acyc_pigeonhole`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section PureParentAndAcyclicity

theorem lctLink_par_notin_free {w h L P b n : ℕ} {freeEdges : List ℕ}
    {edgeMap : List (ℕ × ForestEdge)} {trees : List AuxTree} {mem : ℕ → ℕ}
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap trees mem)
    (hslots_perm : (edgeMap.map Prod.fst ++ freeEdges).Perm ((List.range n).map (n + 1 + ·)))
    (hed_lt : ∀ p ∈ edgeMap, p.2.u < n ∧ p.2.v < n)
    {ed : ℕ} (hed : ed ∈ freeEdges) :
    ∀ z, lctAuxParent mem (lctNodesBase b) (lctCap n) z ≠ ed := by
  let nb := lctNodesBase b
  let cap := lctCap n
  have hed_bd := (hi.freeNodeOk ed hed).1
  have hsub := hi.subdivOk
  have hdisj : ∀ p ∈ edgeMap, p.1 ≠ ed := by
    have hnd : (edgeMap.map Prod.fst ++ freeEdges).Nodup :=
      hslots_perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => by omega))
    intro p hp heq
    exact List.disjoint_of_nodup_append hnd (List.mem_map.2 ⟨p, hp, heq⟩) hed
  intro z hze
  change lctAuxParent mem nb cap z = ed at hze
  have hz_range : 1 ≤ z ∧ z ≤ cap := by
    by_contra hnot
    rw [lctAuxParent_mem_iff_of_trees hi.sf hi.ppar_le_cap z] at hze
    have hfn : trees.findSome? (fun s =>
        let seq := s.evalInorder (revFlag mem nb) false
        if z ∈ seq then some (listParentFrom (nodeField mem nb s.rootId OFF_PPAR) seq z) else none) =
        none := List.findSome?_eq_none_iff.2 fun s hs => by
      have hnin : z ∉ s.evalInorder (revFlag mem nb) false := fun hm => by
        have hm' := (s.evalInorder_perm (revFlag mem nb) false).mem_iff.1 hm
        exact hnot ((hi.sf.trees_ok s hs).2.2.nodup_perm_mem hm')
      simp [hnin]
    rw [hfn] at hze
    dsimp only at hze
    omega
  by_cases hzn : z ≤ n
  · rcases hsub.2.2.1 (z - 1) (by omega) with h0 | ⟨p, hp, _, hp_eq⟩
    · have h1 : lctAuxParent mem nb cap z = 0 := by
        simpa [nb, cap, Nat.sub_add_cancel hz_range.1] using h0
      omega
    · have h1 : lctAuxParent mem nb cap z = p.1 := by
        simpa [nb, cap, Nat.sub_add_cancel hz_range.1] using hp_eq
      exact hdisj p hp (h1.symm.trans hze)
  · have hmem : z ∈ (List.range n).map (n + 1 + ·) :=
      List.mem_map.2 ⟨z - (n + 1), List.mem_range.2 (by unfold cap lctCap at hz_range; omega),
        by omega⟩
    rcases List.mem_append.1 (hslots_perm.symm.mem_iff.1 hmem) with he | hf
    · rcases List.mem_map.1 he with ⟨p, hp, rfl⟩
      have hpu := hed_lt p hp
      rcases hsub.2.2.2 p hp with ⟨hpar_p, _⟩ | ⟨hpar_p, _⟩
      · change lctAuxParent mem nb cap p.1 = p.2.u + 1 at hpar_p
        rw [hpar_p] at hze; omega
      · change lctAuxParent mem nb cap p.1 = p.2.v + 1 at hpar_p
        rw [hpar_p] at hze; omega
    · have h0 : lctAuxParent mem nb cap z = 0 := hsub.2.1 z hf
      omega

private lemma list_exists_dup_of_not_nodup : ∀ {l : List ℕ}, ¬ l.Nodup →
    ∃ i j, i < j ∧ j < l.length ∧ ∃ (hi : i < l.length) (hj : j < l.length), l[i] = l[j]
  | [], h => absurd List.nodup_nil h
  | x :: xs, h => by
      rw [List.nodup_cons, not_and] at h
      by_cases hx : x ∈ xs
      · rcases List.getElem_of_mem hx with ⟨j, hj, hj_eq⟩
        exact ⟨0, j + 1, Nat.succ_pos j, by simp [hj], by simp, by simp [hj],
          by simpa using hj_eq.symm⟩
      · rcases list_exists_dup_of_not_nodup (h hx) with ⟨i, j, hij, hjl, hi, hj, heq⟩
        exact ⟨i + 1, j + 1, Nat.succ_lt_succ hij, by simp [hjl], by simp [hi], by simp [hj],
          by simpa using heq⟩

lemma link_acyc_pigeonhole {par : ℕ → ℕ} {cap : ℕ}
    (hp0 : par 0 = 0)
    (hle : ∀ z, 1 ≤ z → z ≤ cap → par z ≤ cap)
    (hterm : ∀ q, 1 ≤ q → q ≤ cap → ∃ N, iterParent par N q = 0) :
    ∀ q, 1 ≤ q → q ≤ cap → iterParent par cap q = 0 := by
  intro q hq1 hq2
  by_contra hne0
  let xs := (List.range (cap + 1)).map (fun j => iterParent par j q)
  have hno_zero : ∀ j ≤ cap, iterParent par j q ≠ 0 := fun j hj h0 => by
    have hadd : iterParent par cap q = iterParent par (cap - j) (iterParent par j q) := by
      rw [← iterParent_add, Nat.add_comm, Nat.sub_add_cancel hj]
    rw [h0, iterParent_zero_fixed hp0] at hadd
    exact hne0 hadd
  have hsub : xs ⊆ (List.range cap).map (· + 1) := by
    intro y hy
    rcases List.mem_map.1 hy with ⟨j, hj, rfl⟩
    rw [List.mem_range] at hj
    have hnz := hno_zero j (by omega)
    have hle_j := iterParent_le_cap hp0 hle hq2 j
    exact List.mem_map.2 ⟨iterParent par j q - 1, List.mem_range.2 (by omega), by omega⟩
  have hnot_nd : ¬ xs.Nodup := fun hnd => by
    have hle_len := (List.Nodup.subperm hnd hsub).length_le
    simp only [xs, List.length_map, List.length_range] at hle_len
    omega
  rcases list_exists_dup_of_not_nodup hnot_nd with ⟨i, j, hij, _, hi, hj, heq⟩
  have hi_lt : i < cap + 1 := by simp [xs] at hi; omega
  have hj_lt : j < cap + 1 := by simp [xs] at hj; omega
  have heq_it : iterParent par i q = iterParent par j q := by
    simpa [xs, List.getElem_map] using heq
  have hcyc : iterParent par (j - i) (iterParent par i q) = iterParent par i q := by
    rw [← iterParent_add, Nat.add_comm, Nat.sub_add_cancel (le_of_lt hij)]
    exact heq_it.symm
  rcases hterm q hq1 hq2 with ⟨N, hN⟩
  have h0_big : iterParent par (i + N * (j - i)) q = 0 := by
    by_cases hleN : N ≤ i + N * (j - i)
    · have hdec : i + N * (j - i) = N + (i + N * (j - i) - N) := by omega
      rw [hdec, iterParent_add, hN, iterParent_zero_fixed hp0]
    · have : 1 ≤ j - i := by omega
      have : N ≤ N * (j - i) := Nat.le_mul_of_pos_right _ this
      omega
  have hnz_big : iterParent par (i + N * (j - i)) q = iterParent par i q := by
    rw [iterParent_add, iterParent_mul_cycle hcyc N]
  have h0_i := h0_big.symm.trans hnz_big
  exact hno_zero i (by omega) h0_i.symm

private lemma rootAbove_iterParent_eq {par : ℕ → ℕ} {cap : ℕ}
    (hp0 : par 0 = 0)
    (hle : ∀ z, 1 ≤ z → z ≤ cap → par z ≤ cap)
    (hacyc : ∀ z, 1 ≤ z → z ≤ cap → iterParent par cap z = 0) :
    ∀ m x, 1 ≤ x → x ≤ cap → iterParent par m x ≠ 0 →
      rootAbove par cap (iterParent par m x) = rootAbove par cap x := by
  intro m
  induction m with
  | zero => intro x _ _ _; rfl
  | succ m ih =>
      intro x hx1 hx2 hnz
      rw [iterParent_succ_right] at hnz ⊢
      have hm_le : iterParent par m x ≤ cap := iterParent_le_cap hp0 hle hx2 m
      have hm_nz : iterParent par m x ≠ 0 := fun hz => by
        rw [hz, hp0] at hnz; exact hnz rfl
      have hstep := rootAbove_step hp0 hle hacyc (by omega) hm_le hnz
      exact hstep.trans (ih x hx1 hx2 hm_nz)

theorem lctLink_v_no_u {w h L P b u v : ℕ} {F : MathForest} {x : LctConc}
    {mem : ℕ → ℕ} {freeEdges : List ℕ} {edgeMap : List (ℕ × ForestEdge)} {trees : List AuxTree}
    (hi : LctExposeInvs w h L P b F.n freeEdges edgeMap trees mem)
    (hrep : LctMemRep w h L P b F x mem)
    (hu : u < F.n) (hv : v < F.n) (hdisc : ¬ F.SameComp u v) :
    ∀ m, iterParent (lctAuxParent mem (lctNodesBase b) (lctCap F.n)) m (v + 1) ≠ u + 1 := by
  intro m hm
  let nb := lctNodesBase b
  let cap := lctCap F.n
  let par := lctAuxParent mem nb cap
  have hp0 : par 0 = 0 := lctAuxParent_zero mem nb cap
  have hle : ∀ z, 1 ≤ z → z ≤ cap → par z ≤ cap := fun z _ _ => lctAuxParent_le_cap mem nb cap z
  have hrb_eq := rootAbove_iterParent_eq hp0 hle hi.subdivOk.1 m (v + 1) (by omega)
    (by unfold cap lctCap; omega) (by rw [hm]; omega)
  rw [hm] at hrb_eq
  exact hdisc ((hrep.sameComp_iff_rootAbove hu hv).2 hrb_eq)

theorem lctLink_iterParent_no_u {par par' : ℕ → ℕ} {ed u1 : ℕ}
    (hupd : ∀ z, par' z = if z = ed then par' ed else if z = u1 then ed else par z)
    (hno_ed : ∀ z, par z ≠ ed) :
    ∀ k w, w ≠ ed → (∀ m, iterParent par m w ≠ u1) →
      iterParent par' k w = iterParent par k w := by
  intro k
  induction k with
  | zero => intro w _ _; rfl
  | succ k ih =>
      intro w hwed hno_u
      rw [iterParent_succ_right, iterParent_succ_right, ih w hwed hno_u]
      have hne_u : iterParent par k w ≠ u1 := hno_u k
      have hne_ed : iterParent par k w ≠ ed := by
        cases k with
        | zero => exact hwed
        | succ k' =>
            rw [iterParent_succ_right]
            exact hno_ed _
      rw [hupd, ite_eq_right hne_ed, ite_eq_right hne_u]

end PureParentAndAcyclicity

section LinkInvariants

end LinkInvariants
end MinCostFlow.LinkCut.Prog
end
