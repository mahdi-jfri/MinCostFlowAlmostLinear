module

public import MinCostFlow.LinkCut.Prog.MathForestRerootInvs

/-!
# How the represented root moves under reroot

The represented forest is a parent map `lctAuxParent` on node ids `1 .. cap`, and the root of
node `x` is `rootAbove par cap x`. This file proves that `revNode` after `expose v` (the reroot
step) moves the root of the tree of `v + 1` to `v + 1` and keeps every other root
(the `RootMove` part of `revNode_reroot_invs`). The general statement is `RootMove par₁ par₂ cap r`. The proof only
uses the facts that `revNode_reroot_edge_subdiv` already gives: parents change only on the
exposed path, and that path ends at `v + 1`. It also shows that `lctAuxParent` reads only the
structural fields of the nodes (`lctAuxParent_struct_agree`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section RootMove

/-- The root map of `par₂` is that of `par₁`, except that the tree of `r` now has root `r`. -/
def RootMove (par₁ par₂ : ℕ → ℕ) (cap r : ℕ) : Prop :=
  ∀ x, 1 ≤ x → x ≤ cap →
    rootAbove par₂ cap x =
      if rootAbove par₁ cap x = rootAbove par₁ cap r then r else rootAbove par₁ cap x

/-- Two parent maps that agree along the whole chain above `u` give the same root. -/
theorem rootAbove_eq_of_chain_agree {par₁ par₂ : ℕ → ℕ} :
    ∀ k u, (∀ j ≤ k, par₂ (iterParent par₁ j u) = par₁ (iterParent par₁ j u)) →
      rootAbove par₂ k u = rootAbove par₁ k u := by
  intro k
  induction k with
  | zero => intro u _; rfl
  | succ k ih =>
      intro u hagree
      have h0 : par₂ u = par₁ u := hagree 0 (Nat.zero_le _)
      have hrest : ∀ j ≤ k, par₂ (iterParent par₁ j (par₁ u)) =
          par₁ (iterParent par₁ j (par₁ u)) := fun j hj => hagree (j + 1) (by omega)
      simp only [rootAbove, h0]
      split_ifs
      · rfl
      · exact ih (par₁ u) hrest

/-- Every nonzero node on the chain above `x` has the root of `x`. -/
theorem rootAbove_iterParent {par : ℕ → ℕ} {cap : ℕ}
    (hp0 : par 0 = 0) (hle : ∀ x, 1 ≤ x → x ≤ cap → par x ≤ cap)
    (hacyc : ∀ u, 1 ≤ u → u ≤ cap → iterParent par cap u = 0)
    {x : ℕ} (_hx1 : 1 ≤ x) (hx2 : x ≤ cap) :
    ∀ j, iterParent par j x ≠ 0 → rootAbove par cap (iterParent par j x) = rootAbove par cap x := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hne
      rw [iterParent_succ_right] at hne ⊢
      have ha_ne : iterParent par j x ≠ 0 := by
        intro h0; rw [h0, hp0] at hne; exact hne rfl
      have ha2 : iterParent par j x ≤ cap := iterParent_le_cap hp0 hle hx2 j
      rw [rootAbove_step hp0 hle hacyc (Nat.pos_of_ne_zero ha_ne) ha2 hne]
      exact ih ha_ne

theorem rootAbove_self_of_par_zero {par : ℕ → ℕ} {cap r : ℕ} (hcap : 1 ≤ cap) (hr : par r = 0) :
    rootAbove par cap r = r := by
  obtain ⟨m, rfl⟩ : ∃ m, cap = m + 1 := ⟨cap - 1, by omega⟩
  simp [rootAbove, hr]

/-- The general reroot step: parents change only on a list `seq`; under the new parents `seq`
is a chain ending at `r`, which has no parent; and both parent maps have the same trees. Then
the tree of `r` gets root `r` and all other roots stay. -/
theorem rootMove_of_seq {par₁ par₂ : ℕ → ℕ} {cap r : ℕ} {seq : List ℕ}
    (hp0₁ : par₁ 0 = 0) (hle₁ : ∀ x, 1 ≤ x → x ≤ cap → par₁ x ≤ cap)
    (hacyc₁ : ∀ u, 1 ≤ u → u ≤ cap → iterParent par₁ cap u = 0)
    (hp0₂ : par₂ 0 = 0) (hle₂ : ∀ x, 1 ≤ x → x ≤ cap → par₂ x ≤ cap)
    (hacyc₂ : ∀ u, 1 ≤ u → u ≤ cap → iterParent par₂ cap u = 0)
    (hcomp : ∀ x y, 1 ≤ x → x ≤ cap → 1 ≤ y → y ≤ cap →
      (rootAbove par₂ cap x = rootAbove par₂ cap y ↔ rootAbove par₁ cap x = rootAbove par₁ cap y))
    (hseq_sub : ∀ s ∈ seq, 1 ≤ s ∧ s ≤ cap)
    (hout : ∀ u, u ∉ seq → par₂ u = par₁ u)
    (hchain : ∀ i (hi : i + 1 < seq.length), par₂ seq[i] = seq[i + 1])
    (hlast : seq.getLast? = some r)
    (hr1 : 1 ≤ r) (hr2 : r ≤ cap) (hpar_r : par₂ r = 0) :
    RootMove par₁ par₂ cap r := by
  have hcap : 1 ≤ cap := le_trans hr1 hr2
  have hroot_r : rootAbove par₂ cap r = r := rootAbove_self_of_par_zero hcap hpar_r
  -- every element of `seq` lies in the tree of `r`
  have hlen : 0 < seq.length := by
    rcases seq with _ | ⟨a, as⟩
    · simp at hlast
    · simp
  have hlast_get : seq[seq.length - 1]'(by omega) = r := by
    have hg : seq.getLast? = seq[seq.length - 1]? := List.getLast?_eq_getElem?
    rw [List.getElem?_eq_getElem (by omega : seq.length - 1 < seq.length), hlast] at hg
    exact Option.some.inj hg.symm
  have hseq_root₂ : ∀ d i (hi : i < seq.length), seq.length - 1 - i = d →
      rootAbove par₂ cap seq[i] = r := by
    intro d
    induction d with
    | zero =>
        intro i hi hd
        have : i = seq.length - 1 := by omega
        subst this; rw [hlast_get]; exact hroot_r
    | succ d ih =>
        intro i hi hd
        have hi1 : i + 1 < seq.length := by omega
        have hs := hseq_sub seq[i] (List.getElem_mem hi)
        have hs1 := hseq_sub seq[i + 1] (List.getElem_mem hi1)
        have hstep := rootAbove_step hp0₂ hle₂ hacyc₂ hs.1 hs.2
          (by rw [hchain i hi1]; omega)
        rw [← hstep, hchain i hi1]
        exact ih (i + 1) hi1 (by omega)
  have hseq_root₁ : ∀ s ∈ seq, rootAbove par₁ cap s = rootAbove par₁ cap r := by
    intro s hs
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
    have hs' := hseq_sub seq[i] hs
    exact (hcomp _ _ hs'.1 hs'.2 hr1 hr2).1
      ((hseq_root₂ _ i hi rfl).trans hroot_r.symm)
  intro x hx1 hx2
  split_ifs with hsame
  · have h2 := (hcomp x r hx1 hx2 hr1 hr2).2 hsame
    rw [h2, hroot_r]
  · apply rootAbove_eq_of_chain_agree
    intro j _
    apply hout
    intro hmem
    have hne : iterParent par₁ j x ≠ 0 := fun h0 => by
      have := (hseq_sub _ hmem).1; omega
    exact hsame ((rootAbove_iterParent hp0₁ hle₁ hacyc₁ hx1 hx2 j hne).symm.trans
      (hseq_root₁ _ hmem))

end RootMove

section StructAgree

/-- The fields that `lctAuxParent` reads: children, splay parent, path parent and the reversal
bit. -/
def IsStructOff (off : ℕ) : Prop :=
  off = OFF_LEFT ∨ off = OFF_RIGHT ∨ off = OFF_PARENT ∨ off = OFF_PPAR ∨ off = OFF_REV

theorem readAuxTree_struct_agree {mem₁ mem₂ : ℕ → ℕ} {nb cap : ℕ}
    (hs : ∀ u ≤ cap, ∀ off, IsStructOff off → nodeField mem₂ nb u off = nodeField mem₁ nb u off) :
    ∀ fuel x, readAuxTree mem₂ nb cap fuel x = readAuxTree mem₁ nb cap fuel x := by
  intro fuel
  induction fuel with
  | zero => intro x; cases x <;> rfl
  | succ f ih =>
      intro x
      cases x with
      | zero => rfl
      | succ x' =>
          simp only [readAuxTree]
          by_cases hxle : x' + 1 ≤ cap
          · simp only [hxle, ↓reduceIte, hs _ hxle OFF_LEFT (Or.inl rfl),
              hs _ hxle OFF_RIGHT (Or.inr (Or.inl rfl)), ih]
          · simp only [hxle, ↓reduceIte]

/-- `lctAuxParent` reads only the structural fields of nodes `1 .. cap`. -/
theorem lctAuxParent_struct_agree {mem₁ mem₂ : ℕ → ℕ} {nb cap : ℕ}
    (hs : ∀ u ≤ cap, ∀ off, IsStructOff off → nodeField mem₂ nb u off = nodeField mem₁ nb u off)
    (u : ℕ) : lctAuxParent mem₂ nb cap u = lctAuxParent mem₁ nb cap u := by
  have hroots : auxRootIds mem₂ nb cap = auxRootIds mem₁ nb cap := by
    unfold auxRootIds
    apply List.filter_congr
    intro r hr
    simp only [List.mem_map, List.mem_range] at hr
    rcases hr with ⟨x, hx, rfl⟩
    simp [hs (x + 1) (by omega) OFF_PARENT (Or.inr (Or.inr (Or.inl rfl)))]
  have hseq : ∀ r, lctTreeSeq mem₂ nb cap r = lctTreeSeq mem₁ nb cap r := by
    intro r
    unfold lctTreeSeq
    rw [readAuxTree_struct_agree hs]
    apply AuxTree.evalInorder_agree
    intro y hy
    simp [revFlag, hs y (readAuxTree_nodes_bounds hy).2 OFF_REV
      (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]
  have htree : ∀ r ∈ auxRootIds mem₁ nb cap,
      treeParentEntry mem₂ nb cap r u = treeParentEntry mem₁ nb cap r u := by
    intro r hr
    have hr_le : r ≤ cap := by
      unfold auxRootIds at hr
      simp only [List.mem_filter, List.mem_map, List.mem_range] at hr
      rcases hr with ⟨⟨x, hx, rfl⟩, _⟩
      omega
    simp only [treeParentEntry, hseq r,
      hs r hr_le OFF_PPAR (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]
  unfold lctAuxParent
  rw [hroots]
  have go : ∀ rs : List ℕ, (∀ r ∈ rs, treeParentEntry mem₂ nb cap r u =
        treeParentEntry mem₁ nb cap r u) →
      rs.findSome? (fun r => treeParentEntry mem₂ nb cap r u) =
      rs.findSome? (fun r => treeParentEntry mem₁ nb cap r u) := by
    intro rs hrs
    induction rs with
    | nil => simp
    | cons r rs ih =>
        simp only [List.findSome?]
        rw [hrs r (by simp), ih (fun r' hr' => hrs r' (by simp [hr']))]
  rw [go _ htree]

end StructAgree

section LinkCutRoots

/-- Zeroing the parents of the nodes in a set `S` either stops the walk to the root at a node of
`S`, or keeps the root. -/
theorem rootAbove_zeroed {par par' : ℕ → ℕ} {S : ℕ → Prop}
    (hS : ∀ z, S z → par' z = 0) (hnS : ∀ z, ¬ S z → par' z = par z) :
    ∀ k u, S (rootAbove par' k u) ∨ rootAbove par' k u = rootAbove par k u := by
  intro k
  induction k with
  | zero => intro u; right; rfl
  | succ k ih =>
      intro u
      by_cases hu : S u
      · left
        simp only [rootAbove, hS u hu, ↓reduceIte]
        exact hu
      · simp only [rootAbove, hnS u hu]
        split_ifs
        · right; rfl
        · exact ih (par u)

/-- The root map after `link`: the tree of `u1` (whose root is `u1`) is hung below `v1` through
the edge node `ed`, so its nodes get the root of `v1`; all other roots stay. -/
theorem rootAbove_link {par₃ par_p : ℕ → ℕ} {cap u1 v1 ed : ℕ}
    (hp0₃ : par₃ 0 = 0) (hle₃ : ∀ x, 1 ≤ x → x ≤ cap → par₃ x ≤ cap)
    (hacyc₃ : ∀ u, 1 ≤ u → u ≤ cap → iterParent par₃ cap u = 0)
    (hp0_p : par_p 0 = 0) (hle_p : ∀ x, 1 ≤ x → x ≤ cap → par_p x ≤ cap)
    (hacyc_p : ∀ u, 1 ≤ u → u ≤ cap → iterParent par_p cap u = 0)
    (hupd : ∀ z, par_p z = if z = ed then v1 else if z = u1 then ed else par₃ z)
    (hno_ed : ∀ z, par₃ z ≠ ed)
    (hu1 : 1 ≤ u1) (hu1c : u1 ≤ cap) (hpar_u : par₃ u1 = 0)
    (hv1 : 1 ≤ v1) (hv1c : v1 ≤ cap) (hed1 : 1 ≤ ed) (hedc : ed ≤ cap)
    (hv_ed : v1 ≠ ed) (hu_ed : u1 ≠ ed) (hv_root : rootAbove par₃ cap v1 ≠ u1) :
    ∀ x, 1 ≤ x → x ≤ cap → x ≠ ed →
      rootAbove par_p cap x =
        if rootAbove par₃ cap x = u1 then rootAbove par₃ cap v1 else rootAbove par₃ cap x := by
  have hcap : 1 ≤ cap := le_trans hu1 hu1c
  have hroot_u : rootAbove par₃ cap u1 = u1 := rootAbove_self_of_par_zero hcap hpar_u
  have hne_ed : ∀ x, x ≠ ed → ∀ j, iterParent par₃ j x ≠ ed := by
    intro x hxed j
    cases j with
    | zero => exact hxed
    | succ j => rw [iterParent_succ_right]; exact hno_ed _
  -- outside the tree of `u1` nothing changes
  have hout : ∀ x, 1 ≤ x → x ≤ cap → x ≠ ed → rootAbove par₃ cap x ≠ u1 →
      rootAbove par_p cap x = rootAbove par₃ cap x := by
    intro x hx1 hx2 hxed hne
    apply rootAbove_eq_of_chain_agree
    intro j _
    have hne_u : iterParent par₃ j x ≠ u1 := fun h => by
      have hr := rootAbove_iterParent hp0₃ hle₃ hacyc₃ hx1 hx2 j (by rw [h]; omega)
      rw [h, hroot_u] at hr
      exact hne hr.symm
    simp only [hupd, hne_ed x hxed j, hne_u, ↓reduceIte]
  intro x hx1 hx2 hxed
  split_ifs with hin
  · -- the chain from `x` reaches `u1`; before that, the parents agree
    have hreach := rootAbove_reachesIn hle₃ hacyc₃ hx1 hx2
    rw [hin] at hreach
    simp only [reachesIn, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
      List.mem_range] at hreach
    have hex : ∃ j, iterParent par₃ j x = u1 := by
      obtain ⟨_, k, _, hk⟩ := hreach
      exact ⟨k, hk⟩
    classical
    let j := Nat.find hex
    have hj : iterParent par₃ j x = u1 := Nat.find_spec hex
    have hbefore : ∀ i < j, iterParent par₃ i x ≠ u1 := fun i hi => Nat.find_min hex hi
    have hwalk : ∀ i ≤ j, rootAbove par_p cap (iterParent par₃ i x) = rootAbove par_p cap x := by
      intro i
      induction i with
      | zero => intro _; rfl
      | succ i ih =>
          intro hi
          have ha_ne_u : iterParent par₃ i x ≠ u1 := hbefore i (by omega)
          have hnext_ne : iterParent par₃ (i + 1) x ≠ 0 := by
            intro h0
            have hzero : ∀ t, iterParent par₃ (i + 1 + t) x = 0 := by
              intro t
              rw [iterParent_add, h0, iterParent_zero_fixed hp0₃]
            have := hzero (j - (i + 1))
            rw [show i + 1 + (j - (i + 1)) = j by omega, hj] at this
            omega
          have ha_ne0 : iterParent par₃ i x ≠ 0 := by
            intro h0
            rw [iterParent_succ_right, h0, hp0₃] at hnext_ne
            exact hnext_ne rfl
          have ha2 : iterParent par₃ i x ≤ cap := iterParent_le_cap hp0₃ hle₃ hx2 i
          have hpa : par_p (iterParent par₃ i x) = iterParent par₃ (i + 1) x := by
            rw [iterParent_succ_right]
            simp only [hupd, hne_ed x hxed i, ha_ne_u, ↓reduceIte]
          have hstep := rootAbove_step hp0_p hle_p hacyc_p (Nat.pos_of_ne_zero ha_ne0) ha2
            (by rw [hpa]; exact hnext_ne)
          rw [hpa] at hstep
          rw [hstep]
          exact ih (by omega)
    have hpu : par_p u1 = ed := by simp only [hupd, hu_ed, ↓reduceIte]
    have hped : par_p ed = v1 := by simp only [hupd, ↓reduceIte]
    have h1 := rootAbove_step hp0_p hle_p hacyc_p hu1 hu1c (by rw [hpu]; omega)
    have h2 := rootAbove_step hp0_p hle_p hacyc_p hed1 hedc (by rw [hped]; omega)
    rw [hpu] at h1
    rw [hped] at h2
    rw [← hwalk j le_rfl, hj, ← h1, ← h2]
    exact hout v1 hv1 hv1c hv_ed hv_root
  · exact hout x hx1 hx2 hxed hin

end LinkCutRoots

end MinCostFlow.LinkCut.Prog
