module

public import MinCostFlow.LSF.Program.THChainMath
public import MinCostFlow.LSF.Program.THBstMath

/-!
# The parent and depth of `T_H` from a stored chain

Suppose the chain `P` of `u` is stored in an array: position `lo + k` holds the vertex of `P` at
depth `depth top + k`. Then the chain list is the stored list (`chainList_eq_bstSeg`), and the
parent of `u` in `T_H` and its depth in `T_H` come from the search `bstIdx` on the stored list
without the top (`thParent_of_stored`, `thDepth_of_stored`):
* for `u ≠ top`, `thParent u` is the vertex `bstIdx` returns, and
  `depth_TH u = depth_TH top + 1 + bstDepth`;
* the top has `thParent top = parent top`.
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

variable {T : MGraph} {r : ℕ}

/-- A vertex of a chain lies at most `|P| - 1` levels below the top. -/
lemma chain_depth_lt (hT : IsRootedTree T r) {P : Finset ℕ} (hP : P ∈ heavyChains T r)
    {u : ℕ} (hu : u ∈ P) :
    depth T r (chainTop T r P) ≤ depth T r u ∧
      depth T r u - depth T r (chainTop T r P) < P.card := by
  have hsub := (heavyChain_subset hP).2
  obtain ⟨htP, htanc⟩ := chainTop_spec hT hP
  obtain ⟨hbP, hbanc⟩ := chainBot_spec hT hP
  have h1 := isAncestor_depth_le hT (hsub hu) (htanc u hu)
  have h2 := isAncestor_depth_le hT (hsub hbP) (hbanc u hu)
  have hlen := (depth_chainList_getElem hT hP).1
  rw [chainList_length hT hP] at hlen
  omega

/-- The stored chain is the chain list. -/
lemma chainList_eq_bstSeg (hT : IsRootedTree T r) {P : Finset ℕ} (hP : P ∈ heavyChains T r)
    (A : ℕ → ℕ) (lo : ℕ)
    (hA : ∀ k < P.card, A (lo + k) ∈ P ∧ depth T r (A (lo + k)) = depth T r (chainTop T r P) + k) :
    chainList T r P = bstSeg A lo P.card := by
  have hlen := chainList_length hT hP
  refine List.ext_getElem (by rw [hlen, bstSeg_length]) (fun k h1 h2 => ?_)
  rw [bstSeg_getElem]
  have hk : k < P.card := by rw [← hlen]; exact h1
  refine chain_eq_of_depth hT hP ((mem_chainList_iff hT hP).mp (List.getElem_mem h1)) (hA k hk).1 ?_
  rw [(depth_chainList_getElem hT hP).2 k h1, (hA k hk).2]

/-- A vertex of a stored chain is the entry at its depth below the top. -/
lemma stored_eq (hT : IsRootedTree T r) {P : Finset ℕ} (hP : P ∈ heavyChains T r)
    (A : ℕ → ℕ) (lo : ℕ)
    (hA : ∀ k < P.card, A (lo + k) ∈ P ∧ depth T r (A (lo + k)) = depth T r (chainTop T r P) + k)
    {u : ℕ} (hu : u ∈ P) :
    A (lo + (depth T r u - depth T r (chainTop T r P))) = u := by
  obtain ⟨h1, h2⟩ := chain_depth_lt hT hP hu
  have := hA _ h2
  exact chain_eq_of_depth hT hP this.1 hu (by rw [this.2]; omega)

/-- The stored values are distinct on the chain. -/
lemma stored_inj (hT : IsRootedTree T r) {P : Finset ℕ} (A : ℕ → ℕ) (lo : ℕ)
    (hA : ∀ k < P.card, A (lo + k) ∈ P ∧ depth T r (A (lo + k)) = depth T r (chainTop T r P) + k) :
    ∀ a < P.card, ∀ b < P.card, A (lo + a) = A (lo + b) → a = b := by
  intro a ha b hb hab
  have h1 := (hA a ha).2
  have h2 := (hA b hb).2
  rw [hab] at h1
  omega

/-- The parent in `T_H` of a vertex below the top of its chain, from the stored chain. -/
theorem thParent_of_stored (hT : IsRootedTree T r) {u : ℕ} (hu : u ∈ T.V)
    (A : ℕ → ℕ) (lo : ℕ)
    (hA : ∀ k < (chainOf T r u).card, A (lo + k) ∈ chainOf T r u ∧
      depth T r (A (lo + k)) = depth T r (chainTop T r (chainOf T r u)) + k)
    (hne : u ≠ chainTop T r (chainOf T r u)) :
    thParent T r u = (bstIdx (chainTop T r (chainOf T r u)) A (lo + 1)
        ((chainOf T r u).card - 1)
        (depth T r u - depth T r (chainTop T r (chainOf T r u)) - 1)).1 ∧
      bstDepth (chainList T r (chainOf T r u)).tail u =
        (bstIdx (chainTop T r (chainOf T r u)) A (lo + 1) ((chainOf T r u).card - 1)
          (depth T r u - depth T r (chainTop T r (chainOf T r u)) - 1)).2 := by
  set P := chainOf T r u with hPdef
  have hP : P ∈ heavyChains T r := chainOf_mem_heavyChains hu
  have huP : u ∈ P := mem_chainOf_self hu
  set t := chainTop T r P with ht
  have hL := chainList_eq_bstSeg hT hP A lo hA
  have htail : (chainList T r P).tail = bstSeg A (lo + 1) (P.card - 1) := by
    rw [hL, ← List.drop_one, bstSeg_drop]
  obtain ⟨hd1, hd2⟩ := chain_depth_lt hT hP huP
  rw [← ht] at hd1 hd2
  have hdpos : depth T r u ≠ depth T r t := by
    intro h
    exact hne (chain_eq_of_depth hT hP huP (chainTop_spec hT hP).1 h)
  have hju : A (lo + 1 + (depth T r u - depth T r t - 1)) = u := by
    rw [show lo + 1 + (depth T r u - depth T r t - 1) = lo + (depth T r u - depth T r t) by omega]
    exact stored_eq hT hP A lo hA huP
  have hinj : ∀ a < P.card - 1, ∀ b < P.card - 1, A (lo + 1 + a) = A (lo + 1 + b) → a = b := by
    intro a ha b hb hab
    have := stored_inj hT A lo hA (1 + a) (by omega) (1 + b) (by omega)
      (by rw [← Nat.add_assoc, ← Nat.add_assoc]; exact hab)
    omega
  obtain ⟨h1, h2⟩ := bstIdx_spec A (P.card - 1) t (lo + 1) (depth T r u - depth T r t - 1)
    (by omega) hinj
  rw [hju] at h1 h2
  refine ⟨?_, by rw [htail]; exact h2⟩
  have hdef : thParent T r u = bstParentWith t (chainList T r P).tail u := by
    unfold thParent
    simp only [← hPdef, ← ht, hne, if_false]
  rw [hdef, htail, h1]

/-- The parent in `T_H` of the top of a chain is its parent in `T`. -/
lemma thParent_top {u : ℕ} (htop : u = chainTop T r (chainOf T r u)) :
    thParent T r u = parent T r u := by
  unfold thParent
  simp only [← htop, if_true]

/-- The depth in `T_H` below the top of a chain. -/
theorem thDepth_below_top (hT : IsRootedTree T r) {P : Finset ℕ} (hP : P ∈ heavyChains T r) :
    ∀ d u, u ∈ (chainList T r P).tail → bstDepth (chainList T r P).tail u = d →
      depth (hldAuxTree T r) r u = depth (hldAuxTree T r) r (chainTop T r P) + 1 + d := by
  set t := chainTop T r P with ht
  set L := (chainList T r P).tail with hL
  have hnd : L.Nodup := (chainList_nodup hT hP).sublist (List.tail_sublist _)
  have hsub := (heavyChain_subset hP).2
  have hmemL : ∀ v, v ∈ L ↔ v ∈ P ∧ v ≠ t := fun v => chainList_tail_mem_iff hT hP
  -- a vertex of `L` is not the root, and its `T_H` parent is the search parent
  have hfacts : ∀ v ∈ L, v ∈ T.V ∧ v ≠ r ∧ thParent T r v = bstParentWith t L v := by
    intro v hv
    obtain ⟨hvP, hvt⟩ := (hmemL v).mp hv
    have hvV := hsub hvP
    have hPv : chainOf T r v = P := chainOf_eq_of_mem hP hvP
    refine ⟨hvV, fun hvr => hvt ?_, ?_⟩
    · have := chainTop_chainOf_self hT hvV (Or.inl hvr)
      rw [hPv] at this; exact this.symm
    · unfold thParent
      simp only [hPv, ← ht, hvt, if_false, ← hL]
  intro d
  induction d with
  | zero =>
    intro u hu hd
    obtain ⟨huV, hur, hpar⟩ := hfacts u hu
    have hspec := bstParentWith_spec L.length t L u hu rfl hnd
    have hmid : u = L[L.length / 2]'(Nat.div_lt_self (List.length_pos_of_mem hu) (by decide)) := by
      by_contra hne
      have := (hspec.2 hne).2
      omega
    have hp := (hspec.1 hmid).1
    have hTH := (hldAuxTree_parent hT huV hur).2.2
    rw [hpar, hp] at hTH
    omega
  | succ d ih =>
    intro u hu hd
    obtain ⟨huV, hur, hpar⟩ := hfacts u hu
    have hspec := bstParentWith_spec L.length t L u hu rfl hnd
    have hmid : u ≠ L[L.length / 2]'(Nat.div_lt_self (List.length_pos_of_mem hu) (by decide)) := by
      intro hmid
      have := (hspec.1 hmid).2
      omega
    obtain ⟨hpL, hpd⟩ := hspec.2 hmid
    have hTH := (hldAuxTree_parent hT huV hur).2.2
    rw [hpar] at hTH
    have := ih _ hpL (by omega)
    omega

end MinCostFlow.LSF

end
