module

public import MinCostFlow.HierPaths.DelProgEntry
public import MinCostFlow.HierPaths.DelProgWitness

/-!
# Bounding the Delete scratch lists

A terminal in one child has a connector to each sibling, so the terminal incidence cap
bounds the branching. Together with the depth cap, this bounds how many terminals can
appear in the work lists.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

/-- Each sibling of child zero yields a different connector of terminal zero. -/
theorem delBranching_le {A : StaticArrays} {G : Cited.Graph} {ξ κ : ℕ}
    {pairIdx : ℕ → ℕ → ℕ → ℕ} (hA : A.Spec G ξ κ) (hPairs : A.PairSpec pairIdx) (j : ℕ) :
    branching A.x A.b j ≤ κ + 1 := by
  classical
  let k := branching A.x A.b j
  let siblings := Finset.Ico 1 k
  let other := fun c => if A.C.endA c = 0 then A.C.endB c else A.C.endA c
  have hk0 : 0 < k := branching_pos
  have hnum : k ≤ numGroups A.x A.b (j + 1) := by
    apply Nat.le_of_mul_le_mul_right (c := groupSize A.x A.b (j + 1))
    · rw [numGroups_mul_groupSize, ← groupSize_eq_mul_branching]
      exact groupSize_le_two_pow
    · exact groupSize_pos
  have hzero : 0 ∈ members A.x A.b (j + 1) 0 := by
    rw [mem_members_iff, groupOf, Nat.zero_div]
  have ht : 0 < A.C.numTerm := by rw [hA.numTerm_eq]; exact Nat.two_pow_pos _
  have pick : ∀ i, ∃ c, i ∈ siblings →
      c ∈ A.termConns 0 ∧ groupOf A.x A.b (j + 1) (other c) = i := by
    intro i
    by_cases hi : i ∈ siblings
    · obtain ⟨hi1, hik⟩ := Finset.mem_Ico.mp hi
      have hp0 : parentGroup A.x A.b j 0 = 0 := by simp [parentGroup]
      have hpi : parentGroup A.x A.b j i = 0 := by
        simpa only [Nat.zero_mul, Nat.zero_add] using (parentGroup_child (g := 0) hik)
      obtain ⟨σ, hσ, hm⟩ := hPairs.matching j 0 i (hp0.trans hpi.symm)
        (by omega) (hk0.trans_le hnum) (hik.trans_le hnum)
      obtain ⟨c, hc, hend⟩ := hm 0 hzero
      have ho := hσ.mapsTo hzero
      change σ 0 ∈ members A.x A.b (j + 1) i at ho
      have hs := mem_members_iff.mp ho
      have hσ0 : σ 0 ≠ 0 := by
        intro he
        rw [he, groupOf, Nat.zero_div] at hs
        omega
      have hcN := (hA.mem_pairConns (pairIdx j 0 i) c hc).1
      refine ⟨c, fun _ => ⟨(hA.mem_termConns 0 ht c).mpr ⟨hcN, ?_⟩, ?_⟩⟩
      · exact hend.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
      · rcases hend with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · simpa [other, h₁, h₂] using hs
        · simpa [other, h₁, h₂, hσ0] using hs
    · exact ⟨0, fun h => False.elim (hi h)⟩
  choose f hf using pick
  have hcard := Finset.card_le_card_of_injOn (s := siblings)
    (t := (A.termConns 0).toFinset) f
    (fun i hi => List.mem_toFinset.mpr (hf i hi).1)
    (fun i hi j hj he => ((hf i hi).2).symm.trans (he ▸ (hf j hj).2))
  rw [List.toFinset_card_of_nodup (hA.termConns_nodup 0)] at hcard
  have hs : siblings.card = k - 1 := Nat.card_Ico 1 k
  rw [hs] at hcard
  have hl := hA.termConns_length 0
  omega

/-- The number of ports is bounded by the product of the branching bounds. -/
theorem delNumTerm_le_pow {A : StaticArrays} {G : Cited.Graph} {ξ κ : ℕ}
    {pairIdx : ℕ → ℕ → ℕ → ℕ} (hA : A.Spec G ξ κ) (hPairs : A.PairSpec pairIdx) :
    A.C.numTerm ≤ (κ + 1) ^ leafDepth A.x A.b := by
  have h : ∀ n j, j + n = leafDepth A.x A.b →
      groupSize A.x A.b j ≤ (κ + 1) ^ n := by
    intro n
    induction n with
    | zero =>
      intro j hj
      rw [Nat.add_zero] at hj
      exact (groupSize_eq_one hA.b_pos hj.ge).le
    | succ n ih =>
      intro j hj
      rw [groupSize_eq_mul_branching, pow_succ']
      exact Nat.mul_le_mul (delBranching_le hA hPairs j) (ih (j + 1) (by omega))
  have H := h (leafDepth A.x A.b) 0 (Nat.zero_add _)
  rwa [groupSize_zero, ← hA.numTerm_eq] at H

/-- A polynomial cap for the number of ports and the terminal incidence bound. -/
def delPortCap (m : ℕ) : ℕ := (16 * m + 16) ^ 6

private theorem del_succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [pow_succ]
    omega

private theorem del_depth_squared_le (m : ℕ) : depthOf m ^ 2 ≤ 4 * xOf m := by
  let d := depthOf m
  let j := d - 1
  have hd : 2 ≤ d := two_le_depthOf m
  have hj : 1 ≤ j := by unfold j; omega
  have hlt : j < ceilRoot 2 (xOf m) := by
    change j < d
    unfold j
    omega
  have hcube : j ^ 3 ≤ xOf m := (pow_lt_of_lt_ceilRoot hlt).le
  have hsq : j ^ 2 ≤ j ^ 3 := by
    rw [pow_succ j 2]
    exact Nat.le_mul_of_pos_right _ hj
  have h : d ≤ 2 * j := by unfold j; omega
  calc
    depthOf m ^ 2 ≤ (2 * j) ^ 2 := Nat.pow_le_pow_left h _
    _ = 4 * j ^ 2 := by ring
    _ ≤ 4 * xOf m := Nat.mul_le_mul_left _ (hsq.trans hcube)

private theorem del_exp_le (m : ℕ) :
    (branchBits m + depthOf m) * depthOf m ≤ 6 * xOf m := by
  let d := depthOf m
  have hdx : d ≤ xOf m := ceilRoot_le_self 2 _
  have hb : branchBits m * d ≤ xOf m + d - 1 := Nat.div_mul_le_self _ _
  have hdd : d * d ≤ 4 * xOf m := by simpa only [pow_two] using del_depth_squared_le m
  change (branchBits m + d) * d ≤ _
  rw [Nat.add_mul]
  omega

private theorem del_kappa_le_pow (m : ℕ) :
    depthOf m * branchOf m + 1 ≤ 2 ^ (branchBits m + depthOf m) := by
  let d := depthOf m
  let B := branchOf m
  have hB : 1 ≤ B := Nat.one_le_two_pow
  calc
    d * B + 1 ≤ (d + 1) * B := by rw [Nat.add_mul, Nat.one_mul]; omega
    _ ≤ 2 ^ d * B := Nat.mul_le_mul_right _ (del_succ_le_two_pow d)
    _ = 2 ^ (branchBits m + depthOf m) := by
      rw [pow_add, Nat.mul_comm]
      rfl

private theorem del_two_pow_x_le (m : ℕ) : 2 ^ xOf m ≤ 16 * m + 16 := by
  have h := Nat.pow_pred_clog_lt_self (b := 2) (x := 8 * m + 8) (by decide) (by omega)
  change 2 ^ (xOf m - 1) < 8 * m + 8 at h
  have hx := three_le_xOf m
  have he : xOf m = (xOf m - 1) + 1 := by omega
  calc
    2 ^ xOf m = 2 ^ (xOf m - 1) * 2 := by conv_lhs => rw [he, pow_succ]
    _ ≤ 16 * m + 16 := by omega

private theorem del_model_caps (m : ℕ) :
    (depthOf m * branchOf m + 1) ^ depthOf m ≤ delPortCap m := by
  calc
    (depthOf m * branchOf m + 1) ^ depthOf m ≤
        (2 ^ (branchBits m + depthOf m)) ^ depthOf m :=
      Nat.pow_le_pow_left (del_kappa_le_pow m) _
    _ ≤ 2 ^ (6 * xOf m) := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by decide) (del_exp_le m)
    _ = (2 ^ xOf m) ^ 6 := by rw [Nat.mul_comm 6, pow_mul]
    _ ≤ delPortCap m := Nat.pow_le_pow_left (del_two_pow_x_le m) _

theorem HierConcrete.delPortCap_bounds {a : ℕ} (x : HierConcrete) (h : x.H.Rel a x.ms) :
    x.H.A.C.numTerm ≤ delPortCap x.m ∧ x.H.κ + 1 ≤ delPortCap x.m := by
  let d := depthOf x.m
  let K := d * branchOf x.m + 1
  have hK : 0 < K := Nat.succ_pos _
  have hκ : x.H.κ + 1 ≤ K := Nat.succ_le_succ h.fits.conns
  have hd : x.depth ≤ d := h.fits.depth
  have hPorts := delNumTerm_le_pow h.spec.arrays h.spec.pairs
  refine ⟨hPorts.trans ((Nat.pow_le_pow_left hκ _).trans
    ((Nat.pow_le_pow_right hK hd).trans (del_model_caps x.m))), ?_⟩
  have hd₁ : 1 ≤ d := (by decide : 1 ≤ 2).trans (two_le_depthOf x.m)
  have hp : K ^ 1 ≤ K ^ d := Nat.pow_le_pow_right hK hd₁
  rw [pow_one] at hp
  exact hκ.trans (hp.trans (del_model_caps x.m))

end MinCostFlow.HierPaths

end
