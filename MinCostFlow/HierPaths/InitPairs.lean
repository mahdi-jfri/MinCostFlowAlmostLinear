module

public import MinCostFlow.HierPaths.InitProg
public import MinCostFlow.HierPaths.InitBlockLen

/-!
# The pair arrays of the static model

`staticArrays` stores, for the pair number `pairNum` of each connector, the list of connectors
with that number, and the model looks the pair of siblings `Y, Z` up at `pairIdxOf j Y Z`. This
file proves that the pair arrays meet their specification (`PairSpec` of `ModelPick.lean`), in
the form with `Y, Z < numGroups (j + 1)`: `staticArrays_pairSpecIn`.

The key step is that a pair number determines the depth and the two children
(`pairNum_eq_pairIdxOf_iff`): the depth and the first child come from the quotient by `2^b`,
and the second child from its residue, since the children of one group are fewer than `2^b`
consecutive numbers.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- A list of pairs whose first and second entries have no repetition gives bijections between
them, both ways. -/
theorem exists_bijOn_of_nodup {α : Type*} (l : List (ℕ × ℕ × α))
    (h1 : (l.map Prod.fst).Nodup) (h2 : (l.map fun q => q.2.1).Nodup) :
    ∃ σ : ℕ → ℕ, Set.BijOn σ (l.map Prod.fst).toFinset (l.map fun q => q.2.1).toFinset ∧
      ∀ q ∈ l, σ q.1 = q.2.1 := by
  classical
  let F := l.map Prod.fst
  let S := l.map fun q => q.2.1
  have hlen : F.length = S.length := by simp [F, S]
  refine ⟨fun y => S.getD (F.idxOf y) 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro y hy
    have hy' : y ∈ F := by simpa [F] using hy
    have hi : F.idxOf y < S.length := hlen ▸ List.idxOf_lt_length_iff.mpr hy'
    simp only [List.coe_toFinset, Set.mem_ofPred_eq]
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  · intro y₁ hy₁ y₂ hy₂ heq
    have hy₁' : y₁ ∈ F := by simpa [F] using hy₁
    have hy₂' : y₂ ∈ F := by simpa [F] using hy₂
    have hi₁ : F.idxOf y₁ < S.length := hlen ▸ List.idxOf_lt_length_iff.mpr hy₁'
    have hi₂ : F.idxOf y₂ < S.length := hlen ▸ List.idxOf_lt_length_iff.mpr hy₂'
    simp only at heq
    rw [List.getD_eq_getElem _ _ hi₁, List.getD_eq_getElem _ _ hi₂] at heq
    have hidx := (h2.getElem_inj_iff).mp heq
    rw [← List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hy₁'),
      ← List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hy₂')]
    simp only [hidx]
  · intro z hz
    have hz' : z ∈ S := by simpa [S] using hz
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz'
    have hiF : i < F.length := hlen ▸ hi
    refine ⟨F[i], by simpa [F] using List.getElem_mem hiF, ?_⟩
    simp only
    rw [h1.idxOf_getElem, List.getD_eq_getElem _ _ hi]
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    have hiF : i < F.length := by simpa [F] using hi
    have hiS : i < S.length := by simpa [S] using hi
    have e1 : l[i].1 = F[i] := by simp [F]
    have e2 : l[i].2.1 = S[i] := by simp [S]
    simp only
    rw [e1, h1.idxOf_getElem, List.getD_eq_getElem _ _ (hlen ▸ hiF), e2]

/-- Division with remainder is unique: `a · m + r = a' · m + r'` with `r, r' < m` gives `a = a'`
and `r = r'`. -/
theorem eq_of_mul_add_eq {m a r a' r' : ℕ} (hr : r < m) (hr' : r' < m)
    (h : a * m + r = a' * m + r') : a = a' ∧ r = r' := by
  have hm : 0 < m := by omega
  have h1 : (a * m + r) / m = a := by
    rw [Nat.mul_comm, Nat.mul_add_div hm, Nat.div_eq_of_lt hr, Nat.add_zero]
  have h2 : (a' * m + r') / m = a' := by
    rw [Nat.mul_comm, Nat.mul_add_div hm, Nat.div_eq_of_lt hr', Nat.add_zero]
  have ha : a = a' := by rw [← h1, ← h2, h]
  subst ha
  exact ⟨rfl, by omega⟩

/-- Two numbers in one interval of fewer than `m + 1` consecutive numbers with the same residue
mod `m` are equal. -/
theorem eq_of_mod_eq_of_Ico {L n m u v : ℕ} (hn : n ≤ m) (hu : u ∈ Finset.Ico L (L + n))
    (hv : v ∈ Finset.Ico L (L + n)) (h : u % m = v % m) : u = v := by
  simp only [Finset.mem_Ico] at hu hv
  rcases Nat.lt_or_ge u v with huv | huv
  · have h0 : (v - u) % m = 0 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
    have hlt : v - u < m := by omega
    rw [Nat.mod_eq_of_lt hlt] at h0
    omega
  · have h0 : (u - v) % m = 0 := Nat.sub_mod_eq_zero_of_mod_eq h
    have hlt : u - v < m := by omega
    rw [Nat.mod_eq_of_lt hlt] at h0
    omega

variable {x b : ℕ}

theorem childGroups_eq_Ico (j g : ℕ) :
    childGroups x b j g = Finset.Ico (g * branching x b j) (g * branching x b j + branching x b j) := by
  rw [childGroups, Nat.succ_mul]

/-- **A pair number determines the pair.** For two children `c < c'` of a group at depth `t`,
and two distinct children `Y, Z` of one group at depth `j`, the pair number of `c, c'` equals
`pairIdxOf j Y Z` exactly when `t = j` and `c, c'` are `min Y Z, max Y Z`. The depth and `c`
come from the quotient by `2^b` (as `c` and `min Y Z` are below `2^x`); then `c` and `min Y Z`
have the same parent, so `c'` and `max Y Z` are children of one group, which has at most `2^b`
children (`branching_le_pow`), and they have the same residue mod `2^b`. -/
theorem pairNum_eq_pairIdxOf_iff {t g c c' j g' Y Z : ℕ} (hc : c ∈ childGroups x b t g)
    (hc' : c' ∈ childGroups x b t g) (hcc : c < c') (hY : Y ∈ childGroups x b j g')
    (hZ : Z ∈ childGroups x b j g') (hc2 : c < 2 ^ x) (hYZ2 : min Y Z < 2 ^ x) :
    (t * 2 ^ x + c) * 2 ^ b + c' % 2 ^ b = pairIdxOf x b j Y Z ↔
      t = j ∧ c = min Y Z ∧ c' = max Y Z := by
  constructor
  · intro h
    unfold pairIdxOf at h
    obtain ⟨h1, h2⟩ := eq_of_mul_add_eq (Nat.mod_lt _ (Nat.two_pow_pos b))
      (Nat.mod_lt _ (Nat.two_pow_pos b)) h
    obtain ⟨ht, hcm⟩ := eq_of_mul_add_eq hc2 hYZ2 h1
    subst ht
    refine ⟨rfl, hcm, ?_⟩
    have hmin : min Y Z ∈ childGroups x b t g' := by
      rcases min_choice Y Z with e | e <;> rw [e] <;> assumption
    have hmax : max Y Z ∈ childGroups x b t g' := by
      rcases max_choice Y Z with e | e <;> rw [e] <;> assumption
    have hgg : g = g' := by
      rw [mem_childGroups_iff] at hc hmin
      rw [← hc, ← hmin, hcm]
    subst hgg
    rw [childGroups_eq_Ico] at hc' hmax
    exact eq_of_mod_eq_of_Ico (branching_le_pow t) hc' hmax h2
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- Two different children `Y, Z` of one group at depth `j`, with `Y` a group at depth `j + 1`:
the group at depth `j` has more than one member, `j` is below the leaf depth, and the parent is a
group at depth `j`. -/
theorem sibling_facts (hb : 0 < b) {j Y Z : ℕ} (hY : Y < numGroups x b (j + 1))
    (hpar : parentGroup x b j Y = parentGroup x b j Z) (hne : Y ≠ Z) :
    1 < groupSize x b j ∧ j < leafDepth x b ∧ parentGroup x b j Y < numGroups x b j := by
  have h1 : 1 < groupSize x b j := by
    by_contra hc
    have hg1 : groupSize x b j = 1 := by have := (groupSize_pos : 0 < groupSize x b j); omega
    have hbr : branching x b j = 1 := by
      have h := (groupSize_eq_mul_branching : groupSize x b j = _)
      rw [hg1] at h
      exact (Nat.eq_one_of_mul_eq_one_right h.symm)
    simp only [parentGroup, hbr, Nat.div_one] at hpar
    exact hne hpar
  refine ⟨h1, ?_, ?_⟩
  · by_contra hc
    rw [groupSize_eq_one hb (Nat.le_of_not_lt hc)] at h1
    exact lt_irrefl _ h1
  · have e1 := (numGroups_mul_groupSize : numGroups x b j * groupSize x b j = 2 ^ x)
    have e2 := (numGroups_mul_groupSize : numGroups x b (j + 1) * groupSize x b (j + 1) = 2 ^ x)
    rw [groupSize_eq_mul_branching] at e1
    have e3 : numGroups x b (j + 1) = numGroups x b j * branching x b j := by
      rw [← Nat.mul_assoc] at e1
      exact Nat.eq_of_mul_eq_mul_right groupSize_pos (e2.trans e1.symm)
    unfold parentGroup
    rw [Nat.div_lt_iff_lt_mul branching_pos, ← e3]
    exact hY

variable {H : HierData} {owner : ℕ → ℕ} {label : ℕ → Option ℕ}

theorem staticArrays_x : (staticArrays H x b owner label).x = x := rfl

theorem staticArrays_b : (staticArrays H x b owner label).b = b := rfl

/-- The connectors of `staticArrays` with a given pair number are its pair array. -/
theorem mem_pairConns_staticArrays {k p : ℕ} :
    k ∈ (staticArrays H x b owner label).pairConns p ↔
      k < (connRecs H x b).length ∧ pairNum x b ((connRecs H x b).getD k default) = p := by
  simp [staticArrays, List.mem_filter, List.mem_range]

/-- Every connector of `H.conn t c c'` is stored, under the pair number of `c, c'`. -/
theorem exists_pairConns_of_conn {t g c c' : ℕ} (ht : t < leafDepth x b)
    (hg : g < numGroups x b t) (hc : c ∈ childGroups x b t g) (hc' : c' ∈ childGroups x b t g)
    (hcc : c < c') {q : ℕ × ℕ × List ℕ} (hq : q ∈ H.conn t c c') :
    ∃ k ∈ (staticArrays H x b owner label).pairConns ((t * 2 ^ x + c) * 2 ^ b + c' % 2 ^ b),
      (staticArrays H x b owner label).C.endA k = q.1 ∧
        (staticArrays H x b owner label).C.endB k = q.2.1 := by
  have hr : (⟨t, g, c, c', q.1, q.2.1, flatWalk H x b t g q.1 q.2.2⟩ : ConnRec) ∈
      connRecs H x b :=
    mem_connRecs.mpr ⟨t, ht, g, hg, c, hc, c', hc', hcc, q, hq, rfl⟩
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hr
  have hgetD : (connRecs H x b).getD k default =
      ⟨t, g, c, c', q.1, q.2.1, flatWalk H x b t g q.1 q.2.2⟩ := by
    rw [List.getD_eq_getElem _ _ hk, hget]
  refine ⟨k, mem_pairConns_staticArrays.mpr ⟨hk, by rw [hgetD]; rfl⟩, ?_, ?_⟩
  · simp only [staticArrays, connSystem, hgetD]
  · simp only [staticArrays, connSystem, hgetD]

/-- The stored connectors with the pair number of `pairIdxOf j Y Z`, for different children
`Y, Z` of one group at depth `j`, are exactly those of `H.conn j (min Y Z) (max Y Z)`: every
stored connector with this number comes from that list (by `pairNum_eq_pairIdxOf_iff`). -/
theorem conn_of_mem_pairConns {j Y Z : ℕ} (hY : Y < numGroups x b (j + 1))
    (hZ : Z < numGroups x b (j + 1)) (hpar : parentGroup x b j Y = parentGroup x b j Z)
    {k : ℕ} (hk : k ∈ (staticArrays H x b owner label).pairConns (pairIdxOf x b j Y Z)) :
    ∃ q ∈ H.conn j (min Y Z) (max Y Z),
      (staticArrays H x b owner label).C.endA k = q.1 ∧
        (staticArrays H x b owner label).C.endB k = q.2.1 := by
  obtain ⟨hklt, hnum⟩ := mem_pairConns_staticArrays.mp hk
  have hr : (connRecs H x b).getD k default ∈ connRecs H x b := by
    rw [List.getD_eq_getElem _ _ hklt]; exact List.getElem_mem hklt
  obtain ⟨t, _, g, hg, c, hc, c', hc', hcc, q, hq, hrec⟩ := mem_connRecs.mp hr
  rw [hrec] at hnum
  have hc2 : c < 2 ^ x := (childGroups_lt_numGroups hg hc).trans_le (numGroups_le_pow _)
  have hm2 : min Y Z < 2 ^ x := (min_le_left Y Z).trans_lt (hY.trans_le (numGroups_le_pow _))
  have hYc : Y ∈ childGroups x b j (parentGroup x b j Y) := mem_childGroups_iff.mpr rfl
  have hZc : Z ∈ childGroups x b j (parentGroup x b j Y) := mem_childGroups_iff.mpr hpar.symm
  obtain ⟨rfl, rfl, rfl⟩ := (pairNum_eq_pairIdxOf_iff hc hc' hcc hYc hZc hc2 hm2).mp hnum
  refine ⟨q, hq, ?_, ?_⟩
  · simp only [staticArrays, connSystem, hrec]
  · simp only [staticArrays, connSystem, hrec]

/-- The specification `StaticArrays.PairSpec` of the pair arrays, for the children
`Y, Z < numGroups (j + 1)` only. -/
structure PairSpecIn (A : StaticArrays) (pairIdx : ℕ → ℕ → ℕ → ℕ) : Prop where
  lt : ∀ j Y Z, Y < numGroups A.x A.b (j + 1) → Z < numGroups A.x A.b (j + 1) →
    parentGroup A.x A.b j Y = parentGroup A.x A.b j Z → Y ≠ Z → pairIdx j Y Z < A.numPairs
  sides : ∀ j Y Z, Y < numGroups A.x A.b (j + 1) → Z < numGroups A.x A.b (j + 1) →
    parentGroup A.x A.b j Y = parentGroup A.x A.b j Z → Y ≠ Z →
    ∀ c ∈ A.pairConns (pairIdx j Y Z),
      (A.C.endA c ∈ members A.x A.b (j + 1) Y ∧ A.C.endB c ∈ members A.x A.b (j + 1) Z) ∨
      (A.C.endB c ∈ members A.x A.b (j + 1) Y ∧ A.C.endA c ∈ members A.x A.b (j + 1) Z)
  matching : ∀ j Y Z, Y < numGroups A.x A.b (j + 1) → Z < numGroups A.x A.b (j + 1) →
    parentGroup A.x A.b j Y = parentGroup A.x A.b j Z → Y ≠ Z →
    ∃ σ : ℕ → ℕ, Set.BijOn σ (members A.x A.b (j + 1) Y) (members A.x A.b (j + 1) Z) ∧
      ∀ y ∈ members A.x A.b (j + 1) Y, ∃ c ∈ A.pairConns (pairIdx j Y Z),
        (A.C.endA c = y ∧ A.C.endB c = σ y) ∨ (A.C.endB c = y ∧ A.C.endA c = σ y)

/-- The perfect matching of the children `min Y Z < max Y Z`, from `IsValid.conn_perfect`. -/
theorem perfect_of_siblings (hb : 0 < b) (hH : H.IsValid x b) {j Y Z : ℕ}
    (hY : Y < numGroups x b (j + 1)) (hpar : parentGroup x b j Y = parentGroup x b j Z)
    (hne : Y ≠ Z) :
    j < leafDepth x b ∧ parentGroup x b j Y < numGroups x b j ∧
      min Y Z ∈ childGroups x b j (parentGroup x b j Y) ∧
      max Y Z ∈ childGroups x b j (parentGroup x b j Y) ∧ min Y Z < max Y Z ∧
      HierData.IsPerfectOn x b (j + 1) (min Y Z) (max Y Z) (H.conn j (min Y Z) (max Y Z)) := by
  obtain ⟨hgs, hj, hg⟩ := sibling_facts hb hY hpar hne
  have hYc : Y ∈ childGroups x b j (parentGroup x b j Y) := mem_childGroups_iff.mpr rfl
  have hZc : Z ∈ childGroups x b j (parentGroup x b j Y) := mem_childGroups_iff.mpr hpar.symm
  have hmin : min Y Z ∈ childGroups x b j (parentGroup x b j Y) := by
    rcases min_choice Y Z with e | e <;> rw [e] <;> assumption
  have hmax : max Y Z ∈ childGroups x b j (parentGroup x b j Y) := by
    rcases max_choice Y Z with e | e <;> rw [e] <;> assumption
  have hlt : min Y Z < max Y Z := min_lt_max.mpr hne
  exact ⟨hj, hg, hmin, hmax, hlt, hH.conn_perfect j _ hgs hg _ hmin _ hmax hlt⟩

/-- **The pair arrays of `staticArrays` meet `PairSpecIn`** for a valid hierarchy, with the pair
numbers `pairIdxOf`. -/
theorem staticArrays_pairSpecIn (hb : 0 < b) (hH : H.IsValid x b) :
    PairSpecIn (staticArrays H x b owner label) (pairIdxOf x b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j Y Z hY _ hpar hne
    simp only [staticArrays_x, staticArrays_b] at *
    obtain ⟨hj, hg, hmin, hmax, hlt, hP⟩ := perfect_of_siblings hb hH hY hpar hne
    -- The matching is not empty, since the group `min Y Z` has a member.
    have hne' : (members x b (j + 1) (min Y Z)).Nonempty := by
      rw [← Finset.card_pos, card_members]; exact groupSize_pos
    obtain ⟨u, hu⟩ := hne'
    rw [← hP.2.1, List.mem_toFinset, List.mem_map] at hu
    obtain ⟨q, hq, _⟩ := hu
    obtain ⟨k, hk, _⟩ := exists_pairConns_of_conn (owner := owner) (label := label) hj hg hmin
      hmax hlt hq
    obtain ⟨hklt, hnum⟩ := mem_pairConns_staticArrays.mp hk
    have hr : (connRecs H x b).getD k default ∈ connRecs H x b := by
      rw [List.getD_eq_getElem _ _ hklt]; exact List.getElem_mem hklt
    have := pairNum_lt hr
    rw [hnum] at this
    exact this
  · intro j Y Z hY hZ hpar hne k hk
    simp only [staticArrays_x, staticArrays_b] at *
    obtain ⟨-, -, -, -, -, hP⟩ := perfect_of_siblings hb hH hY hpar hne
    obtain ⟨q, hq, hA, hB⟩ := conn_of_mem_pairConns hY hZ hpar hk
    have h1 : q.1 ∈ members x b (j + 1) (min Y Z) := by
      rw [← hP.2.1, List.mem_toFinset]; exact List.mem_map_of_mem hq
    have h2 : q.2.1 ∈ members x b (j + 1) (max Y Z) := by
      rw [← hP.2.2.2, List.mem_toFinset]; exact List.mem_map_of_mem (f := fun q => q.2.1) hq
    rw [hA, hB]
    rcases le_total Y Z with hle | hle
    · rw [min_eq_left hle] at h1
      rw [max_eq_right hle] at h2
      exact Or.inl ⟨h1, h2⟩
    · rw [min_eq_right hle] at h1
      rw [max_eq_left hle] at h2
      exact Or.inr ⟨h2, h1⟩
  · intro j Y Z hY _ hpar hne
    simp only [staticArrays_x, staticArrays_b] at *
    obtain ⟨hj, hg, hmin, hmax, hlt, hP⟩ := perfect_of_siblings hb hH hY hpar hne
    obtain ⟨hn1, hm1, hn2, hm2⟩ := hP
    have hidx : pairIdxOf x b j Y Z =
        (j * 2 ^ x + min Y Z) * 2 ^ b + max Y Z % 2 ^ b := rfl
    rcases le_total Y Z with hle | hle
    · -- `Y` is the first child: match along the list.
      obtain ⟨σ, hσ, hσq⟩ := exists_bijOn_of_nodup _ hn1 hn2
      rw [hm1, hm2, min_eq_left hle, max_eq_right hle] at hσ
      refine ⟨σ, hσ, fun y hy => ?_⟩
      rw [← min_eq_left hle, ← hm1, List.mem_toFinset, List.mem_map] at hy
      obtain ⟨q, hq, rfl⟩ := hy
      obtain ⟨k, hk, hA, hB⟩ := exists_pairConns_of_conn (owner := owner) (label := label) hj hg
        hmin hmax hlt hq
      exact ⟨k, hidx ▸ hk, Or.inl ⟨hA, by rw [hB, hσq q hq]⟩⟩
    · -- `Y` is the second child: match along the swapped list.
      let l' := (H.conn j (min Y Z) (max Y Z)).map fun q => (q.2.1, q.1, q.2.2)
      have e1 : l'.map Prod.fst = (H.conn j (min Y Z) (max Y Z)).map fun q => q.2.1 := by
        simp [l', Function.comp_def]
      have e2 : (l'.map fun q => q.2.1) = (H.conn j (min Y Z) (max Y Z)).map Prod.fst := by
        simp [l', Function.comp_def]
      obtain ⟨σ, hσ, hσq⟩ := exists_bijOn_of_nodup l' (e1 ▸ hn2) (e2 ▸ hn1)
      rw [e1, e2, hm1, hm2, min_eq_right hle, max_eq_left hle] at hσ
      refine ⟨σ, hσ, fun y hy => ?_⟩
      rw [← max_eq_left hle, ← hm2, List.mem_toFinset, List.mem_map] at hy
      obtain ⟨q, hq, rfl⟩ := hy
      have hσy : σ q.2.1 = q.1 := hσq (q.2.1, q.1, q.2.2) (List.mem_map_of_mem hq)
      obtain ⟨k, hk, hA, hB⟩ := exists_pairConns_of_conn (owner := owner) (label := label) hj hg
        hmin hmax hlt hq
      exact ⟨k, hidx ▸ hk, Or.inr ⟨hB, by rw [hA, hσy]⟩⟩

/-- The residue step of `pairOfIdx`: for `L ≤ c' < L + m`, the number
`(c' mod m + m − L mod m) mod m` is `c' − L`. -/
theorem mod_sub_mod_eq {m L c' : ℕ} (hL : L ≤ c') (hlt : c' < L + m) :
    (c' % m + m - L % m) % m = c' - L := by
  have hm : 0 < m := by omega
  obtain ⟨d, rfl⟩ : ∃ d, c' = L + d := ⟨c' - L, by omega⟩
  have hd : d < m := by omega
  have hr : L % m < m := Nat.mod_lt _ hm
  rw [Nat.add_sub_cancel_left, Nat.add_mod, Nat.mod_eq_of_lt hd]
  rcases Nat.lt_or_ge (L % m + d) m with h | h
  · rw [Nat.mod_eq_of_lt h, show L % m + d + m - L % m = d + m by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hd]
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega : L % m + d - m < m),
      show L % m + d - m + m - L % m = d by omega, Nat.mod_eq_of_lt hd]

/-- **`pairOfIdx` reads a pair back** from its pair index: for children `c < c'` of one group
at depth `j`, with `c < 2^x`. -/
theorem pairOfIdx_pairIdxOf {j g c c' : ℕ} (hc : c ∈ childGroups x b j g)
    (hc' : c' ∈ childGroups x b j g) (hcc : c < c') (hc2 : c < 2 ^ x) :
    pairOfIdx x b (pairIdxOf x b j c c') = (j, c, c') := by
  have hmin : min c c' = c := min_eq_left hcc.le
  have hmax : max c c' = c' := max_eq_right hcc.le
  have hk : pairIdxOf x b j c c' = (j * 2 ^ x + c) * 2 ^ b + c' % 2 ^ b := by
    rw [pairIdxOf, hmin, hmax]
  have hr : c' % 2 ^ b < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos b)
  have hdiv : pairIdxOf x b j c c' / 2 ^ b = j * 2 ^ x + c := by
    rw [hk, Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos b), Nat.div_eq_of_lt hr,
      Nat.add_zero]
  have hmod : pairIdxOf x b j c c' % 2 ^ b = c' % 2 ^ b := by
    rw [hk, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  have hj : (j * 2 ^ x + c) / 2 ^ x = j := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos x), Nat.div_eq_of_lt hc2, Nat.add_zero]
  have hcm : (j * 2 ^ x + c) % 2 ^ x = c := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hc2]
  have hpar : c / branching x b j = g := mem_childGroups_iff.mp hc
  rw [childGroups_eq_Ico] at hc'
  simp only [Finset.mem_Ico] at hc'
  have hbr := branching_le_pow (x := x) (b := b) j
  unfold pairOfIdx
  simp only [hdiv, hmod, hj, hcm, hpar]
  rw [mod_sub_mod_eq hc'.1 (by omega)]
  simp only [Prod.mk.injEq, true_and]
  omega

end MinCostFlow.HierPaths
