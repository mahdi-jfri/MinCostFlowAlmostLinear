module

public import MinCostFlow.HierPaths.DeleteState
public import MinCostFlow.HierPaths.QueryGroups
public import MinCostFlow.HierPaths.Sibling

/-!
# The connector choice read from the pair cursors

`GetPath` takes the connector between two children `Y` and `Z` of a group from the cursor of
their pair array. This file proves that this choice meets
`IsSiblingChoice` of `HierPaths/QueryGroups.lean`, for a state with the invariant `DelInv`.

The static arrays must say which pair array belongs to two siblings (`pairIdx j Y Z`) and what it
holds (`PairSpec`): its connectors join `Y` and `Z`, and they contain a perfect matching `σ` from
the members of `Y` to those of `Z`. Then `exists_surviving_matching_edge` gives an
eligible connector in the array, so by the cursor invariant the cursor is before the end and its
entry is eligible (`isSiblingChoice_pick`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

namespace StaticArrays

variable (A : StaticArrays)

/-- The specification of the pair arrays of the siblings `Y ≠ Z` (children at depth `j + 1` of
one group, both among the `numGroups` groups at that depth): the array `pairConns (pairIdx j Y Z)` exists, each of its connectors has one endpoint
in `Y` and the other in `Z`, and it contains a perfect matching `σ` from `Y` to `Z`. -/
structure PairSpec (pairIdx : ℕ → ℕ → ℕ → ℕ) : Prop where
  lt : ∀ j Y Z, parentGroup A.x A.b j Y = parentGroup A.x A.b j Z → Y ≠ Z →
    Y < numGroups A.x A.b (j + 1) → Z < numGroups A.x A.b (j + 1) →
    pairIdx j Y Z < A.numPairs
  sides : ∀ j Y Z, parentGroup A.x A.b j Y = parentGroup A.x A.b j Z → Y ≠ Z →
    Y < numGroups A.x A.b (j + 1) → Z < numGroups A.x A.b (j + 1) →
    ∀ c ∈ A.pairConns (pairIdx j Y Z),
      (A.C.endA c ∈ members A.x A.b (j + 1) Y ∧ A.C.endB c ∈ members A.x A.b (j + 1) Z) ∨
      (A.C.endB c ∈ members A.x A.b (j + 1) Y ∧ A.C.endA c ∈ members A.x A.b (j + 1) Z)
  matching : ∀ j Y Z, parentGroup A.x A.b j Y = parentGroup A.x A.b j Z → Y ≠ Z →
    Y < numGroups A.x A.b (j + 1) → Z < numGroups A.x A.b (j + 1) →
    ∃ σ : ℕ → ℕ, Set.BijOn σ (members A.x A.b (j + 1) Y) (members A.x A.b (j + 1) Z) ∧
      ∀ y ∈ members A.x A.b (j + 1) Y, ∃ c ∈ A.pairConns (pairIdx j Y Z),
        (A.C.endA c = y ∧ A.C.endB c = σ y) ∨ (A.C.endB c = y ∧ A.C.endA c = σ y)

/-- The connector between the children `Y` and `Z` at depth `j + 1` that the state offers: the
entry under the cursor of their pair array. -/
def pick (pairIdx : ℕ → ℕ → ℕ → ℕ) (st : DelState) (j Y Z : ℕ) : ℕ :=
  (A.pairConns (pairIdx j Y Z)).getD (st.pairCur (pairIdx j Y Z)) 0

end StaticArrays

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

namespace StaticArrays

variable (A : StaticArrays) {G : Graph} {ξ κ : ℕ}

public section

/-- The connectors under the pair cursors form a sibling choice for the surviving terminals. -/
theorem isSiblingChoice_pick {pairIdx : ℕ → ℕ → ℕ → ℕ} {st : DelState} (hA : A.Spec G ξ κ)
    (hP : A.PairSpec pairIdx) (hinv : A.DelInv G st) :
    A.C.IsSiblingChoice A.x A.b (A.pick pairIdx st) (A.surv st) := by
  intro j Y Z u v hu hv huY hvZ hpar hne
  have hsurvG : ∀ t ∈ A.surv st, t < 2 ^ A.x ∧ t ∉ globalLost A.x A.b st.loss.failed := by
    intro t ht
    obtain ⟨hlt, hg⟩ := (A.mem_surv).mp ht
    rw [hinv.loss.glob] at hg
    exact ⟨hA.numTerm_eq ▸ hlt, hg⟩
  have hY : Y < numGroups A.x A.b (j + 1) :=
    (mem_members_iff.mp huY) ▸ groupOf_lt_numGroups (hsurvG u hu).1
  have hZ : Z < numGroups A.x A.b (j + 1) :=
    (mem_members_iff.mp hvZ) ▸ groupOf_lt_numGroups (hsurvG v hv).1
  obtain ⟨σ, hσ, hmatch⟩ := hP.matching j Y Z hpar hne hY hZ
  obtain ⟨y, hyY, hy, hσy⟩ := exists_surviving_matching_edge hA.b_pos huY (hsurvG u hu).1
    (hsurvG u hu).2 hvZ (hsurvG v hv).1 (hsurvG v hv).2 hσ
  obtain ⟨c, hc, hends⟩ := hmatch y hyY
  have hp := hP.lt j Y Z hpar hne hY hZ
  have hcinv := hinv.pairCur _ hp
  have hyN : y < A.C.numTerm := by
    rw [hA.numTerm_eq]; exact Finset.mem_range.mp (members_subset_range hY hyY)
  have hσN : σ y < A.C.numTerm := by
    rw [hA.numTerm_eq]; exact Finset.mem_range.mp (members_subset_range hZ (hσ.mapsTo hyY))
  have hys : y ∈ A.surv st := (A.mem_surv).mpr ⟨hyN, by rw [hinv.loss.glob]; exact hy⟩
  have hσs : σ y ∈ A.surv st := (A.mem_surv).mpr ⟨hσN, by rw [hinv.loss.glob]; exact hσy⟩
  have hel : A.C.Eligible (A.surv st) c := by
    refine ⟨(hA.mem_pairConns _ c hc).1, ?_⟩
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact ⟨hys, hσs⟩
    · rw [h1, h2]; exact ⟨hσs, hys⟩
  -- The cursor is before the end, since the array has an eligible entry.
  have hlt : st.pairCur (pairIdx j Y Z) < (A.pairConns (pairIdx j Y Z)).length := by
    rcases Nat.lt_or_ge (st.pairCur (pairIdx j Y Z)) (A.pairConns (pairIdx j Y Z)).length
      with h | h
    · exact h
    · exfalso
      have hall := (hcinv.eq_len_iff).mp (le_antisymm hcinv.1 h)
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
      have := hall i hi
      rw [pairValid, List.getD_eq_getElem _ _ hi] at this
      simp only [decide_eq_false_iff_not] at this
      exact this hel
  have hv' := hcinv.2.2 hlt
  rw [pairValid] at hv'
  simp only [decide_eq_true_eq] at hv'
  refine ⟨hv', ?_⟩
  have hmem : A.pick pairIdx st j Y Z ∈ A.pairConns (pairIdx j Y Z) := by
    rw [pick, List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
  exact hP.sides j Y Z hpar hne hY hZ _ hmem

end

end StaticArrays

end MinCostFlow.HierPaths
