module

public import MinCostFlow.HierPaths.DeleteStep

/-!
# Refreshing cursors in any order, with repeats

The model `deleteState` moves the cursor of each touched vertex and each touched pair once, and
the lists `touchedVerts` and `touchedPairs` have no repeats. The program does not need to remove
repeats: moving a cursor a second time does nothing, since `advance` stops at a valid entry or at
the end (`advance_advance`). So the program can walk the owners of the new lost terminals and the
walks of the new ineligible connectors as they come, with repeats. This file proves this:

* `advance_advance`: `advance` is idempotent;
* `refreshAll_eq`: moving the cursors of a list of keys one after the other gives, for each key
  in the list, the moved cursor, and for every other key the old one;
* `refreshOut`: the keys whose cursor reaches the end in such a pass, reported at the first
  time; `nodup_refreshOut` and `mem_refreshOut` say it has no repeats and contains exactly the
  keys of the list whose cursor was before the end and is at the end afterwards.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

/-- `advance` is idempotent. -/
theorem advance_advance (valid : ℕ → Bool) {N c : ℕ} (hc : c ≤ N) :
    advance valid N (advance valid N c) = advance valid N c := by
  have hle := advance_le valid hc
  rcases Nat.lt_or_ge (advance valid N c) N with h | h
  · exact advance_of_valid valid h (advance_valid valid N c h)
  · have : advance valid N c = N := le_antisymm hle h
    rw [this, advance]
    simp

/-- Move the cursor of each key of `ks`, one after the other. -/
def refreshAll (valid : ℕ → ℕ → Bool) (len : ℕ → ℕ) (cur : ℕ → ℕ) (ks : List ℕ) : ℕ → ℕ :=
  ks.foldl (fun cur k => Function.update cur k (advance (valid k) (len k) (cur k))) cur

theorem refreshAll_eq (valid : ℕ → ℕ → Bool) (len : ℕ → ℕ) :
    ∀ (ks : List ℕ) (cur : ℕ → ℕ), (∀ k ∈ ks, cur k ≤ len k) →
      refreshAll valid len cur ks =
        fun k => if k ∈ ks then advance (valid k) (len k) (cur k) else cur k
  | [], cur, _ => by funext k; simp [refreshAll]
  | a :: ks, cur, hcur => by
    have hcur' : ∀ k ∈ ks,
        Function.update cur a (advance (valid a) (len a) (cur a)) k ≤ len k := by
      intro k hk'
      by_cases hk : k = a
      · subst hk; simp only [Function.update_self]
        exact advance_le _ (hcur k List.mem_cons_self)
      · rw [Function.update_of_ne hk]; exact hcur k (List.mem_cons_of_mem _ hk')
    have ih := refreshAll_eq valid len ks _ hcur'
    simp only [refreshAll, List.foldl_cons] at ih ⊢
    rw [ih]
    funext k
    by_cases hk : k = a
    · subst hk
      simp only [Function.update_self, List.mem_cons, true_or, if_true]
      split_ifs
      · exact advance_advance _ (hcur k List.mem_cons_self)
      · rfl
    · simp only [Function.update_of_ne hk, List.mem_cons, hk, false_or]

/-- The keys whose cursor reaches the end in a pass over `ks`, each at its first time. -/
def refreshOut (valid : ℕ → ℕ → Bool) (len : ℕ → ℕ) (cur : ℕ → ℕ) : List ℕ → List ℕ
  | [] => []
  | k :: ks =>
    let cur' := Function.update cur k (advance (valid k) (len k) (cur k))
    (if cur k < len k ∧ cur' k = len k then [k] else []) ++ refreshOut valid len cur' ks

theorem mem_refreshOut (valid : ℕ → ℕ → Bool) (len : ℕ → ℕ) :
    ∀ (ks : List ℕ) (cur : ℕ → ℕ), (∀ k ∈ ks, cur k ≤ len k) → ∀ k,
      (k ∈ refreshOut valid len cur ks ↔
        k ∈ ks ∧ cur k < len k ∧ advance (valid k) (len k) (cur k) = len k)
  | [], _, _, k => by simp [refreshOut]
  | a :: ks, cur, hcur, k => by
    have hcur' : ∀ k ∈ ks,
        Function.update cur a (advance (valid a) (len a) (cur a)) k ≤ len k := by
      intro k hk'
      by_cases hk : k = a
      · subst hk; simp only [Function.update_self]
        exact advance_le _ (hcur k List.mem_cons_self)
      · rw [Function.update_of_ne hk]; exact hcur k (List.mem_cons_of_mem _ hk')
    have ih := mem_refreshOut valid len ks _ hcur' k
    simp only [refreshOut, List.mem_append, ih]
    by_cases hk : k = a
    · subst hk
      simp only [Function.update_self, List.mem_cons, true_or, true_and]
      constructor
      · rintro (h | ⟨_, h1, h2⟩)
        · split_ifs at h with hh
          · exact hh
          · simp at h
        · rw [advance_advance _ (hcur k List.mem_cons_self)] at h2
          omega
      · intro h
        left
        simp [h]
    · simp only [Function.update_of_ne hk, List.mem_cons, hk, false_or]
      constructor
      · rintro (h | h)
        · split_ifs at h <;> simp_all
        · exact h
      · exact Or.inr

theorem nodup_refreshOut (valid : ℕ → ℕ → Bool) (len : ℕ → ℕ) :
    ∀ (ks : List ℕ) (cur : ℕ → ℕ), (∀ k ∈ ks, cur k ≤ len k) →
      (refreshOut valid len cur ks).Nodup
  | [], _, _ => by simp [refreshOut]
  | a :: ks, cur, hcur => by
    have hcur' : ∀ k ∈ ks,
        Function.update cur a (advance (valid a) (len a) (cur a)) k ≤ len k := by
      intro k hk'
      by_cases hk : k = a
      · subst hk; simp only [Function.update_self]
        exact advance_le _ (hcur k List.mem_cons_self)
      · rw [Function.update_of_ne hk]; exact hcur k (List.mem_cons_of_mem _ hk')
    have ih := nodup_refreshOut valid len ks _ hcur'
    simp only [refreshOut]
    split_ifs with h
    · refine List.nodup_append.mpr ⟨List.nodup_singleton a, ih, ?_⟩
      intro u hu v hv
      rw [List.mem_singleton] at hu
      subst hu
      intro huv
      subst huv
      have h1 := ((mem_refreshOut valid len ks _ hcur' u).mp hv).2.1
      have h2 := h.2
      simp only [Function.update_self] at h1 h2
      omega
    · simpa using ih

namespace StaticArrays

variable (A : StaticArrays)

/-- The support cursors of `deleteState` come from a pass over any list with the same members as
`touchedVerts`. -/
theorem supCur_deleteState_eq {st : DelState} {e : ℕ} {ks : List ℕ}
    (hks : ∀ w, w ∈ ks ↔ w ∈ A.touchedVerts st e)
    (hcur : ∀ w ∈ ks, st.supCur w ≤ (A.C.supportArray w).length) :
    (A.deleteState st e).supCur = refreshAll (fun w => A.supValid (A.newSurv st e) w)
      (fun w => (A.C.supportArray w).length) st.supCur ks := by
  rw [refreshAll_eq _ _ ks _ hcur]
  funext w
  simp only [deleteState, hks]

/-- The pair cursors of `deleteState` come from a pass over any list with the same members as
`touchedPairs`. -/
theorem pairCur_deleteState_eq {st : DelState} {e : ℕ} {ks : List ℕ}
    (hks : ∀ q, q ∈ ks ↔ q ∈ A.touchedPairs st e)
    (hcur : ∀ q ∈ ks, st.pairCur q ≤ (A.pairConns q).length) :
    (A.deleteState st e).pairCur = refreshAll (fun q => A.pairValid (A.newSurv st e) q)
      (fun q => (A.pairConns q).length) st.pairCur ks := by
  rw [refreshAll_eq _ _ ks _ hcur]
  funext q
  simp only [deleteState, hks]

/-- The output of a pass over any list with the same members as `touchedVerts` has the members
of `deleteOut`. -/
theorem mem_refreshOut_iff_deleteOut {st : DelState} {e : ℕ} {ks : List ℕ}
    (hks : ∀ w, w ∈ ks ↔ w ∈ A.touchedVerts st e)
    (hcur : ∀ w ∈ ks, st.supCur w ≤ (A.C.supportArray w).length) (w : ℕ) :
    w ∈ refreshOut (fun w => A.supValid (A.newSurv st e) w)
        (fun w => (A.C.supportArray w).length) st.supCur ks ↔ w ∈ A.deleteOut st e := by
  rw [mem_refreshOut _ _ ks _ hcur, deleteOut, List.mem_filter, hks]
  by_cases hw : w ∈ A.touchedVerts st e
  · simp [hw, deleteState]
  · simp [hw]

end StaticArrays

end MinCostFlow.HierPaths

end
