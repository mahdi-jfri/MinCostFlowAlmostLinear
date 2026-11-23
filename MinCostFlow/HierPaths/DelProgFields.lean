module

public import MinCostFlow.HierPaths.DelProgMark

/-!
# Each change of the dynamic state is one write

The `Delete` program changes the dynamic state one field entry at a time: it sets a failed bit,
a lost bit, an ineligible bit or a bit of `Vhat`, it sets a loss counter, and it moves a cursor.
This file shows that each such change of the concrete state changes exactly one word of one
section of the block, so the program can make it with one store (`triple_writeSec`). The concrete
state is changed with `HierConcrete.withSt` (a new dynamic state) and `HierConcrete.withVhat` (a
new set `Vhat`). The lemmas are:

* `sections_setFailed`, `sections_setGlob`, `sections_setInelig`, `sections_setVhat`: one bit;
* `sections_setOwn`, `sections_setSum`: one loss counter, inside a `csrList` section;
* `sections_setSupCur`, `sections_setPairCur`: one cursor.

The lemmas `csrList_getElem_offset` and `csrList_getElem_data` read the offsets and the elements
of a `csrList` section, which the program needs for the lists `revList`, `termConns` and
`pairConns`, the support arrays, the walks and the counters.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner MinCostFlow.Cited

private theorem listAt_self (l : List ℕ) : ListAt (fun a => l[a]?.getD 0) 0 l := by
  intro i hi
  simp [hi]

/-- Offset word `j` of a `csrList`. -/
theorem csrList_getElem_offset {n : ℕ} (f : ℕ → List ℕ) {j : ℕ} (hj : j ≤ n)
    (h : j < (csrList n f).length) :
    (csrList n f)[j] = ((List.range j).map fun i => (f i).length).sum := by
  have := csrList_offset (listAt_self (csrList n f)) hj
  rw [Nat.zero_add, List.getElem?_eq_getElem h, Option.getD_some] at this
  exact this

/-- Element `k` of list `j` of a `csrList`. -/
theorem csrList_getElem_data {n : ℕ} (f : ℕ → List ℕ) {j : ℕ} (hj : j < n) {k : ℕ}
    (hk : k < (f j).length)
    (h : n + 1 + ((List.range j).map fun i => (f i).length).sum + k < (csrList n f).length) :
    (csrList n f)[n + 1 + ((List.range j).map fun i => (f i).length).sum + k] = (f j)[k] := by
  have := listAt_csrList_get (listAt_self (csrList n f)) hj k hk
  rw [Nat.zero_add, List.getElem?_eq_getElem h, Option.getD_some] at this
  exact this

namespace HierConcrete

/-- The concrete state with a new dynamic state. -/
def withSt (x : HierConcrete) (st : DelState) : HierConcrete := ⟨x.H, ⟨st, x.ms.abs⟩⟩

/-- The concrete state with a new set `Vhat`. -/
def withVhat (x : HierConcrete) (V : Finset ℕ) : HierConcrete :=
  ⟨x.H, ⟨x.ms.st, { x.ms.abs with Vhat := V }⟩⟩

private theorem bits_insert (n : ℕ) (S : Finset ℕ) (t : ℕ) :
    (bitsList n fun i => decide (i ∈ S)).set t 1 = bitsList n fun i => decide (i ∈ insert t S) := by
  have := bitsList_set n (fun i => decide (i ∈ S)) t true
  simp only [ite_true] at this
  rw [this]
  congr 1
  funext i
  by_cases h : i = t
  · subst h; simp
  · simp [Finset.mem_insert, h]

variable (x : HierConcrete)

theorem sections_setFailed (t : ℕ) :
    (x.withSt { x.ms.st with loss := { x.ms.st.loss with
        failed := insert t x.ms.st.loss.failed } }).sections =
      x.sections.set 13 ((x.sections.getD 13 []).set t 1) := by
  have := bits_insert x.H.A.C.numTerm x.ms.st.loss.failed t
  simp only [sections, header, withSt, n, m, depth, pairIdxTable] at this ⊢
  simp [List.set, this]
  all_goals (and_intros <;> rfl)

theorem sections_setGlob (t : ℕ) :
    (x.withSt { x.ms.st with loss := { x.ms.st.loss with
        glob := insert t x.ms.st.loss.glob } }).sections =
      x.sections.set 14 ((x.sections.getD 14 []).set t 1) := by
  have := bits_insert x.H.A.C.numTerm x.ms.st.loss.glob t
  simp only [sections, header, withSt, n, m, depth, pairIdxTable] at this ⊢
  simp [List.set, this]
  all_goals (and_intros <;> rfl)

theorem sections_setInelig (c : ℕ) :
    (x.withSt { x.ms.st with inelig := insert c x.ms.st.inelig }).sections =
      x.sections.set 15 ((x.sections.getD 15 []).set c 1) := by
  have := bits_insert x.H.A.C.numConn x.ms.st.inelig c
  simp only [sections, header, withSt, n, m, depth, pairIdxTable] at this ⊢
  simp [List.set, this]
  all_goals (and_intros <;> rfl)

theorem sections_setVhat (v : ℕ) :
    (x.withVhat (insert v x.ms.abs.Vhat)).sections =
      x.sections.set 17 ((x.sections.getD 17 []).set v 1) := by
  have := bits_insert x.n x.ms.abs.Vhat v
  simp only [sections, header, withVhat, n, m, depth, pairIdxTable] at this ⊢
  simp [List.set, this]
  all_goals (and_intros <;> rfl)

theorem sections_setSupCur (w v : ℕ) :
    (x.withSt { x.ms.st with supCur := Function.update x.ms.st.supCur w v }).sections =
      x.sections.set 20 ((x.sections.getD 20 []).set w v) := by
  have := tabList_set x.n x.ms.st.supCur w v
  simp only [sections, header, withSt, n, m, depth, pairIdxTable] at this ⊢
  simp [List.set, this]
  all_goals (and_intros <;> rfl)

theorem sections_setPairCur (q v : ℕ) :
    (x.withSt { x.ms.st with pairCur := Function.update x.ms.st.pairCur q v }).sections =
      x.sections.set 21 ((x.sections.getD 21 []).set q v) := by
  have := tabList_set x.H.A.numPairs x.ms.st.pairCur q v
  simp only [sections, header, withSt, n, m, depth, pairIdxTable] at this ⊢
  simp [List.set, this]
  all_goals (and_intros <;> rfl)

/-- The word of section `18` or `19` that holds the counter of group `g` at depth `j`. -/
def ctrIdx (j g : ℕ) : ℕ :=
  x.depth + 1 + 1 +
    ((List.range j).map fun i => (tabList (numGroups x.H.A.x x.H.A.b i) fun _ => 0).length).sum + g

private theorem csr_setAt (L : ℕ) (N : ℕ → ℕ) (f : ℕ → ℕ → ℕ) {j g : ℕ} (hj : j < L)
    (hg : g < N j) (v : ℕ) :
    (csrList L fun i => tabList (N i) (setAt f j g v i)) =
      (csrList L fun i => tabList (N i) (f i)).set
        (L + 1 + ((List.range j).map fun i => (tabList (N i) fun _ => 0).length).sum + g) v := by
  have hfun : (fun i => tabList (N i) (setAt f j g v i)) =
      Function.update (fun i => tabList (N i) (f i)) j ((tabList (N j) (f j)).set g v) := by
    funext i
    by_cases hi : i = j
    · subst hi
      rw [Function.update_self, tabList_set]
      congr 1
      funext c
      by_cases hc : c = g
      · subst hc; simp [setAt]
      · simp [setAt, hc, Function.update_of_ne hc]
    · rw [Function.update_of_ne hi]
      congr 1
      funext c
      simp [setAt, hi]
  rw [hfun, csrList_set _ hj (by simpa using hg)]
  simp

theorem sections_setOwn {j g : ℕ} (hj : j ≤ x.depth) (hg : g < numGroups x.H.A.x x.H.A.b j)
    (v : ℕ) :
    (x.withSt { x.ms.st with loss := { x.ms.st.loss with
        own := setAt x.ms.st.loss.own j g v } }).sections =
      x.sections.set 18 ((x.sections.getD 18 []).set (x.ctrIdx j g) v) := by
  have := csr_setAt (x.depth + 1) (numGroups x.H.A.x x.H.A.b) x.ms.st.loss.own
    (by omega : j < x.depth + 1) hg v
  simp only [sections, header, withSt, n, m, depth, pairIdxTable, ctrIdx] at this ⊢
  simp [List.set, this]
  all_goals (and_intros <;> rfl)

theorem sections_setSum {j g : ℕ} (hj : j ≤ x.depth) (hg : g < numGroups x.H.A.x x.H.A.b j)
    (v : ℕ) :
    (x.withSt { x.ms.st with loss := { x.ms.st.loss with
        sum := setAt x.ms.st.loss.sum j g v } }).sections =
      x.sections.set 19 ((x.sections.getD 19 []).set (x.ctrIdx j g) v) := by
  have := csr_setAt (x.depth + 1) (numGroups x.H.A.x x.H.A.b) x.ms.st.loss.sum
    (by omega : j < x.depth + 1) hg v
  simp only [sections, header, withSt, n, m, depth, pairIdxTable, ctrIdx] at this ⊢
  simp [List.set, this]
  all_goals (and_intros <;> rfl)

end HierConcrete

end MinCostFlow.HierPaths

end
