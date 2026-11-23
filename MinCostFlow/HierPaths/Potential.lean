module

public import MinCostFlow.HierPaths.DeleteStep

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The event count and the cost of one `Delete`

The amortized bound of `Delete` charges the work to monotone events that the
state records. Here the event count `events` of a state is a function of the state:

* the counter updates and the enumerated terminals of the loss counters;
* the directly failed terminals;
* for each globally lost terminal, two plus the number of its connectors;
* for each ineligible connector, two plus the number of vertices of its walk;
* the positions of all support cursors and pair cursors.

`events_deleteState`: one `Delete(e)` raises the count by exactly the sum of the growths of these
parts, and `deleteCost_le`: the cost of `Delete(e)` is at most `2 · (1 + ξ + E' − E)`, with `E` and
`E'` the counts before and after and `ξ` the bound on the reverse lists.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

namespace StaticArrays

variable (A : StaticArrays)

/-- The weight of a lost terminal: two plus the number of its connectors. -/
def termWeight (t : ℕ) : ℕ := 2 + (A.termConns t).length

/-- The weight of an ineligible connector: two plus the number of vertices of its walk. -/
def connWeight (c : ℕ) : ℕ := 2 + (A.C.walk c).verts.length

/-- The event count of a state, for an input graph on `n` vertices. -/
def events (n : ℕ) (st : DelState) : ℕ :=
  st.loss.updates + st.loss.enumerated + st.loss.failed.card +
    ∑ t ∈ st.loss.glob, A.termWeight t + ∑ c ∈ st.inelig, A.connWeight c +
    ∑ w ∈ Finset.range n, st.supCur w + ∑ p ∈ Finset.range A.numPairs, st.pairCur p

end StaticArrays

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

namespace StaticArrays

variable (A : StaticArrays) {G : Graph} {ξ κ : ℕ}

/-- A sum over the range of the new cursor positions is the old sum plus the moves of the
touched cursors. -/
private theorem sum_cursor_eq {N : ℕ} {old new : ℕ → ℕ} {T : List ℕ} (hT : T.Nodup)
    (hTN : ∀ w ∈ T, w < N) (hge : ∀ w, old w ≤ new w) (hout : ∀ w, w ∉ T → new w = old w) :
    ∑ w ∈ Finset.range N, new w =
      ∑ w ∈ Finset.range N, old w + (T.map fun w => new w - old w).sum := by
  have h1 : ∑ w ∈ Finset.range N, new w =
      ∑ w ∈ Finset.range N, (old w + (new w - old w)) :=
    Finset.sum_congr rfl fun w _ => by have := hge w; omega
  rw [h1, Finset.sum_add_distrib]
  congr 1
  rw [← List.sum_toFinset _ hT]
  refine (Finset.sum_subset (fun w hw => Finset.mem_range.mpr (hTN w (List.mem_toFinset.mp hw)))
    fun w _ hw => ?_).symm
  rw [hout w (fun h => hw (List.mem_toFinset.mpr h))]
  simp

private theorem length_touchedVerts_le (st : DelState) (e : ℕ) :
    (A.touchedVerts st e).length ≤
      ((A.newLost st e).map A.termWeight).sum + ((A.newInelig st e).map A.connWeight).sum := by
  refine (List.dedup_sublist _).length_le.trans ?_
  rw [List.length_append, List.length_map, List.length_flatMap]
  have h1 : (A.newLost st e).length ≤ ((A.newLost st e).map A.termWeight).sum := by
    induction (A.newLost st e) with
    | nil => simp
    | cons t l ih => simp only [List.length_cons, List.map_cons, List.sum_cons, termWeight]; omega
  have h2 : ((A.newInelig st e).map fun c => (A.C.walk c).verts.length).sum ≤
      ((A.newInelig st e).map A.connWeight).sum := by
    induction (A.newInelig st e) with
    | nil => simp
    | cons c l ih => simp only [List.map_cons, List.sum_cons, connWeight]; omega
  omega

public section

/-- One `Delete(e)` raises the event count by exactly the growth of its parts. -/
theorem events_deleteState {st : DelState} (hA : A.Spec G ξ κ) (hG : G.IsValid)
    (hinv : A.DelInv G st) (e : ℕ) :
    A.events G.n (A.deleteState st e) = A.events G.n st +
      (((A.newLoss st e).updates - st.loss.updates) +
        ((A.newLoss st e).enumerated - st.loss.enumerated) +
        ((A.newLoss st e).failed.card - st.loss.failed.card) +
        ((A.newLost st e).map A.termWeight).sum + ((A.newInelig st e).map A.connWeight).sum +
        ((A.touchedVerts st e).map fun w => (A.deleteState st e).supCur w - st.supCur w).sum +
        ((A.touchedPairs st e).map fun p =>
          (A.deleteState st e).pairCur p - st.pairCur p).sum) := by
  obtain ⟨hL, hnd, heq, hU, hE⟩ := A.newLoss_spec hA hinv e
  have hF : st.loss.failed.card ≤ (A.newLoss st e).failed.card := by
    rw [hL.failed, hinv.loss.failed]
    exact Finset.card_le_card Finset.subset_union_left
  have hglob : st.loss.glob ⊆ (A.newLoss st e).glob := by
    rw [hL.glob, hinv.loss.glob]; exact globalLost_mono Finset.subset_union_left
  have hT : ∑ t ∈ (A.newLoss st e).glob, A.termWeight t =
      ∑ t ∈ st.loss.glob, A.termWeight t + ((A.newLost st e).map A.termWeight).sum := by
    rw [← List.sum_toFinset _ hnd, heq, add_comm, Finset.sum_sdiff hglob]
  have hdisj : Disjoint st.inelig (A.newInelig st e).toFinset := by
    rw [Finset.disjoint_left]
    intro c hc hc'
    rw [List.mem_toFinset, newInelig, List.mem_dedup, List.mem_filter] at hc'
    simpa [hc] using hc'.2
  have hI : ∑ c ∈ st.inelig ∪ (A.newInelig st e).toFinset, A.connWeight c =
      ∑ c ∈ st.inelig, A.connWeight c + ((A.newInelig st e).map A.connWeight).sum := by
    have hn : (A.newInelig st e).Nodup := List.nodup_dedup _
    rw [Finset.sum_union hdisj, List.sum_toFinset A.connWeight hn]
  have hS := sum_cursor_eq (N := G.n) (old := st.supCur) (new := (A.deleteState st e).supCur)
    (T := A.touchedVerts st e) (List.nodup_dedup _)
    (fun w hw => A.lt_of_mem_touchedVerts hA hG hinv e hw)
    (fun w => by
      show st.supCur w ≤ if w ∈ A.touchedVerts st e then _ else _
      split_ifs
      · exact le_advance _ _ _
      · exact le_rfl)
    (fun w hw => by simp only [deleteState, hw, ↓reduceIte])
  have hP := sum_cursor_eq (N := A.numPairs) (old := st.pairCur)
    (new := (A.deleteState st e).pairCur) (T := A.touchedPairs st e) (List.nodup_dedup _)
    (fun p hp => by
      rw [touchedPairs, List.mem_dedup, List.mem_map] at hp
      obtain ⟨c, hc, rfl⟩ := hp
      exact hA.pairOf_lt c ((A.mem_newInelig_iff hA hinv e c).mp hc).1.1)
    (fun p => by
      show st.pairCur p ≤ if p ∈ A.touchedPairs st e then _ else _
      split_ifs
      · exact le_advance _ _ _
      · exact le_rfl)
    (fun p hp => by simp only [deleteState, hp, ↓reduceIte])
  unfold events
  have hglob' : (A.deleteState st e).loss.glob = (A.newLoss st e).glob := rfl
  have hinel' : (A.deleteState st e).inelig = st.inelig ∪ (A.newInelig st e).toFinset := rfl
  have hloss' : (A.deleteState st e).loss = A.newLoss st e := rfl
  rw [hglob', hinel', hT, hI, hS, hP, hloss']
  omega

/-- The cost of `Delete(e)` is at most `2 · (1 + ξ + E' − E)`, where `E` and `E'` are the event
counts before and after. Also `E ≤ E'`. -/
theorem deleteCost_le {st : DelState} (hA : A.Spec G ξ κ) (hG : G.IsValid)
    (hinv : A.DelInv G st) (e : ℕ) :
    A.events G.n st ≤ A.events G.n (A.deleteState st e) ∧
      A.deleteCost st e ≤
        2 * (1 + ξ + (A.events G.n (A.deleteState st e) - A.events G.n st)) := by
  have hE := A.events_deleteState hA hG hinv e
  have ht := A.length_touchedVerts_le st e
  have hr := hA.rev_length e
  refine ⟨by omega, ?_⟩
  rw [hE, Nat.add_sub_cancel_left]
  unfold deleteCost
  have hw : ((A.newLost st e).map fun t => 2 + (A.termConns t).length).sum =
      ((A.newLost st e).map A.termWeight).sum := rfl
  have hc : ((A.newInelig st e).map fun c => 2 + (A.C.walk c).verts.length).sum =
      ((A.newInelig st e).map A.connWeight).sum := rfl
  rw [hw, hc]
  omega

end

end StaticArrays

end MinCostFlow.HierPaths
