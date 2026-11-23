module

public import MinCostFlow.HierPaths.BuildChildSpec
import Mathlib.Data.List.GetD

/-!
# The batched game of `lemma_3`: what one call gives each child

One router call serves the requests of several children `cs` at once. Request `i` belongs to
child `cs[i]`, and its two sides lie in the child's terminals `Y (cs[i])`. The children's
terminals are disjoint. So the first end of a matched edge tells which child it belongs to, and
the entries that child `cs[i]` takes (`takeEntries`) are exactly the edges of matching `i` with
their walks, shifted back to local numbers (`take_call`).
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

theorem mem_shiftSet_iff {o x : ℕ} {A : Finset ℕ} : x ∈ shiftSet o A ↔ o ≤ x ∧ x - o ∈ A := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    simpa using ha
  · rintro ⟨h1, h2⟩
    have : o + (x - o) = x := by omega
    rw [← this]
    exact mem_shiftSet.mpr h2

/-- The edges of the entries of a call are the matched edges. -/
theorem map_fst_callEntries (E : List (ℕ × ℕ)) (Ms : List (List (ℕ × ℕ))) (emb : ℕ → List ℕ) :
    (callEntries E (.matched Ms emb)).map Prod.fst = Ms.flatten := by
  unfold callEntries rawEntries
  simp only [List.map_map]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_range, Function.comp, edgeAt]
  exact List.getD_eq_getElem _ _ h2

theorem mem_callEntries {E : List (ℕ × ℕ)} {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    {en : (ℕ × ℕ) × List ℕ} (h : en ∈ callEntries E (.matched Ms emb)) :
    ∃ j < Ms.flatten.length,
      en = (edgeAt Ms.flatten j, erase E (edgeAt Ms.flatten j).1 (emb j)) := by
  unfold callEntries rawEntries at h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
  exact ⟨j, List.mem_range.mp hj, rfl⟩

/-- **What one call gives a child.** The children `cs` are distinct, their terminal sets `Y c` are
disjoint and inside `X`, and both sides of request `i` lie in `Y (cs[i])`. If the call returns
matchings `Ms` (one per request, each inside its request) with an embedding of walks of at most
`d` edges, and `Y (cs[i])` is the interval of `s` terminals from `o`, then child `cs[i]` takes
matching `i` shifted back, and each entry it takes is good. -/
theorem take_call {G : Graph} {X : Finset ℕ} {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    {cs : List ℕ} {Y : ℕ → Finset ℕ} {p : ℕ → Finset ℕ × Finset ℕ} {d : ℕ}
    (hnd : cs.Nodup) (hY : ∀ c ∈ cs, Y c ⊆ X)
    (hdisj : ∀ c ∈ cs, ∀ c' ∈ cs, c ≠ c' → Disjoint (Y c) (Y c'))
    (hp : ∀ c ∈ cs, (p c).1 ⊆ Y c ∧ (p c).2 ⊆ Y c) (hlenM : Ms.length = cs.length)
    (hends : ∀ i (hi : i < cs.length), ∀ e ∈ Ms.getD i [], e.1 ∈ (p cs[i]).1 ∧ e.2 ∈ (p cs[i]).2)
    (hemb : IsEmbeddingOn (Graph.mk G.n Ms.flatten) G X emb)
    (hd : ∀ j < Ms.flatten.length, (emb j).length ≤ d)
    {i : ℕ} (hi : i < cs.length) {s o : ℕ} (hYo : Y cs[i] = shiftSet o (Finset.range s)) :
    (takeEntries s o (callEntries G.edges (.matched Ms emb))).map Prod.fst =
        unshiftEdges o (Ms.getD i []) ∧
      ∀ en ∈ takeEntries s o (callEntries G.edges (.matched Ms emb)), EntryOK G X o d en := by
  have hiM : i < Ms.length := hlenM ▸ hi
  have hgetD : ∀ i' (h : i' < Ms.length), Ms.getD i' [] = Ms[i'] :=
    fun i' h => List.getD_eq_getElem _ _ h
  -- The edges whose first end lies in child `cs[i]` are the edges of matching `i`.
  have hfl : Ms.flatten.filter (fun e => decide (e.1 ∈ shiftSet o (Finset.range s))) = Ms[i] := by
    apply filter_flatten_single hiM
    intro i' hi' x hx
    have hi'c : i' < cs.length := hlenM ▸ hi'
    have hx1 : x.1 ∈ Y cs[i'] :=
      (hp _ (List.getElem_mem hi'c)).1 (hends i' hi'c x (by rw [hgetD i' hi']; exact hx)).1
    rw [decide_eq_true_iff, ← hYo]
    constructor
    · intro hxi
      by_contra hne
      have hcne : cs[i'] ≠ cs[i] := fun h => hne ((hnd.getElem_inj_iff).mp h)
      exact Finset.disjoint_left.mp
        (hdisj _ (List.getElem_mem hi'c) _ (List.getElem_mem hi) hcne) hx1 hxi
    · rintro rfl
      exact hx1
  set P : (ℕ × ℕ) × List ℕ → Bool := fun en => decide (en.1.1 ∈ shiftSet o (Finset.range s))
  have hfst : ((callEntries G.edges (.matched Ms emb)).filter P).map Prod.fst = Ms[i] := by
    rw [← hfl, ← map_fst_callEntries G.edges Ms emb, List.filter_map]
    rfl
  have htake : takeEntries s o (callEntries G.edges (.matched Ms emb)) =
      ((callEntries G.edges (.matched Ms emb)).filter P).map
        fun en => ((en.1.1 - o, en.1.2 - o), en.2) := rfl
  refine ⟨?_, ?_⟩
  · rw [htake, hgetD i hiM, ← hfst]
    unfold unshiftEdges
    simp only [List.map_map]
    rfl
  · intro en hen
    rw [htake] at hen
    obtain ⟨en0, hen0, rfl⟩ := List.mem_map.mp hen
    have he0 : en0.1 ∈ Ms[i] := by
      rw [← hfst]
      exact List.mem_map_of_mem hen0
    obtain ⟨h1, h2⟩ := hends i hi en0.1 (by rw [hgetD i hiM]; exact he0)
    obtain ⟨hp1, hp2⟩ := hp _ (List.getElem_mem hi)
    have hY1 := hp1 h1
    have hY2 := hp2 h2
    have hX1 := hY _ (List.getElem_mem hi) hY1
    have hX2 := hY _ (List.getElem_mem hi) hY2
    rw [hYo] at hY1 hY2
    have ho1 := (mem_shiftSet_iff.mp hY1).1
    have ho2 := (mem_shiftSet_iff.mp hY2).1
    obtain ⟨j, hj, hen0eq⟩ := mem_callEntries (List.mem_of_mem_filter hen0)
    rw [hen0eq] at hX1 hX2 ho1 ho2 ⊢
    simp only at hX1 hX2 ho1 ho2 ⊢
    have hin : insideB X (edgeAt (Graph.mk G.n Ms.flatten).edges j) = true := by
      simp only [insideB, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hX1, hX2⟩
    obtain ⟨hwalk0, hins0⟩ := hemb j hj hin
    obtain ⟨hwalk, hsub, _, _⟩ := erase_spec _ _ _ _ le_rfl hwalk0
    have hins : ∀ i' ∈ erase G.edges (edgeAt Ms.flatten j).1 (emb j),
        insideB X (edgeAt G.edges i') = true := fun i' hi' => hins0 i' (hsub.subset hi')
    have e1 : o + ((edgeAt Ms.flatten j).1 - o) = (edgeAt Ms.flatten j).1 := by omega
    have e2 : o + ((edgeAt Ms.flatten j).2 - o) = (edgeAt Ms.flatten j).2 := by omega
    refine ⟨?_, hins, hsub.length_le.trans (hd j hj)⟩
    rw [e1, e2]
    exact hwalk

end MinCostFlow.HierPaths
