module

public import MinCostFlow.SparseCore.Program.OutStepSpecSmall
public import MinCostFlow.DynSpanner.Program.DynGraphLayout

/-!
# What the tour answers mean for the edits, and the split records

The step program of P7 reads answers of the tour and lists of the helper, and writes records of
the batch and of the edits. This file proves, in the model only, that these answers are the ones
the edits `outStepEditsSmall` and the batch `U_S` ask for.

* `markedList_eq_filter`: when the marked ends of the core lists are the ends of the edges of `E`,
  the marked list of a vertex is its output list. So `firstMarked` gives the end that `rotateTo`
  needs.
* `nextMarked_eq_cycNextWith`: when the marked ends are the ends of the edges of `E` that meet a
  test `P`, `nextMarked` from an unmarked end `x` is the next end after `x` in the output list
  that meets `P`. So `nextMarked` gives the place of an insertion edit.
* `splitLists_spec` and `splitLists_sel`: the ends of a split list `Y` whose edge is still in the
  graph give the two edge lists of the split record (`UpdateAt`, tag `2` for the moved side and
  tag `3` for the kept side), and the set of ends of the edit of that side (`splitMovedSel` or
  `splitKeptSel`). The lists come with no repeats when `Y` has none (`nodup_endEdges`).
* `mem_splitSide_iff`: the ends of the edit of a side are the ends at the vertex of that side
  after the split, so the step can write the other side from the incidence list of its vertex.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

/-! ## The tour answers -/

theorem exists_first_split {xs : List End} {x : End} (hx : x ∈ xs) :
    ∃ A B, xs = A ++ x :: B ∧ x ∉ A := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    by_cases hy : y = x
    · exact ⟨[], ys, by rw [hy]; rfl, by simp⟩
    · have hx' : x ∈ ys := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h.symm hy
        · exact h
      obtain ⟨A, B, rfl, hA⟩ := ih hx'
      refine ⟨y :: A, B, rfl, ?_⟩
      simp only [List.mem_cons, not_or]
      exact ⟨fun h => hy h.symm, hA⟩

theorem afterEnd_split {A B : List End} {x : End} (hA : x ∉ A) :
    afterEnd x (A ++ x :: B) = B ++ A := by
  have htw : (A ++ x :: B).takeWhile (· != x) = A := by
    induction A with
    | nil => simp
    | cons a A ih =>
      simp only [List.mem_cons, not_or] at hA
      have ha : (a != x) = true := by simpa using fun h => hA.1 h.symm
      rw [List.cons_append, List.takeWhile_cons, ite_eq_left ha, ih hA.2]
  unfold afterEnd
  simp only [htw]
  rw [List.drop_append, List.drop_eq_nil_of_le (by simp), List.nil_append]
  simp

/-- The ends after `x` in a filtered list are the filtered ends after `x`, when `x` passes the
filter. -/
theorem afterEnd_filter {xs : List End} {x : End} (Q : End → Bool) (hx : x ∈ xs) (hQ : Q x) :
    afterEnd x (xs.filter Q) = (afterEnd x xs).filter Q := by
  obtain ⟨A, B, rfl, hA⟩ := exists_first_split hx
  have hA' : x ∉ A.filter Q := fun h => hA (List.mem_of_mem_filter h)
  rw [List.filter_append, List.filter_cons_of_pos hQ, afterEnd_split hA', afterEnd_split hA,
    List.filter_append]

theorem find?_filter' (l : List End) (Q P : End → Bool) :
    (l.filter Q).find? P = l.find? (fun z => Q z && P z) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases hQ : Q a
    · rw [List.filter_cons_of_pos hQ]
      by_cases hP : P a
      · rw [List.find?_cons_of_pos hP, List.find?_cons_of_pos (by simp [hQ, hP])]
      · rw [List.find?_cons_of_neg hP, List.find?_cons_of_neg (by simp [hP]), ih]
    · rw [List.filter_cons_of_neg hQ, List.find?_cons_of_neg (by simp [hQ]), ih]

theorem find?_congr_mem {l : List End} {P P' : End → Bool} (h : ∀ z ∈ l, P z = P' z) :
    l.find? P = l.find? P' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hl : ∀ z ∈ l, P z = P' z := fun z hz => h z (List.mem_cons_of_mem _ hz)
    by_cases hP : P a
    · rw [List.find?_cons_of_pos hP, List.find?_cons_of_pos (h a List.mem_cons_self ▸ hP)]
    · rw [List.find?_cons_of_neg hP,
        List.find?_cons_of_neg (by rw [← h a List.mem_cons_self]; exact hP), ih hl]

theorem mem_of_mem_afterEnd {x z : End} {xs : List End} (h : z ∈ afterEnd x xs) : z ∈ xs := by
  unfold afterEnd at h
  rcases List.mem_append.mp h with h | h
  · exact List.mem_of_mem_drop h
  · exact (List.takeWhile_sublist _).subset h

/-- **`nextMarked` gives the place of an insertion.** The tour holds the core lists `C`, and an end
of a core list is marked exactly when its edge is in `E` and it meets the test `P`. Then
`nextMarked` from an unmarked end `x` of the list at `v`, whose edge is in `E`, is the next end
after `x` in the output list (the core list restricted to `E`) that meets `P`. -/
theorem nextMarked_eq_cycNextWith (s : OutTourAbs) (E : Finset ℕ) (P : End → Bool) (v : ℕ)
    (hmk : ∀ z, (∃ u, z ∈ s.cord u) → (z ∈ s.marked ↔ z.1 ∈ E ∧ P z = true))
    {x : End} (hx : x ∈ s.cord v) (hxE : x.1 ∈ E) (hxm : x ∉ s.marked) :
    s.nextMarked v x = cycNextWith ((s.cord v).filter fun z => decide (z.1 ∈ E)) P x := by
  classical
  rw [OutTourAbs.nextMarked_of_not_mem s v hxm]
  unfold cycNextWith
  rw [afterEnd_filter _ hx (by simpa using hxE), find?_filter']
  apply find?_congr_mem
  intro z hz
  have hz' := mem_of_mem_afterEnd hz
  have := hmk z ⟨v, hz'⟩
  by_cases hm : z ∈ s.marked
  · simp only [hm, decide_true, true_iff] at this ⊢
    simp [this.1, this.2]
  · simp only [hm, decide_false, false_iff, not_and] at this ⊢
    by_cases hzE : z.1 ∈ E
    · simp [hzE, this hzE]
    · simp [hzE]

/-- **`firstMarked` gives the start of an output list.** When an end of a core list is marked
exactly when its edge is in `E`, the marked list of `v` is the core list restricted to `E`. -/
theorem markedList_eq_filter (s : OutTourAbs) (E : Finset ℕ) (v : ℕ)
    (hmk : ∀ z, (∃ u, z ∈ s.cord u) → (z ∈ s.marked ↔ z.1 ∈ E)) :
    s.markedList v = (s.cord v).filter fun z => decide (z.1 ∈ E) := by
  classical
  unfold OutTourAbs.markedList
  apply List.filter_congr
  intro z hz
  simp [hmk z ⟨v, hz⟩]

/-! ## The split records -/

/-- The edges of the ends of `Y` on side `b` (`true` for tails, `false` for heads) whose edge is
in `E`, in the order of `Y`. These are the two edge lists of a split record. -/
def endEdges (Y : List End) (E : Finset ℕ) (b : Bool) : List ℕ :=
  (Y.filter fun x => x.2 == b && decide (x.1 ∈ E)).map Prod.fst

theorem mem_endEdges {Y : List End} {E : Finset ℕ} {b : Bool} {e : ℕ} :
    e ∈ endEdges Y E b ↔ (e, b) ∈ Y ∧ e ∈ E := by
  unfold endEdges
  simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨e', b'⟩, ⟨hY, hb, hE⟩, rfl⟩
    simp only at hb hE
    subst hb
    exact ⟨hY, hE⟩
  · rintro ⟨hY, hE⟩
    exact ⟨(e, b), ⟨hY, rfl, hE⟩, rfl⟩

theorem nodup_endEdges {Y : List End} (hY : Y.Nodup) (E : Finset ℕ) (b : Bool) :
    (endEdges Y E b).Nodup := by
  unfold endEdges
  refine (hY.filter _).map_on ?_
  intro x hx y hy hxy
  simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hx hy
  exact Prod.ext hxy (hx.2.1.trans hy.2.1.symm)

/-- **The split lists give the split record.** Let `Y` be a list of ends without repeats such that
an end of an edge of `G` is in `Y` exactly when it lies at the vertex of side `side` after the
split (`v` for side `0`, `v'` for side `1`). Then the ends of `Y` whose edge is in `G` give the
edge lists of the record of the split: the moved tail and head edges for side `1` (tag `2`), and
the kept ones for side `0` (tag `3`). -/
theorem splitLists_spec {G : MGraph} {v v' : ℕ} {St Sh : Finset ℕ} (hG : G.IsValid)
    (hu : G.UpdateIsValid (.split v v' St Sh)) {Y : List End} (side : ℕ)
    (hside : ∀ x : End, x.1 ∈ G.E →
      (x ∈ Y ↔ (G.applyUpdate (.split v v' St Sh)).src x = if side = 0 then v else v')) :
    (side ≠ 0 → (∀ e, e ∈ endEdges Y G.E true ↔ e ∈ G.E ∧ G.tail e = v ∧ e ∈ St) ∧
        (∀ e, e ∈ endEdges Y G.E false ↔ e ∈ G.E ∧ G.head e = v ∧ e ∈ Sh)) ∧
      (side = 0 → (∀ e, e ∈ endEdges Y G.E true ↔ e ∈ G.E ∧ G.tail e = v ∧ e ∉ St) ∧
        (∀ e, e ∈ endEdges Y G.E false ↔ e ∈ G.E ∧ G.head e = v ∧ e ∉ Sh)) := by
  obtain ⟨hvV, hv'V, -, -⟩ := hu
  have hne : v ≠ v' := fun h => hv'V (h ▸ hvV)
  have htl : ∀ e ∈ G.E, G.tail e ≠ v' := fun e he h => hv'V (h ▸ (hG e he).1)
  have hhd : ∀ e ∈ G.E, G.head e ≠ v' := fun e he h => hv'V (h ▸ (hG e he).2)
  have key : ∀ (b : Bool) (e : ℕ), e ∈ endEdges Y G.E b ↔ e ∈ G.E ∧
      (G.applyUpdate (.split v v' St Sh)).src (e, b) = if side = 0 then v else v' := by
    intro b e
    rw [mem_endEdges]
    constructor
    · rintro ⟨hY, hE⟩; exact ⟨hE, (hside (e, b) hE).mp hY⟩
    · rintro ⟨hE, h⟩; exact ⟨(hside (e, b) hE).mpr h, hE⟩
  have hsrc : ∀ (b : Bool) (e : ℕ), (G.applyUpdate (.split v v' St Sh)).src (e, b) =
      if b then (if e ∈ St ∧ G.tail e = v then v' else G.tail e)
      else (if e ∈ Sh ∧ G.head e = v then v' else G.head e) := by
    intro b e; cases b <;> rfl
  -- the end moves to `v'` exactly when its edge is listed at `v`
  have hmv : ∀ (S : Finset ℕ) (f : ℕ → ℕ) (e : ℕ), f e ≠ v' →
      ((if e ∈ S ∧ f e = v then v' else f e) = v' ↔ f e = v ∧ e ∈ S) := by
    intro S f e hf
    by_cases hc : e ∈ S ∧ f e = v
    · rw [ite_eq_left hc]; exact ⟨fun _ => ⟨hc.2, hc.1⟩, fun _ => rfl⟩
    · rw [ite_eq_right hc]; exact ⟨fun h => absurd h hf, fun h => absurd ⟨h.2, h.1⟩ hc⟩
  have hkp : ∀ (S : Finset ℕ) (f : ℕ → ℕ) (e : ℕ),
      ((if e ∈ S ∧ f e = v then v' else f e) = v ↔ f e = v ∧ e ∉ S) := by
    intro S f e
    by_cases hc : e ∈ S ∧ f e = v
    · rw [ite_eq_left hc]; exact ⟨fun h => absurd h.symm hne, fun h => absurd hc.1 h.2⟩
    · rw [ite_eq_right hc]; exact ⟨fun h => ⟨h, fun hS => hc ⟨hS, h⟩⟩, fun h => h.1⟩
  refine ⟨fun hs => ⟨fun e => ?_, fun e => ?_⟩, fun hs => ⟨fun e => ?_, fun e => ?_⟩⟩
  · rw [key, hsrc, ite_eq_right hs]
    exact ⟨fun ⟨hE, h⟩ => ⟨hE, (hmv St G.tail e (htl e hE)).mp h⟩,
      fun ⟨hE, h⟩ => ⟨hE, (hmv St G.tail e (htl e hE)).mpr h⟩⟩
  · rw [key, hsrc, ite_eq_right hs]
    exact ⟨fun ⟨hE, h⟩ => ⟨hE, (hmv Sh G.head e (hhd e hE)).mp h⟩,
      fun ⟨hE, h⟩ => ⟨hE, (hmv Sh G.head e (hhd e hE)).mpr h⟩⟩
  · rw [key, hsrc, ite_eq_left hs]
    exact ⟨fun ⟨hE, h⟩ => ⟨hE, (hkp St G.tail e).mp h⟩,
      fun ⟨hE, h⟩ => ⟨hE, (hkp St G.tail e).mpr h⟩⟩
  · rw [key, hsrc, ite_eq_left hs]
    exact ⟨fun ⟨hE, h⟩ => ⟨hE, (hkp Sh G.head e).mp h⟩,
      fun ⟨hE, h⟩ => ⟨hE, (hkp Sh G.head e).mpr h⟩⟩

/-- **The split lists give the split edit.** Under the hypotheses of `splitLists_spec`, the ends
of `Y` whose edge is in `G` are the set of ends of the edit of that side: the moved ends
(`splitMovedSel`) for side `1` and the kept ends (`splitKeptSel`) for side `0`. -/
theorem splitLists_sel {G : MGraph} {v v' : ℕ} {St Sh : Finset ℕ} (hG : G.IsValid)
    (hu : G.UpdateIsValid (.split v v' St Sh)) {Y : List End} (side : ℕ)
    (hside : ∀ x : End, x.1 ∈ G.E →
      (x ∈ Y ↔ (G.applyUpdate (.split v v' St Sh)).src x = if side = 0 then v else v')) :
    (Y.filter fun x => decide (x.1 ∈ G.E)).toFinset =
      if side = 0 then splitKeptSel G v St Sh else splitMovedSel G v St Sh := by
  obtain ⟨h1, h0⟩ := splitLists_spec hG hu side hside
  ext ⟨e, b⟩
  have hmem : (e, b) ∈ (Y.filter fun x => decide (x.1 ∈ G.E)).toFinset ↔ e ∈ endEdges Y G.E b := by
    rw [mem_endEdges]; simp
  rw [hmem]
  by_cases hs : side = 0
  · rw [ite_eq_left hs]
    obtain ⟨ht, hh⟩ := h0 hs
    cases b
    · rw [hh]; simp [splitKeptSel, splitSel, and_assoc]
    · rw [ht]; simp [splitKeptSel, splitSel, and_assoc]
  · rw [ite_eq_right hs]
    obtain ⟨ht, hh⟩ := h1 hs
    cases b
    · rw [hh]; simp [splitMovedSel, splitSel, and_assoc]
    · rw [ht]; simp [splitMovedSel, splitSel, and_assoc]

/-- The ends of the edit of a side are the ends at the vertex of that side after the split. So the
step can also write the edit of a side from the incidence list of its vertex. -/
theorem mem_splitSide_iff {G : MGraph} {v v' : ℕ} {St Sh : Finset ℕ} (hG : G.IsValid)
    (hu : G.UpdateIsValid (.split v v' St Sh)) (side : ℕ) (x : End) :
    x ∈ (if side = 0 then splitKeptSel G v St Sh else splitMovedSel G v St Sh) ↔
      x.1 ∈ G.E ∧ (G.applyUpdate (.split v v' St Sh)).src x = if side = 0 then v else v' := by
  classical
  set tgt := if side = 0 then v else v'
  set Y : List End := (G.E.toList.flatMap fun e => [(e, true), (e, false)]).filter
    fun z => decide ((G.applyUpdate (.split v v' St Sh)).src z = tgt) with hYdef
  have hY : ∀ z : End, z ∈ Y ↔ z.1 ∈ G.E ∧ (G.applyUpdate (.split v v' St Sh)).src z = tgt := by
    intro z
    obtain ⟨e, b⟩ := z
    simp only [hYdef, List.mem_filter, List.mem_flatMap, Finset.mem_toList, List.mem_cons,
      List.not_mem_nil, or_false, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨f, hf, h⟩, hs⟩
      rcases h with h | h <;> (rw [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ⟨hf, hs⟩)
    · rintro ⟨he, hs⟩
      exact ⟨⟨e, he, by cases b <;> simp⟩, hs⟩
  have hsel := splitLists_sel hG hu (Y := Y) side (fun z hz => by
    rw [hY]; exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩)
  rw [← hsel, List.mem_toFinset, List.mem_filter, hY, decide_eq_true_eq]
  exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩

end MinCostFlow.SparseCore.Program
