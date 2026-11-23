module

public import MinCostFlow.HierPaths.Live
public import MinCostFlow.HierPaths.Cursor

/-!
# Support arrays

A query starts at a live vertex `w`, which need not own a surviving terminal. It must first reach
the owner of a surviving terminal. For this the data structure keeps, for each vertex `w`, a
*support array*: one entry for each terminal owned by `w`, and one entry for
each occurrence of `w` on a connector walk, with the connector and the position. A terminal entry
is live while its terminal survives, and a walk entry while its connector is eligible. A cursor
points to the first live entry.

This file proves:

* `exists_live_entry_iff`: a vertex is live exactly when its support array has a live entry;
* `supportCursor_eq_iff`: the cursor of the support array of `w` reaches the end exactly when `w`
  is pruned, for any history in which terminals are only lost;
* `supportWalk_spec`: a live entry gives a walk from `w` to the owner of a surviving terminal that
  uses no deleted edge, only live vertices, and at most as many edges as the connector walk.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

/-- An entry of a support array: a terminal, or a position on the walk of a connector. -/
inductive SupportEntry where
  /-- The terminal `t`. -/
  | term (t : ℕ)
  /-- Position `pos` on the walk of connector `c`. -/
  | onWalk (c pos : ℕ)
  deriving DecidableEq, Inhabited

namespace ConnectorSystem

variable (C : ConnectorSystem)

/-- The positions of the vertex `w` on the walk of connector `c`. -/
def positionsOn (w c : ℕ) : List ℕ :=
  (List.range (C.walk c).verts.length).filter fun pos => (C.walk c).verts.getD pos 0 = w

/-- The support array of the vertex `w`: its terminals, then its occurrences on connector
walks. -/
def supportArray (w : ℕ) : List SupportEntry :=
  ((List.range C.numTerm).filter fun t => C.owner t = w).map SupportEntry.term ++
    (List.range C.numConn).flatMap fun c => (C.positionsOn w c).map (SupportEntry.onWalk c)

/-- A support entry is live when its terminal survives or its connector is eligible. -/
def entryLive (surv : Finset ℕ) : SupportEntry → Bool
  | .term t => decide (t ∈ surv)
  | .onWalk c _ => decide (C.Eligible surv c)

/-- The surviving terminal that a support entry reaches: the terminal itself, or the first
endpoint of the connector. -/
def entryTerm : SupportEntry → ℕ
  | .term t => t
  | .onWalk c _ => C.endA c

/-- The walk that a support entry gives: the empty walk for a terminal entry, and the reversed
prefix of the connector walk up to the position for a walk entry. -/
def supportWalk : SupportEntry → Walk
  | .term _ => Walk.empty
  | .onWalk c pos => (Walk.prefix (C.walk c) pos).reverse

/-- The cursor of the support array of `w` after time `t`, for surviving sets `surv t`. -/
def supportCursor (surv : ℕ → Finset ℕ) (w t : ℕ) : ℕ :=
  cursorAt (fun t i => C.entryLive (surv t) ((C.supportArray w).getD i default))
    (C.supportArray w).length t

end ConnectorSystem

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

namespace ConnectorSystem

variable (C : ConnectorSystem)

public section

theorem mem_positionsOn {w c pos : ℕ} :
    pos ∈ C.positionsOn w c ↔ pos < (C.walk c).verts.length ∧ (C.walk c).verts.getD pos 0 = w := by
  simp [positionsOn]

theorem mem_supportArray {w : ℕ} {x : SupportEntry} :
    x ∈ C.supportArray w ↔
      (∃ t < C.numTerm, C.owner t = w ∧ x = .term t) ∨
        ∃ c < C.numConn, ∃ pos ∈ C.positionsOn w c, x = .onWalk c pos := by
  simp only [supportArray, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
    List.mem_flatMap, decide_eq_true_eq]
  constructor
  · rintro (⟨t, ⟨ht, ho⟩, rfl⟩ | ⟨c, hc, pos, hpos, rfl⟩)
    · exact Or.inl ⟨t, ht, ho, rfl⟩
    · exact Or.inr ⟨c, hc, pos, hpos, rfl⟩
  · rintro (⟨t, ht, ho, rfl⟩ | ⟨c, hc, pos, hpos, rfl⟩)
    · exact Or.inl ⟨t, ⟨ht, ho⟩, rfl⟩
    · exact Or.inr ⟨c, hc, pos, hpos, rfl⟩

/-- A vertex of `G` is live exactly when its support array has a live entry. -/
theorem exists_live_entry_iff {G : Graph} {surv : Finset ℕ}
    (hsurv : surv ⊆ Finset.range C.numTerm) {w : ℕ} (hw : w < G.n) :
    (∃ x ∈ C.supportArray w, C.entryLive surv x = true) ↔ w ∈ C.liveSet G surv := by
  rw [mem_liveSet]
  constructor
  · rintro ⟨x, hx, hl⟩
    rcases (C.mem_supportArray).mp hx with ⟨t, _, ho, rfl⟩ | ⟨c, _, pos, hpos, rfl⟩
    · exact ⟨hw, Or.inl ⟨t, by simpa [entryLive] using hl, ho⟩⟩
    · obtain ⟨hlt, hget⟩ := (C.mem_positionsOn).mp hpos
      refine ⟨hw, Or.inr ⟨c, by simpa [entryLive] using hl, ?_⟩⟩
      rw [← hget, List.getD_eq_getElem _ _ hlt]
      exact List.getElem_mem hlt
  · rintro ⟨_, ⟨t, ht, ho⟩ | ⟨c, hc, hwc⟩⟩
    · refine ⟨.term t, (C.mem_supportArray).mpr
        (Or.inl ⟨t, Finset.mem_range.mp (hsurv ht), ho, rfl⟩), by simpa [entryLive] using ht⟩
    · obtain ⟨pos, hpos, rfl⟩ := List.getElem_of_mem hwc
      refine ⟨.onWalk c pos, (C.mem_supportArray).mpr (Or.inr ⟨c, hc.1, pos, ?_, rfl⟩),
        by simpa [entryLive] using hc⟩
      exact (C.mem_positionsOn).mpr ⟨hpos, List.getD_eq_getElem _ _ hpos⟩

/-- Live entries stay live only while their terminal or connector does. -/
theorem entryLive_mono {surv surv' : Finset ℕ} (h : surv' ⊆ surv) {x : SupportEntry}
    (hx : C.entryLive surv' x = true) : C.entryLive surv x = true := by
  cases x with
  | term t => simpa [entryLive] using h (by simpa [entryLive] using hx)
  | onWalk c pos =>
    simpa [entryLive] using (show C.Eligible surv' c by simpa [entryLive] using hx).mono C h

/-- The cursor of the support array of a vertex `w` of `G` reaches the end of the array exactly
when `w` is pruned, for any history in which terminals are only lost. This is how a deletion
detects the newly pruned vertices. -/
theorem supportCursor_eq_iff {G : Graph} {surv : ℕ → Finset ℕ}
    (hanti : ∀ t, surv (t + 1) ⊆ surv t) (hsurv : ∀ t, surv t ⊆ Finset.range C.numTerm)
    {w : ℕ} (hw : w < G.n) (t : ℕ) :
    C.supportCursor surv w t = (C.supportArray w).length ↔ w ∈ C.prunedSet G (surv t) := by
  unfold supportCursor
  rw [cursorAt_eq_iff (valid := fun t i => C.entryLive (surv t) ((C.supportArray w).getD i default))
    (fun t i h => C.entryLive_mono (hanti t) h) t, mem_prunedSet,
    ← C.exists_live_entry_iff (hsurv t) hw]
  constructor
  · rintro hall
    refine ⟨hw, ?_⟩
    rintro ⟨x, hx, hl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := hall i hi
    rw [List.getD_eq_getElem _ _ hi, hl] at this
    exact absurd this (by decide)
  · rintro ⟨_, hno⟩ i hi
    rw [List.getD_eq_getElem _ _ hi]
    cases h : C.entryLive (surv t) (C.supportArray w)[i]
    · rfl
    · exact (hno ⟨_, List.getElem_mem hi, h⟩).elim

/-- A live support entry of `w` gives a walk from `w` to the owner of a surviving terminal. The
walk uses no deleted edge and only live vertices, and it has at most as many edges as the walk of
the connector of the entry (none for a terminal entry). -/
theorem supportWalk_spec {G : Graph} (hG : G.IsValid) (hfit : C.FitsGraph G)
    {D surv : Finset ℕ} (hrule : C.ReverseIndexRule D surv) {w : ℕ} (hw : w < G.n)
    {x : SupportEntry} (hx : x ∈ C.supportArray w) (hl : C.entryLive surv x = true) :
    C.entryTerm x ∈ surv ∧
      (C.supportWalk x).IsWalk G w (C.owner (C.entryTerm x)) ∧
      (∀ e ∈ (C.supportWalk x).edges, e ∉ D) ∧
      (∀ y ∈ (C.supportWalk x).verts, y ∈ C.liveSet G surv) ∧
      (∀ c pos, x = .onWalk c pos →
        (C.supportWalk x).edges.length ≤ (C.walk c).edges.length) ∧
      (∀ t, x = .term t → (C.supportWalk x).edges = []) := by
  rcases (C.mem_supportArray).mp hx with ⟨t, _, ho, rfl⟩ | ⟨c, hc, pos, hpos, rfl⟩
  · refine ⟨by simpa [entryLive, entryTerm] using hl, ?_, by simp [supportWalk, Walk.empty],
      by simp [supportWalk, Walk.empty], by simp, fun _ _ => rfl⟩
    rw [entryTerm, ho, supportWalk]
    exact ⟨hw, hw, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · have hel : C.Eligible surv c := by simpa [entryLive] using hl
    obtain ⟨hlt, hget⟩ := (C.mem_positionsOn).mp hpos
    have hwalk := (hfit.2 c hc).2.2
    refine ⟨hel.2.1, ?_, ?_, ?_, ?_, by simp⟩
    · rw [supportWalk, entryTerm]
      have := Walk.isWalk_reverse (isWalk_prefix hG hwalk hlt)
      rwa [hget] at this
    · intro e he
      rw [supportWalk, edges_reverse, List.mem_reverse] at he
      exact C.eligible_edge_not_deleted hrule hel (edges_prefix_subset _ _ e he)
    · intro y hy
      rw [supportWalk, verts_reverse, List.mem_reverse] at hy
      exact C.eligible_vert_live hG hfit hel (verts_prefix_subset _ y hy)
    · rintro c' pos' heq
      cases heq
      rw [supportWalk, edges_reverse, List.length_reverse]
      exact length_edges_prefix_le _ _

end

end ConnectorSystem

end MinCostFlow.HierPaths
