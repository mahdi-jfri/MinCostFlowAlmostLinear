module

public import MinCostFlow.HierPaths.DeleteState
public import MinCostFlow.HierPaths.DeleteScan

/-!
# The operation `Delete`

`Delete(e)` runs in four parts.

1. Scan the reverse list of `e`: each listed terminal that has not failed is marked directly
   failed and the loss counters run on it (`scan`). This gives the list `newLost` of terminals
   that became globally lost.
2. For each newly lost terminal, read its connectors and keep those whose eligibility bit is still
   set (`newInelig`). Clear their bits.
3. Refresh the cursors: the support cursors of the owners of the newly lost terminals and of the
   vertices on the walks of the newly ineligible connectors (`touchedVerts`), and the cursors of the
   pairs of children of those connectors (`touchedPairs`). A refresh is `advance` of
   `HierPaths/Cursor.lean`.
4. Output the touched vertices whose support cursor has just reached the end (`deleteOut`).

The main result is `delete_spec`: from a state with the invariant `DelInv`, the new state has the
invariant again, with `e` added to the deleted edges, and the output has no repetition and is
exactly the new pruned set minus the old one. Since `DelInv` contains the reverse-index rule, the
facts of `HierPaths/Live.lean` hold after the step; `delete_live_facts` states them.

`deleteCost` counts the unit steps of the four parts; `HierPaths/Potential.lean` bounds it.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

namespace StaticArrays

variable (A : StaticArrays)

/-- The loss counters after the scan of the reverse list of `e`. -/
def newLoss (st : DelState) (e : ℕ) : LossState :=
  (scan A.x A.b st.loss (A.revList e)).1

/-- The terminals that become globally lost in `Delete(e)`. -/
def newLost (st : DelState) (e : ℕ) : List ℕ :=
  (scan A.x A.b st.loss (A.revList e)).2

/-- The connectors that become ineligible in `Delete(e)`: the connectors of the newly lost
terminals whose bit is still set, each once. -/
def newInelig (st : DelState) (e : ℕ) : List ℕ :=
  (((A.newLost st e).flatMap A.termConns).filter fun c => c ∉ st.inelig).dedup

/-- The vertices whose support cursor `Delete(e)` refreshes. -/
def touchedVerts (st : DelState) (e : ℕ) : List ℕ :=
  ((A.newLost st e).map A.C.owner ++
    (A.newInelig st e).flatMap fun c => (A.C.walk c).verts).dedup

/-- The pairs of children whose cursor `Delete(e)` refreshes. -/
def touchedPairs (st : DelState) (e : ℕ) : List ℕ :=
  ((A.newInelig st e).map A.pairOf).dedup

/-- The surviving terminals after `Delete(e)`. -/
def newSurv (st : DelState) (e : ℕ) : Finset ℕ :=
  Finset.range A.C.numTerm \ (A.newLoss st e).glob

/-- The state after `Delete(e)`. -/
def deleteState (st : DelState) (e : ℕ) : DelState where
  loss := A.newLoss st e
  deleted := insert e st.deleted
  inelig := st.inelig ∪ (A.newInelig st e).toFinset
  supCur w :=
    if w ∈ A.touchedVerts st e then
      advance (A.supValid (A.newSurv st e) w) (A.C.supportArray w).length (st.supCur w)
    else st.supCur w
  pairCur p :=
    if p ∈ A.touchedPairs st e then
      advance (A.pairValid (A.newSurv st e) p) (A.pairConns p).length (st.pairCur p)
    else st.pairCur p

/-- The output of `Delete(e)`: the touched vertices whose support cursor has just reached the
end. -/
def deleteOut (st : DelState) (e : ℕ) : List ℕ :=
  (A.touchedVerts st e).filter fun w =>
    decide (st.supCur w < (A.C.supportArray w).length ∧
      (A.deleteState st e).supCur w = (A.C.supportArray w).length)

/-- The unit steps of `Delete(e)`: one to start, one per entry of the reverse list, the counter
updates and enumerated terminals of the loss counters, for each newly lost terminal one step,
one per connector and one for the refresh of its owner, for each newly ineligible connector one
step, one per vertex of its walk and one for its pair, one per cursor move, and one per touched
vertex for the output test. -/
def deleteCost (st : DelState) (e : ℕ) : ℕ :=
  1 + (A.revList e).length +
    ((A.newLoss st e).updates - st.loss.updates) +
    ((A.newLoss st e).enumerated - st.loss.enumerated) +
    ((A.newLost st e).map fun t => 2 + (A.termConns t).length).sum +
    ((A.newInelig st e).map fun c => 2 + (A.C.walk c).verts.length).sum +
    ((A.touchedVerts st e).map fun w => (A.deleteState st e).supCur w - st.supCur w).sum +
    ((A.touchedPairs st e).map fun p => (A.deleteState st e).pairCur p - st.pairCur p).sum +
    (A.touchedVerts st e).length

end StaticArrays

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

namespace StaticArrays

variable (A : StaticArrays) {G : Graph} {ξ κ : ℕ}

public section

theorem surv_deleteState (st : DelState) (e : ℕ) :
    A.surv (A.deleteState st e) = A.newSurv st e := rfl

/-- The scan facts in terms of the state. -/
theorem newLoss_spec {st : DelState} (hA : A.Spec G ξ κ) (hinv : A.DelInv G st) (e : ℕ) :
    LossInv A.x A.b (st.loss.failed ∪ (A.revList e).toFinset) (A.newLoss st e) ∧
      (A.newLost st e).Nodup ∧
      (A.newLost st e).toFinset = (A.newLoss st e).glob \ st.loss.glob ∧
      st.loss.updates ≤ (A.newLoss st e).updates ∧
      st.loss.enumerated ≤ (A.newLoss st e).enumerated := by
  have hl : ∀ t ∈ A.revList e, t < 2 ^ A.x := fun t ht => hA.numTerm_eq ▸ hA.rev_lt e t ht
  obtain ⟨h1, h2, h3, h4, h5⟩ := scan_spec hinv.loss hl
  refine ⟨h1, h2, ?_, h4, h5⟩
  rw [newLost, h3, newLoss, h1.glob, hinv.loss.glob]

theorem newSurv_subset {st : DelState} (hA : A.Spec G ξ κ) (hinv : A.DelInv G st) (e : ℕ) :
    A.newSurv st e ⊆ A.surv st := by
  obtain ⟨h1, _⟩ := A.newLoss_spec hA hinv e
  intro t ht
  rw [newSurv, Finset.mem_sdiff] at ht
  rw [surv, Finset.mem_sdiff]
  refine ⟨ht.1, fun hg => ht.2 ?_⟩
  rw [h1.glob]
  rw [hinv.loss.glob] at hg
  exact globalLost_mono Finset.subset_union_left hg

/-- A terminal survives before but not after exactly when it is newly lost. -/
theorem mem_newLost_iff {st : DelState} (hA : A.Spec G ξ κ) (hinv : A.DelInv G st) (e t : ℕ) :
    t ∈ A.newLost st e ↔ t ∈ A.surv st ∧ t ∉ A.newSurv st e := by
  obtain ⟨h1, _, h3, _⟩ := A.newLoss_spec hA hinv e
  rw [← List.mem_toFinset, h3, Finset.mem_sdiff, surv, newSurv, Finset.mem_sdiff,
    Finset.mem_sdiff, Finset.mem_range]
  have hsub : (A.newLoss st e).glob ⊆ Finset.range A.C.numTerm := by
    rw [h1.glob, hA.numTerm_eq]; exact globalLost_subset_range
  constructor
  · rintro ⟨hn, ho⟩
    exact ⟨⟨Finset.mem_range.mp (hsub hn), ho⟩, fun h => h.2 hn⟩
  · rintro ⟨⟨hlt, ho⟩, hn⟩
    exact ⟨by by_contra h; exact hn ⟨hlt, h⟩, ho⟩

/-- The newly ineligible connectors are those eligible before and not after. -/
theorem mem_newInelig_iff {st : DelState} (hA : A.Spec G ξ κ) (hinv : A.DelInv G st) (e c : ℕ) :
    c ∈ A.newInelig st e ↔
      A.C.Eligible (A.surv st) c ∧ ¬ A.C.Eligible (A.newSurv st e) c := by
  rw [newInelig, List.mem_dedup, List.mem_filter, List.mem_flatMap, hinv.inelig_eq]
  simp only [Finset.mem_filter, Finset.mem_range, not_and, not_not, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨t, ht, hc⟩, hel⟩
    obtain ⟨hts, htn⟩ := (A.mem_newLost_iff hA hinv e t).mp ht
    have htN : t < A.C.numTerm := ((A.mem_surv).mp hts).1
    obtain ⟨hcN, hend⟩ := (hA.mem_termConns t htN c).mp hc
    refine ⟨hel hcN, fun h => ?_⟩
    rcases hend with rfl | rfl
    · exact htn h.2.1
    · exact htn h.2.2
  · rintro ⟨hel, hnel⟩
    refine ⟨?_, fun _ => hel⟩
    have : ¬ (A.C.endA c ∈ A.newSurv st e ∧ A.C.endB c ∈ A.newSurv st e) :=
      fun h => hnel ⟨hel.1, h⟩
    by_cases ha : A.C.endA c ∈ A.newSurv st e
    · have hb : A.C.endB c ∉ A.newSurv st e := fun hb => this ⟨ha, hb⟩
      refine ⟨A.C.endB c, (A.mem_newLost_iff hA hinv e _).mpr ⟨hel.2.2, hb⟩, ?_⟩
      exact (hA.mem_termConns _ ((A.mem_surv).mp hel.2.2).1 c).mpr ⟨hel.1, Or.inr rfl⟩
    · refine ⟨A.C.endA c, (A.mem_newLost_iff hA hinv e _).mpr ⟨hel.2.1, ha⟩, ?_⟩
      exact (hA.mem_termConns _ ((A.mem_surv).mp hel.2.1).1 c).mpr ⟨hel.1, Or.inl rfl⟩

/-- A support entry that dies in `Delete(e)` belongs to a touched vertex. -/
theorem mem_touchedVerts_of_dies {st : DelState} (hA : A.Spec G ξ κ) (hinv : A.DelInv G st)
    (e : ℕ) {w : ℕ} {y : SupportEntry} (hy : y ∈ A.C.supportArray w)
    (hl : A.C.entryLive (A.surv st) y = true) (hl' : A.C.entryLive (A.newSurv st e) y = false) :
    w ∈ A.touchedVerts st e := by
  rw [touchedVerts, List.mem_dedup, List.mem_append]
  rcases (A.C.mem_supportArray).mp hy with ⟨t, _, ho, rfl⟩ | ⟨c, _, pos, hpos, rfl⟩
  · left
    simp only [ConnectorSystem.entryLive, decide_eq_true_eq, decide_eq_false_iff_not] at hl hl'
    exact List.mem_map.mpr ⟨t, (A.mem_newLost_iff hA hinv e t).mpr ⟨hl, hl'⟩, ho⟩
  · right
    simp only [ConnectorSystem.entryLive, decide_eq_true_eq, decide_eq_false_iff_not] at hl hl'
    obtain ⟨hlt, hget⟩ := (A.C.mem_positionsOn).mp hpos
    refine List.mem_flatMap.mpr ⟨c, (A.mem_newInelig_iff hA hinv e c).mpr ⟨hl, hl'⟩, ?_⟩
    rw [← hget, List.getD_eq_getElem _ _ hlt]
    exact List.getElem_mem hlt

/-- A pair entry that dies in `Delete(e)` belongs to a touched pair. -/
theorem mem_touchedPairs_of_dies {st : DelState} (hA : A.Spec G ξ κ) (hinv : A.DelInv G st)
    (e : ℕ) {p c : ℕ} (hc : c ∈ A.pairConns p) (hl : A.C.Eligible (A.surv st) c)
    (hl' : ¬ A.C.Eligible (A.newSurv st e) c) : p ∈ A.touchedPairs st e := by
  rw [touchedPairs, List.mem_dedup, List.mem_map]
  exact ⟨c, (A.mem_newInelig_iff hA hinv e c).mpr ⟨hl, hl'⟩, (hA.mem_pairConns p c hc).2⟩

/-- The touched vertices are vertices of `G`. -/
theorem lt_of_mem_touchedVerts {st : DelState} (hA : A.Spec G ξ κ) (hG : G.IsValid)
    (hinv : A.DelInv G st) (e : ℕ) {w : ℕ} (hw : w ∈ A.touchedVerts st e) : w < G.n := by
  rw [touchedVerts, List.mem_dedup, List.mem_append] at hw
  rcases hw with hw | hw
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw
    exact hA.fits.1 t ((A.mem_surv).mp ((A.mem_newLost_iff hA hinv e t).mp ht).1).1
  · obtain ⟨c, hc, hwc⟩ := List.mem_flatMap.mp hw
    have hel := ((A.mem_newInelig_iff hA hinv e c).mp hc).1
    exact Walk.isWalk_verts_lt hG (hA.fits.2 c hel.1).2.2 w hwc

private theorem supValid_mono {S S' : Finset ℕ} (h : S' ⊆ S) (w i : ℕ)
    (hv : A.supValid S' w i = true) : A.supValid S w i = true :=
  A.C.entryLive_mono h hv

private theorem pairValid_mono {S S' : Finset ℕ} (h : S' ⊆ S) (p i : ℕ)
    (hv : A.pairValid S' p i = true) : A.pairValid S p i = true := by
  simp only [pairValid, decide_eq_true_eq] at hv ⊢
  exact hv.mono A.C h

/-- `Delete(e)` keeps the invariant, and adds `e` to the deleted edges. -/
theorem deleteState_inv {st : DelState} (hA : A.Spec G ξ κ) (hinv : A.DelInv G st) (e : ℕ) :
    A.DelInv G (A.deleteState st e) ∧ (A.deleteState st e).deleted = insert e st.deleted := by
  obtain ⟨hL, _, _, _, _⟩ := A.newLoss_spec hA hinv e
  have hsub := A.newSurv_subset hA hinv e
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · show LossInv A.x A.b (A.newLoss st e).failed (A.newLoss st e)
    rw [hL.failed]; exact hL
  · show (A.newLoss st e).failed ⊆ (insert e st.deleted).biUnion fun e => (A.revList e).toFinset
    rw [hL.failed, hinv.loss.failed]
    refine Finset.union_subset (hinv.failed_sub.trans ?_) ?_
    · exact Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.subset_insert _ _)
    · exact Finset.subset_biUnion_of_mem (fun e => (A.revList e).toFinset) (Finset.mem_insert_self _ _)
  · intro c hc e' he' hD
    rw [surv_deleteState]
    rcases Finset.mem_insert.mp hD with rfl | hD
    · intro hs
      rw [newSurv, Finset.mem_sdiff] at hs
      apply hs.2
      rw [hL.glob]
      have hmem : A.C.desig c ∈ st.loss.failed ∪ (A.revList e').toFinset :=
        Finset.mem_union_right _ (List.mem_toFinset.mpr (hA.rev_mem c hc e' he'))
      refine mem_globalLost_of_mem ?_ hmem
      rw [← hA.numTerm_eq]; exact Finset.mem_range.mp hs.1
    · exact fun hs => hinv.rule c hc e' he' hD (hsub hs)
  · show st.inelig ∪ (A.newInelig st e).toFinset =
      (Finset.range A.C.numConn).filter fun c => ¬ A.C.Eligible (A.newSurv st e) c
    ext c
    rw [Finset.mem_union, hinv.inelig_eq, List.mem_toFinset, A.mem_newInelig_iff hA hinv e c,
      Finset.mem_filter, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro (⟨hc, hn⟩ | ⟨hel, hn⟩)
      · exact ⟨hc, fun h => hn (h.mono A.C hsub)⟩
      · exact ⟨hel.1, hn⟩
    · rintro ⟨hc, hn⟩
      by_cases hel : A.C.Eligible (A.surv st) c
      · exact Or.inr ⟨hel, hn⟩
      · exact Or.inl ⟨hc, hel⟩
  · intro w hw
    have hold := hinv.supCur w hw
    show CurInv (A.supValid (A.newSurv st e) w) _ (if w ∈ A.touchedVerts st e then _ else _)
    split_ifs with ht
    · refine curInv_advance hold.1 fun i hi => ?_
      cases hv : A.supValid (A.newSurv st e) w i
      · rfl
      · have := hold.2.1 i hi
        rw [A.supValid_mono hsub w i hv] at this
        exact absurd this (by decide)
    · refine hold.of_le (A.supValid_mono hsub w) fun hlt => ?_
      cases hv : A.supValid (A.newSurv st e) w (st.supCur w)
      · exfalso
        apply ht
        refine A.mem_touchedVerts_of_dies hA hinv e (List.getElem_mem hlt) ?_ ?_
        · have := hold.2.2 hlt
          rwa [supValid, List.getD_eq_getElem _ _ hlt] at this
        · rwa [supValid, List.getD_eq_getElem _ _ hlt] at hv
      · rfl
  · intro p hp
    have hold := hinv.pairCur p hp
    show CurInv (A.pairValid (A.newSurv st e) p) _ (if p ∈ A.touchedPairs st e then _ else _)
    split_ifs with ht
    · refine curInv_advance hold.1 fun i hi => ?_
      cases hv : A.pairValid (A.newSurv st e) p i
      · rfl
      · have := hold.2.1 i hi
        rw [A.pairValid_mono hsub p i hv] at this
        exact absurd this (by decide)
    · refine hold.of_le (A.pairValid_mono hsub p) fun hlt => ?_
      cases hv : A.pairValid (A.newSurv st e) p (st.pairCur p)
      · exfalso
        apply ht
        have h1 := hold.2.2 hlt
        simp only [pairValid, decide_eq_true_eq, decide_eq_false_iff_not,
          List.getD_eq_getElem _ _ hlt] at h1 hv
        exact A.mem_touchedPairs_of_dies hA hinv e (List.getElem_mem hlt) h1 hv
      · rfl

/-- `Delete(e)` outputs, without repetition, exactly the vertices that become pruned. -/
theorem deleteOut_spec {st : DelState} (hA : A.Spec G ξ κ) (hG : G.IsValid)
    (hinv : A.DelInv G st) (e : ℕ) :
    (A.deleteOut st e).Nodup ∧
      (A.deleteOut st e).toFinset =
        A.C.prunedSet G (A.surv (A.deleteState st e)) \ A.C.prunedSet G (A.surv st) := by
  have hinv' := (A.deleteState_inv hA hinv e).1
  refine ⟨(List.nodup_dedup _).filter _, ?_⟩
  ext w
  rw [List.mem_toFinset, deleteOut, List.mem_filter, decide_eq_true_eq, Finset.mem_sdiff]
  constructor
  · rintro ⟨ht, hlt, heq⟩
    have hw := A.lt_of_mem_touchedVerts hA hG hinv e ht
    refine ⟨(A.supCur_eq_len_iff hinv' hw).mp heq, fun h => ?_⟩
    rw [← A.supCur_eq_len_iff hinv hw] at h
    omega
  · rintro ⟨hn, ho⟩
    have hw : w < G.n := ((A.C.mem_prunedSet).mp hn).1
    have heq := (A.supCur_eq_len_iff hinv' hw).mpr hn
    have hne : st.supCur w ≠ (A.C.supportArray w).length :=
      fun h => ho ((A.supCur_eq_len_iff hinv hw).mp h)
    have hle := (hinv.supCur w hw).1
    by_cases ht : w ∈ A.touchedVerts st e
    · exact ⟨ht, by omega, heq⟩
    · exfalso
      apply hne
      have : (A.deleteState st e).supCur w = st.supCur w := by
        simp only [deleteState, ht, ↓reduceIte]
      rw [← this, heq]

/-- The main theorem on `Delete(e)`: the invariant is kept, `e` is added to the deleted edges, and
the output lists, without repetition, exactly the newly pruned vertices. -/
theorem delete_spec {st : DelState} (hA : A.Spec G ξ κ) (hG : G.IsValid)
    (hinv : A.DelInv G st) (e : ℕ) :
    A.DelInv G (A.deleteState st e) ∧ (A.deleteState st e).deleted = insert e st.deleted ∧
      (A.deleteOut st e).Nodup ∧
      (A.deleteOut st e).toFinset =
        A.C.prunedSet G (A.surv (A.deleteState st e)) \ A.C.prunedSet G (A.surv st) := by
  obtain ⟨h1, h2⟩ := A.deleteState_inv hA hinv e
  obtain ⟨h3, h4⟩ := A.deleteOut_spec hA hG hinv e
  exact ⟨h1, h2, h3, h4⟩

/-- The facts of `HierPaths/Live.lean` for a state with the invariant: the pruned set
only grows over a step, and eligible walks use no deleted edge and only live vertices. -/
theorem delete_live_facts {st : DelState} (hA : A.Spec G ξ κ) (hG : G.IsValid)
    (hinv : A.DelInv G st) (e : ℕ) :
    A.C.prunedSet G (A.surv st) ⊆ A.C.prunedSet G (A.surv (A.deleteState st e)) ∧
      (∀ c, A.C.Eligible (A.surv (A.deleteState st e)) c →
        (∀ e' ∈ (A.C.walk c).edges, e' ∉ (A.deleteState st e).deleted) ∧
        ∀ y ∈ (A.C.walk c).verts, y ∈ A.C.liveSet G (A.surv (A.deleteState st e))) := by
  have hinv' := (A.deleteState_inv hA hinv e).1
  refine ⟨A.C.prunedSet_mono (A.newSurv_subset hA hinv e), fun c hc => ⟨?_, ?_⟩⟩
  · exact fun e' he' => A.C.eligible_edge_not_deleted hinv'.rule hc he'
  · exact fun y hy => A.C.eligible_vert_live hG hA.fits hc hy

end

end StaticArrays

end MinCostFlow.HierPaths
