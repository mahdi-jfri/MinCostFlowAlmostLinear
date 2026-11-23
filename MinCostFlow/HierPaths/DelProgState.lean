module

public import MinCostFlow.HierPaths.DelProgFinish
public import MinCostFlow.HierPaths.DelProgOutputOwner

/-!
# The Delete state after the machine passes

The loss scan fixes the surviving terminals. The connector pass then fixes eligibility.
The cursor and report passes use that fixed eligibility and yield the model's final state.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

/-- The concrete state after marking the edge and running the loss and connector passes. -/
def HierConcrete.afterDelConns (x : HierConcrete) (e : ℕ) : HierConcrete :=
  ((x.markDeleted e).withLoss (x.H.A.newLoss x.ms.st e)).markIneligList
    ((x.H.A.newLost x.ms.st e).flatMap x.H.A.termConns)

/-- The connector list produced in first-visit order. -/
def HierConcrete.delWorkConns (x : HierConcrete) (e : ℕ) : List ℕ :=
  delCollect x.ms.st.inelig ((x.H.A.newLost x.ms.st e).flatMap x.H.A.termConns)

theorem HierConcrete.afterDelConns_inelig (x : HierConcrete) (e : ℕ) :
    (x.afterDelConns e).ms.st.inelig = (x.H.A.deleteState x.ms.st e).inelig := by
  change x.ms.st.inelig ∪ ((x.H.A.newLost x.ms.st e).flatMap x.H.A.termConns).toFinset =
    x.ms.st.inelig ∪ (x.H.A.newInelig x.ms.st e).toFinset
  rw [← delCollect_newInelig]
  ext c
  simp only [Finset.mem_union, List.mem_toFinset, mem_delCollect]
  tauto

theorem HierConcrete.afterDelConns_surv (x : HierConcrete) (e : ℕ) :
    x.H.A.surv (x.afterDelConns e).ms.st = x.H.A.newSurv x.ms.st e := rfl

/-- Before the support scans, the pair scan leaves the rest of the state intact. -/
theorem HierConcrete.refreshPairs_other (x : HierConcrete) (cs : List ℕ) :
    (x.refreshPairs cs).ms.abs = x.ms.abs ∧
      (x.refreshPairs cs).ms.st.supCur = x.ms.st.supCur ∧
      (x.refreshPairs cs).ms.st.deleted = x.ms.st.deleted := by
  induction cs using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | append_singleton cs c ih =>
    rw [x.refreshPairs_append_one]
    exact ih

/-- The support scans leave the pair cursors and abstract state intact. -/
theorem HierConcrete.refreshWalkVerts_other (x : HierConcrete) (vs : List ℕ) :
    (x.refreshWalkVerts vs).ms.abs = x.ms.abs ∧
      (x.refreshWalkVerts vs).ms.st.pairCur = x.ms.st.pairCur ∧
      (x.refreshWalkVerts vs).ms.st.deleted = x.ms.st.deleted := by
  induction vs using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | append_singleton vs v ih =>
    rw [x.refreshWalkVerts_append_one]
    exact ih

/-- Refreshing owners is refreshing their mapped vertex list. -/
theorem HierConcrete.refreshOwners_eq_walk (x : HierConcrete) (ts : List ℕ) :
    x.refreshOwners ts = x.refreshWalkVerts (ts.map x.H.A.C.owner) := by
  induction ts using List.reverseRecOn with
  | nil => rfl
  | append_singleton ts t ih =>
    rw [x.refreshOwners_append_one, List.map_append, List.map_singleton,
      x.refreshWalkVerts_append_one, ih]

/-- The machine cursor passes before it writes the pruned bits. -/
def HierConcrete.afterDelCursors (x : HierConcrete) (e : ℕ) : HierConcrete :=
  ((x.afterDelConns e).refreshPairs (x.delWorkConns e)).refreshWalkVerts
    (x.H.A.delSupportVisits x.ms.st e)

/-- The sequential support passes agree with a single pass over their joined vertex list. -/
theorem HierConcrete.afterDelCursors_eq (x : HierConcrete) (e : ℕ) :
    let y := (x.afterDelConns e).refreshPairs (x.delWorkConns e)
    let z := y.refreshOwners (x.H.A.newLost x.ms.st e)
    z.refreshWalkVerts (z.walkPassVerts (x.delWorkConns e)) = x.afterDelCursors e := by
  dsimp only
  let y := (x.afterDelConns e).refreshPairs (x.delWorkConns e)
  let z := y.refreshOwners (x.H.A.newLost x.ms.st e)
  have hHy : y.H = x.H := (HierConcrete.refreshPairs_data (x.afterDelConns e) _).1
  have hHz : z.H = x.H := (y.refreshOwners_data _).1.trans hHy
  change z.refreshWalkVerts (z.walkPassVerts _) = _
  rw [walkPassVerts, hHz]
  have hz : z = y.refreshWalkVerts ((x.H.A.newLost x.ms.st e).map x.H.A.C.owner) := by
    dsimp only [z]
    rw [y.refreshOwners_eq_walk, hHy]
  rw [hz, ← y.refreshWalkVerts_append]
  rfl

/-- The cursor passes restore both cursor tables of the abstract deletion. -/
theorem HierConcrete.afterDelCursors_tables (x : HierConcrete) (e : ℕ) {ξ κ : ℕ}
    (hA : x.H.A.Spec x.ms.abs.G ξ κ) (hG : x.ms.abs.G.IsValid)
    (hinv : x.H.A.DelInv x.ms.abs.G x.ms.st) :
    let st' := x.H.A.deleteState x.ms.st e
    (x.afterDelCursors e).ms.st.supCur = st'.supCur ∧
      (x.afterDelCursors e).ms.st.pairCur = st'.pairCur := by
  dsimp only
  let A := x.H.A
  let P := x.afterDelConns e
  let cs := x.delWorkConns e
  let Y := P.refreshPairs cs
  let vs := A.delSupportVisits x.ms.st e
  have hp : P.H = x.H := rfl
  have hY : Y.H = x.H := (P.refreshPairs_data cs).1.trans hp
  have hS : Y.H.A.surv Y.ms.st = A.newSurv x.ms.st e := by
    simp only [StaticArrays.surv, hY, Y, (P.refreshPairs_data cs).2.1]
    rfl
  have hySup : Y.ms.st.supCur = x.ms.st.supCur := (P.refreshPairs_other cs).2.1
  have hpair : Y.ms.st.pairCur = (A.deleteState x.ms.st e).pairCur := by
    rw [P.refreshPairs_eq cs]
    change refreshAll (fun q => A.pairValid (A.newSurv x.ms.st e) q)
      (fun q => (A.pairConns q).length) x.ms.st.pairCur (A.delPairVisits x.ms.st e) = _
    apply Eq.symm (A.pairCur_deleteState_eq (A.mem_delPairVisits x.ms.st e) ?_)
    intro q hm
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
    have hmem := (mem_delCollect.mp hc).1
    obtain ⟨t, ht, htc⟩ := List.mem_flatMap.mp hmem
    have ht' := ((A.mem_surv).mp ((A.mem_newLost_iff hA hinv e t).mp ht).1).1
    have hc' := ((hA.mem_termConns t ht' c).mp htc).1
    exact (hinv.pairCur _ (hA.pairOf_lt _ hc')).1
  change (Y.refreshWalkVerts vs).ms.st.supCur = _ ∧ (Y.refreshWalkVerts vs).ms.st.pairCur = _
  constructor
  · rw [Y.refreshWalkVerts_eq vs, hS, hY, hySup]
    exact (A.supCur_deleteState_eq (A.mem_delSupportVisits x.ms.st e) fun v hv =>
      (hinv.supCur v (A.lt_of_mem_touchedVerts hA hG hinv e
        ((A.mem_delSupportVisits x.ms.st e v).mp hv))).1).symm
  · exact ((Y.refreshWalkVerts_other vs).2.1).trans hpair

theorem HierConcrete.afterDelCursors_abs (x : HierConcrete) (e : ℕ) :
    (x.afterDelCursors e).ms.abs = (x.markDeleted e).ms.abs := by
  unfold afterDelCursors
  rw [(HierConcrete.refreshWalkVerts_other ..).1, (HierConcrete.refreshPairs_other ..).1]
  rfl

theorem HierConcrete.afterDelCursors_H (x : HierConcrete) (e : ℕ) :
    (x.afterDelCursors e).H = x.H := by
  unfold afterDelCursors
  rw [(HierConcrete.refreshWalkVerts_data ..).1, (HierConcrete.refreshPairs_data ..).1]
  rfl

/-- The final state, after setting the output vertices' pruned bits. -/
def HierConcrete.afterDelReports (x : HierConcrete) (e : ℕ) : HierConcrete :=
  (x.afterDelCursors e).afterReports (x.H.A.delSupportVisits x.ms.st e)

private theorem delState_fields {s t : DelState}
    (h1 : s.loss = t.loss) (h2 : s.deleted = t.deleted) (h3 : s.inelig = t.inelig)
    (h4 : s.supCur = t.supCur) (h5 : s.pairCur = t.pairCur) : s = t := by
  cases s
  cases t
  simp_all

/-- The program's final state is the abstract deletion model. -/
theorem HierConcrete.afterDelReports_eq (x : HierConcrete) (e : ℕ) {ξ κ : ℕ}
    (hA : x.H.A.Spec x.ms.abs.G ξ κ) (hG : x.ms.abs.G.IsValid)
    (hinv : x.H.A.DelInv x.ms.abs.G x.ms.st)
    (hV : x.ms.abs.Vhat = x.H.A.C.prunedSet x.ms.abs.G (x.H.A.surv x.ms.st)) :
    x.afterDelReports e = ⟨x.H, x.H.delete x.ms e⟩ := by
  let A := x.H.A
  let P := x.afterDelConns e
  let Y := P.refreshPairs (x.delWorkConns e)
  let Z := x.afterDelCursors e
  let vs := A.delSupportVisits x.ms.st e
  have hZA : Z.ms.abs = (x.markDeleted e).ms.abs := x.afterDelCursors_abs e
  have hZH : Z.H = x.H := x.afterDelCursors_H e
  have hVG : Z.ms.abs.G = x.ms.abs.G := by rw [hZA]; rfl
  have hZV : Z.ms.abs.Vhat = x.ms.abs.Vhat := by rw [hZA]; rfl
  obtain ⟨hSup, hPair⟩ := x.afterDelCursors_tables e hA hG hinv
  have hST : Z.ms.st = A.deleteState x.ms.st e := by
    apply delState_fields
    · exact ((Y.refreshWalkVerts_data vs).2.1).trans (P.refreshPairs_data _).2.1
    · exact ((Y.refreshWalkVerts_other vs).2.2).trans (P.refreshPairs_other _).2.2
    · exact (((Y.refreshWalkVerts_data vs).2.2).trans
        (P.refreshPairs_data _).2.2).trans (x.afterDelConns_inelig e)
    · exact hSup
    · exact hPair
  have hOut := Z.delReports_spec (e := e) (st := x.ms.st)
    (by rw [hZH, hVG]; exact hA) (by rwa [hVG])
    (by rw [hZH, hVG]; exact hinv) (by rw [hZH]; exact hSup)
    (by rw [hZH, hVG, hZV]; exact hV)
  have hMono := (A.delete_live_facts hA hG hinv e).1
  rw [StaticArrays.surv_deleteState] at hMono
  have hbits : x.ms.abs.Vhat ∪ (Z.delReports vs).toFinset =
      A.C.prunedSet x.ms.abs.G (A.newSurv x.ms.st e) := by
    rw [show (Z.delReports vs).toFinset =
      A.C.prunedSet x.ms.abs.G (A.newSurv x.ms.st e) \ x.ms.abs.Vhat from by
        simpa only [hZH, hVG, hZV] using hOut.2]
    exact Finset.union_sdiff_of_subset (hV.symm ▸ hMono)
  change HierConcrete.mk Z.H (ModelState.mk Z.ms.st
    { Z.ms.abs with Vhat := Z.ms.abs.Vhat ∪ (Z.delReports vs).toFinset }) = _
  rw [hZH, hST, hZV, hbits, hZA]
  rfl

end MinCostFlow.HierPaths

end
