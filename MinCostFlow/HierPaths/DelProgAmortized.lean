module

public import MinCostFlow.HierPaths.DelProgEntry

/-!
# Event charges for the Delete program

The reverse scan charges updates and enumerated terminals. The remaining passes charge incidence
records, stored walk vertices, and the advances of the two cursor tables.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner

private theorem sumWeights (f : ℕ → List ℕ) (l : List ℕ) :
    (l.map fun i => 2 + (f i).length).sum = 2 * l.length + (l.flatMap f).length := by
  induction l with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.flatMap_cons,
      List.length_append, ih]
    omega

private theorem reportCharge (x : HierConcrete) (cs : List ℕ) :
    rangeCost (delOutputConnCost x cs) 0 cs.length =
      200 * (x.walkPassVerts cs).length + 106 * cs.length := by
  unfold delOutputConnCost HierConcrete.walkPassVerts
  rw [delRangeCost_list (fun c => 200 * (x.H.A.C.walk c).verts.length + 106) cs]
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append,
      List.length_cons, ih]
    omega

private theorem cursorMoves {N : ℕ} {old new : ℕ → ℕ} {T : List ℕ} (hT : T.Nodup)
    (hTN : ∀ w ∈ T, w < N) (hge : ∀ w, old w ≤ new w)
    (hout : ∀ w, w ∉ T → new w = old w) :
    ∑ w ∈ Finset.range N, new w =
      (∑ w ∈ Finset.range N, old w) + (T.map fun w => new w - old w).sum := by
  calc
    _ = ∑ w ∈ Finset.range N, (old w + (new w - old w)) :=
      Finset.sum_congr rfl fun w _ => (Nat.add_sub_of_le (hge w)).symm
    _ = _ := by
      rw [Finset.sum_add_distrib, ← List.sum_toFinset _ hT]
      congr 1
      refine (Finset.sum_subset (fun w hw => Finset.mem_range.mpr (hTN w (List.mem_toFinset.mp hw)))
        fun w _ hw => ?_).symm
      rw [hout w (fun h => hw (List.mem_toFinset.mpr h)), Nat.sub_self]

/-- The actual machine cost is bounded by the increment in the same events that define the
potential, plus a fixed charge for the reverse list and the call. -/
theorem hierDeleteEntryCost_le_events {a : ℕ} (x : HierConcrete) (e : ℕ)
    (hrel : x.H.Rel a x.ms) (hG : x.ms.abs.G.IsValid) :
    hierDeleteEntryCost x e ≤ hierPhiScale *
      (1 + x.H.ξ + 2 * (x.H.A.events x.n (x.H.A.deleteState x.ms.st e) -
        x.H.A.events x.n x.ms.st)) := by
  let A := x.H.A
  let st := x.ms.st
  let st' := A.deleteState st e
  let lost := A.newLost st e
  let cs := x.delWorkConns e
  let p := x.afterDelConns e
  let y := p.refreshPairs cs
  let z := y.refreshOwners lost
  let q := x.afterDelCursors e
  have hperm : List.Perm cs (A.newInelig st e) := by
    apply (List.perm_ext_iff_of_nodup (nodup_delCollect _ _) (List.nodup_dedup _)).mpr
    intro c
    have h := delCollect_newInelig A st e
    change cs.toFinset = _ at h
    change c ∈ cs ↔ c ∈ A.newInelig st e
    calc
      c ∈ cs ↔ c ∈ cs.toFinset := List.mem_toFinset.symm
      _ ↔ c ∈ (A.newInelig st e).toFinset := by rw [h]
      _ ↔ c ∈ A.newInelig st e := List.mem_toFinset
  have ht : ∀ t ∈ lost, t < A.C.numTerm := by
    intro t ht
    exact ((A.mem_surv).mp ((A.mem_newLost_iff hrel.spec.arrays hrel.inv e t).mp ht).1).1
  have hc : ∀ c ∈ cs, c < A.C.numConn := fun c hc =>
    ((A.mem_newInelig_iff hrel.spec.arrays hrel.inv e c).mp (hperm.mem_iff.mp hc)).1.1
  have hy : y.H = x.H := (p.refreshPairs_data cs).1
  have hz : z.H = x.H := (y.refreshOwners_data lost).1.trans hy
  have hyn : y.n = x.n :=
    (congrArg (fun s : PathDSAbsState => s.G.n) (p.refreshPairs_other cs).1).trans rfl
  have hzn : z.n = x.n := (y.refreshOwners_n lost).trans hyn
  obtain ⟨hS, hP⟩ := x.afterDelCursors_tables e hrel.spec.arrays hG hrel.inv
  have hfinal : z.refreshWalkVerts (z.walkPassVerts cs) = q := x.afterDelCursors_eq e
  have hP' : y.ms.st.pairCur = st'.pairCur := by
    have h := (z.refreshWalkVerts_other (z.walkPassVerts cs)).2.1
    rw [hfinal, hP] at h
    have hzpair : z.ms.st.pairCur = y.ms.st.pairCur := by
      dsimp only [z]
      rw [y.refreshOwners_eq_walk]
      exact (y.refreshWalkVerts_other _).2.1
    exact (h.trans hzpair).symm
  have hp := delPairPass_rangeCost p cs (fun c h => hrel.spec.arrays.pairOf_lt c (hc c h))
  change rangeCost (delPairPassStepCost p cs) 0 cs.length +
      90 * (∑ i ∈ Finset.range A.numPairs, st.pairCur i) ≤
    261 * cs.length + 90 * (∑ i ∈ Finset.range A.numPairs, y.ms.st.pairCur i) at hp
  rw [hP'] at hp
  have ho := delOwnerPass_rangeCost y lost (fun t h => by
    rw [hy, hyn]; exact hrel.spec.arrays.fits.1 t (ht t h))
  have hys : y.ms.st.supCur = st.supCur := (p.refreshPairs_other cs).2.1
  rw [hyn, hys] at ho
  have hv := delWalkPass_rangeCost z cs (fun c h v hv => by
    rw [hz] at hv
    rw [hzn]
    exact Walk.isWalk_verts_lt hG (hrel.spec.arrays.fits.2 c (hc c h)).2.2 v hv)
  rw [hzn, hfinal, hS] at hv
  have hvs : (z.walkPassVerts cs).length = (x.walkPassVerts cs).length := by
    unfold HierConcrete.walkPassVerts
    rw [hz]
  rw [hvs] at hv
  have hreport := reportCharge q cs
  have hqv : (q.walkPassVerts cs).length = (x.walkPassVerts cs).length := by
    unfold HierConcrete.walkPassVerts
    rw [x.afterDelCursors_H e]
  rw [hqv] at hreport
  have hOwnerSize : delOutputOwnerExpr.size ≤ 20 := by decide
  have hOwnerCost : lost.length * (delOutputOwnerExpr.size + 176) ≤ 196 * lost.length := by
    rw [Nat.mul_comm lost.length]
    exact Nat.mul_le_mul_right _ (by omega)
  let l := A.revList e
  let L := A.newLoss st e
  have hr := delScan_rangeCost (x.markDeleted e) ((x.markDeleted e).revStart e) l
  change rangeCost (delScanStepCost (x.markDeleted e) l ((x.markDeleted e).revStart e))
      ((x.markDeleted e).revStart e) ((x.markDeleted e).revStart e + l.length) +
      (700 * st.loss.updates + 130 * st.loss.enumerated) ≤
    1408 * l.length + (700 * L.updates + 130 * L.enumerated) at hr
  have hr' : delEntryStartCost x e + (700 * st.loss.updates + 130 * st.loss.enumerated) ≤
      1417 * l.length + 150 + (700 * L.updates + 130 * L.enumerated) := by
    unfold delEntryStartCost
    change rangeCost (delScanStepCost (x.markDeleted e) l ((x.markDeleted e).revStart e))
      ((x.markDeleted e).revStart e) ((x.markDeleted e).revStart e + l.length) +
      9 * l.length + 150 + _ ≤ _
    omega
  obtain ⟨_, _, _, hU, hE⟩ := A.newLoss_spec hrel.spec.arrays hrel.inv e
  have hlen : l.length ≤ x.H.ξ := hrel.spec.arrays.rev_length e
  have hSsum := cursorMoves (N := x.n) (old := st.supCur) (new := st'.supCur)
    (T := A.touchedVerts st e) (List.nodup_dedup _)
    (fun w hw => A.lt_of_mem_touchedVerts hrel.spec.arrays hG hrel.inv e hw)
    (fun w => by
      show st.supCur w ≤ if w ∈ A.touchedVerts st e then _ else _
      split_ifs
      · exact le_advance _ _ _
      · exact le_rfl)
    (fun w hw => by simp only [st', StaticArrays.deleteState, hw, ↓reduceIte])
  have hPsum := cursorMoves (N := A.numPairs) (old := st.pairCur) (new := st'.pairCur)
    (T := A.touchedPairs st e) (List.nodup_dedup _)
    (fun i hi => by
      rw [StaticArrays.touchedPairs, List.mem_dedup, List.mem_map] at hi
      obtain ⟨c, hc, rfl⟩ := hi
      exact hrel.spec.arrays.pairOf_lt c
        ((A.mem_newInelig_iff hrel.spec.arrays hrel.inv e c).mp hc).1.1)
    (fun i => by
      show st.pairCur i ≤ if i ∈ A.touchedPairs st e then _ else _
      split_ifs
      · exact le_advance _ _ _
      · exact le_rfl)
    (fun i hi => by simp only [st', StaticArrays.deleteState, hi, ↓reduceIte])
  rw [hSsum] at hv
  rw [hPsum] at hp
  have hTerm := sumWeights A.termConns lost
  have hConn : ((A.newInelig st e).map A.connWeight).sum =
      2 * cs.length + (x.walkPassVerts cs).length :=
    (hperm.map A.connWeight).sum_eq.symm.trans (sumWeights (fun c => (A.C.walk c).verts) cs)
  have hEvent := A.events_deleteState hrel.spec.arrays hG hrel.inv e
  change A.events x.n st' = _ at hEvent
  change (lost.map A.termWeight).sum = _ at hTerm
  rw [hTerm, hConn] at hEvent
  unfold hierDeleteEntryCost delEntryWorkCost delEntryReportsCost delEntryCursorsCost hierPhiScale
  change delEntryStartCost x e + (99 * (lost.flatMap A.termConns).length + 104 * lost.length + 30) +
      (rangeCost (delPairPassStepCost p cs) 0 cs.length +
        rangeCost (delOwnerPassStepCost y lost) 0 lost.length +
        rangeCost (delWalkPassStepCost z cs) 0 cs.length +
        18 * cs.length + 9 * lost.length + 50) + 2 +
      (lost.length * (delOutputOwnerExpr.size + 176) +
        rangeCost (delOutputConnCost (q.afterReports (lost.map q.H.A.C.owner)) cs) 0 cs.length +
        cs.length * 9 + 35) + 12 * (lost.length + cs.length) + 57 ≤ _
  rw [show delOutputConnCost (q.afterReports (lost.map q.H.A.C.owner)) cs =
    delOutputConnCost q cs by rfl, hreport]
  dsimp only [A, st, st', L, z, HierConcrete.n] at hEvent hU hE hp ho hv hr' ⊢
  omega

end MinCostFlow.HierPaths
