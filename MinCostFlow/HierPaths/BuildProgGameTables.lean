module

public import MinCostFlow.HierPaths.BuildProgGameSchedule

/-!
# The active arrays at consecutive rounds

Compacting the current tables along the selected indices gives the tables
for the next model round. The same original child number indexes both
its graph reservation and its parent terminal offset.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

private theorem tabList_map_getD (l : List ℕ) (f : ℕ → ℕ) :
    tabList l.length (fun i => f (l.getD i 0)) = l.map f := by
  apply List.ext_getElem
  · simp
  · intro i _ hi
    have h : i < l.length := by simpa using hi
    simp [tabList,List.getElem?_eq_getElem h]

/-- The graph-address and terminal-offset arrays use the same stable filter. -/
theorem BuildGameSchedule.compact_table (S : BuildGameSchedule) (t : ℕ) (f : ℕ → ℕ) :
    activeCompactWords (tabList (S.round t).jobs.count (fun i => f (S.child t i))) (S.round t).indices =
      tabList (S.round (t+1)).jobs.count (fun i => f (S.child (t+1) i)) := by
  let l := activeChildren S.count (S.states t)
  let l' := activeChildren S.count (S.states (t+1))
  let idx := (S.round t).indices
  change activeCompactWords (tabList l.length (fun i => f (l.getD i 0))) idx =
    tabList l'.length (fun i => f (l'.getD i 0))
  rw [tabList_map_getD,tabList_map_getD]
  have he := modelGameJobs_indices S.base.core S.base.M S.base.r S.base.childSize S.count
    S.offset S.childAddr (S.states t)
  have hAct := activeChildren_gameRound S.base.route S.base.host S.base.verts S.base.Δ
    S.base.L S.base.core S.base.M S.base.r S.base.childSize S.count S.offset (S.states t)
  change l' = _ at hAct
  change idx.map (fun i => l.getD i 0) = _ at he
  rw [← hAct] at he
  rw [← he, List.map_map]
  unfold activeCompactWords
  apply List.map_congr_left
  intro i hi
  have hil : i < l.length := (mem_batchJobIndices.mp hi).1
  rw [List.getD_eq_getElem _ _ (by simpa using hil),List.getElem_map,Function.comp_apply,List.getD_eq_getElem _ _ hil]

/-- A schedule's active lookup has no repeated original child number. -/
theorem BuildGameSchedule.child_injective (S : BuildGameSchedule) (t : ℕ)
    {i j : ℕ} (hi : i < (S.round t).jobs.count) (hj : j < (S.round t).jobs.count)
    (he : S.child t i = S.child t j) : i = j := by
  let l := activeChildren S.count (S.states t)
  have hnd : l.Nodup := List.nodup_range.filter _
  have hi' : i < l.length := hi
  have hj' : j < l.length := hj
  change l.getD i 0 = l.getD j 0 at he
  rw [List.getD_eq_getElem _ _ hi',List.getD_eq_getElem _ _ hj'] at he
  exact (hnd.getElem_inj_iff).mp he

/-- The two table sizes are bounded by the number of original children. -/
theorem BuildGameSchedule.count_le (S : BuildGameSchedule) (t : ℕ) :
    (S.round t).jobs.count ≤ S.count := by
  change (activeChildren S.count (S.states t)).length ≤ S.count
  simpa [activeChildren] using
    List.length_filter_le (fun c => (S.states t c).saved.isNone) (List.range S.count)

end MinCostFlow.HierPaths
