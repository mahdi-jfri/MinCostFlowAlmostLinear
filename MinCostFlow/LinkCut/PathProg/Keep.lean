module

public import MinCostFlow.LinkCut.PathProg.Rep
public import MinCostFlow.LinkCut.PathProg.Vals
public import MinCostFlow.LinkCut.PathTree.AccOps

/-!
# The operations keep `StateOk`

Each operation keeps the facts of `StateOk`, with the index stack that the machine leaves:
pointers stay in range (`PtrOk`), the model invariant holds, every ready root is on the stack
(`readyIdx_step`, from the root lemmas of `PathTree/Acc`), free slots keep their shape, and only
edges hold values (`PathProg/Vals`).

This file treats the expose, the reroot, and the path summary.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree

theorem active_le {s : PathTreeState} {trees : List AuxTree} {free : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload s trees free depth) {v : ℕ}
    (hv : v ∈ trees.flatMap AuxTree.toList) : v ≤ 2 * s.n := by
  have := (W.activeValid v hv).2; omega

/-- An expose of an active node keeps `StateOk`, with the nodes it notes added to the stack. -/
theorem stateOk_expose {s : PathTreeState} {S : List ℕ} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} (W : LctInvWith pathPayload s trees free depth)
    (hI : ReadyIdx s trees S) (hF : FreeShape s free) (hP : PtrOk (2 * s.n) s.splay)
    (hE : ValsOnEdges s) {v : ℕ} (hv : v ∈ trees.flatMap AuxTree.toList) :
    StateOk (lctExpose pathPayload s v) (exposeNotes pathPayload s v S) := by
  obtain ⟨tv, htv, hvt⟩ := List.mem_flatMap.mp hv
  obtain ⟨trees', Lv, -, W', hperm, -⟩ := lctExpose_spec pathPayload_laws W htv hvt
  obtain ⟨hacc, hkeep⟩ := lctExpose_rootAcc pathPayload_laws W htv hvt S
  refine ⟨?_, ⟨trees', free, depth, W', ?_, freeShape_keep W hF hkeep⟩, vals_expose W hE hv⟩
  · rw [lctExpose_n]; exact hP.expose (active_le W hv)
  · exact readyIdx_step W W' hacc (fun z hz => Or.inl (hperm.subset hz)) hI
      (subset_exposeNotes _ _ _ _) (fun _ h => h)

/-- A reroot at a vertex keeps `StateOk`. -/
theorem stateOk_reroot {s : PathTreeState} {S : List ℕ} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} (W : LctInvWith pathPayload s trees free depth)
    (hI : ReadyIdx s trees S) (hF : FreeShape s free) (hP : PtrOk (2 * s.n) s.splay)
    (hE : ValsOnEdges s) {v : ℕ} (hv : isVertex s.n v) :
    ∃ trees' depth', LctInvWith pathPayload (lctReroot pathPayload s v) trees' free depth' ∧
      (trees'.flatMap AuxTree.toList).Perm (trees.flatMap AuxTree.toList) ∧
      ReadyIdx (lctReroot pathPayload s v) trees' (exposeNotes pathPayload s v S) ∧
      FreeShape (lctReroot pathPayload s v) free ∧
      PtrOk (2 * (lctReroot pathPayload s v).n) (lctReroot pathPayload s v).splay ∧
      ValsOnEdges (lctReroot pathPayload s v) := by
  have hva := isVertex_mem_active W hv
  obtain ⟨tv, htv, hvt⟩ := List.mem_flatMap.mp hva
  obtain ⟨trees', L, d', -, W', hperm, -⟩ := lctReroot_spec pathPayload_laws W htv hvt hv
  obtain ⟨hacc, hkeep⟩ := lctReroot_rootAcc pathPayload_laws W htv hvt S
  refine ⟨trees', d', W', hperm, ?_, freeShape_keep W hF hkeep, ?_, vals_reroot W hE hv⟩
  · exact readyIdx_step W W' hacc (fun z hz => Or.inl (hperm.subset hz)) hI
      (subset_exposeNotes _ _ _ _) (fun _ h => h)
  · rw [lctReroot_n]; exact hP.reroot (active_le W hva)

/-- A reroot at a vertex followed by an expose of a vertex keeps `StateOk`. -/
theorem stateOk_summary {s : PathTreeState} {S : List ℕ} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} (W : LctInvWith pathPayload s trees free depth)
    (hI : ReadyIdx s trees S) (hF : FreeShape s free) (hP : PtrOk (2 * s.n) s.splay)
    (hE : ValsOnEdges s) {u v : ℕ} (hu : isVertex s.n u) (hv : isVertex s.n v) :
    StateOk (lctPathSummary pathPayload s u v).1 (rerootExposeNotes pathPayload s u v S) := by
  obtain ⟨trees', d', W', hperm, hI', hF', hP', hE'⟩ := stateOk_reroot W hI hF hP hE hu
  have hv' : v ∈ trees'.flatMap AuxTree.toList :=
    hperm.symm.subset (isVertex_mem_active W hv)
  rw [lctPathSummary_fst]
  exact stateOk_expose W' hI' hF' hP' hE' hv'

end MinCostFlow.LinkCut.PathProg
