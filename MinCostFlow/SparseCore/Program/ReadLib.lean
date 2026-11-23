module

public import MinCostFlow.SparseCore.Program.ReadCollect
public import MinCostFlow.SparseCore.Program.ReadLoops
public import MinCostFlow.DynSpanner.Program.DynGraphBatch
public import MinCostFlow.LSF.Program.BatchTBlockOpsBase
public import WordRAM.CopyWords
import MinCostFlow.SparseCore.Program.ReadTree

/-!
# The procedures that the update of the readout data calls

The update of the readout data of a branch calls procedures of other libraries: the graph library
(`dgOpsProcs`, `dgEdgeProcs`, `dgSplitProcs`, `dgBatchProcs`), the edge listing `collectStmt`,
`copyWords`, the stretch writer `lsfSetWstrOneProc` and the two list loops of `ReadLoops.lean`.
`ReadLib` names where they are in the program, and `ReadLib.Has` says that they are there. The
lemmas `ReadLib.Has.*` give their contracts.

Two facts on lists of edges close the file: a list of distinct names below `cap` has at most `cap`
entries (`length_le_of_nodup_lt`), and the two lists of the edges with tail and with head at a
vertex have together the degree of the vertex (`tails_add_heads_eq_deg`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.LSF.Program

/-- Where the procedures that the update calls are in the program. -/
structure ReadLib where
  ops : ℕ
  edge : ℕ
  split : ℕ
  batch : ℕ
  collect : ℕ
  copy : ℕ
  setOne : ℕ
  loops : ℕ

/-- The program `p` has the procedures of `L`. -/
def ReadLib.Has (p : Program) (L : ReadLib) : Prop :=
  p.HasAt L.ops dgOpsProcs ∧ p.HasAt L.edge (dgEdgeProcs L.ops) ∧
  p.HasAt L.split (dgSplitProcs L.ops L.split) ∧
  p.HasAt L.batch (dgBatchProcs L.ops L.edge L.split L.batch) ∧
  p.procs[L.collect]? = some collectStmt ∧ p.HasAt L.copy [copyWords] ∧
  p.procs[L.setOne]? = some lsfSetWstrOneProc ∧ p.HasAt L.loops (readLoopProcs L.edge)

namespace ReadLib.Has

variable {p : Program} {L : ReadLib} (h : L.Has p) {w : ℕ}
include h

theorem getDeg (vCap eCap : ℕ) (G : MGraph) :
    MeetsContract w p (L.ops + dgIdxGetDeg) (dgGetDegContract w vCap eCap G) :=
  dgGetDeg_meetsContract h.1

theorem getTail (vCap eCap : ℕ) (G : MGraph) :
    MeetsContract w p (L.ops + dgIdxGetTail) (dgGetTailContract w vCap eCap G) :=
  dgGetTail_meetsContract h.1

theorem getHead (vCap eCap : ℕ) (G : MGraph) :
    MeetsContract w p (L.ops + dgIdxGetHead) (dgGetHeadContract w vCap eCap G) :=
  dgGetHead_meetsContract h.1

theorem addVertex (vCap eCap : ℕ) (G : MGraph) :
    MeetsContract w p (L.ops + dgIdxAddVertex) (dgAddVertexContract w vCap eCap G) :=
  dgAddVertex_meetsContract h.1

theorem insertEdge (vCap eCap : ℕ) (G : MGraph) :
    MeetsContract w p (L.edge + dgIdxInsertEdge) (dgInsertEdgeContract w vCap eCap G) :=
  dgInsertEdge_meetsContract h.2.1 h.1

theorem applySplit (vCap eCap : ℕ) (H : MGraph) (St Sh : Finset ℕ) (Lt Lh : List ℕ) :
    MeetsContract w p (L.split + dgIdxApplySplit)
      (dgApplySplitContract w vCap eCap H St Sh Lt Lh) :=
  dgApplySplit_meetsContract h.2.2.1 h.1

theorem applyUpdate (vCap eCap : ℕ) (G H : MGraph) (u : Update) (len : ℕ) :
    MeetsContract w p (L.batch + dgIdxApplyUpdate) (dgApplyUpdateContract w vCap eCap G H u len) :=
  dgApplyUpdate_meetsContract h.2.2.2.1 h.2.1 h.2.2.1 h.1

theorem applyBatch (vCap eCap : ℕ) (G H : MGraph) (U : List Update) (words : ℕ) :
    MeetsContract w p (L.batch + dgIdxApplyBatch) (dgApplyBatchContract w vCap eCap G H U words) :=
  dgApplyBatch_meetsContract h.2.2.2.1 h.2.1 h.2.2.1 h.1

theorem collect (vCap eCap : ℕ) (G : MGraph) :
    MeetsContract w p L.collect (collectContract w vCap eCap G) :=
  collect_meetsContract h.2.2.2.2.1

theorem copy : MeetsContract w p L.copy (copyWordsContract w) :=
  copyWords_meetsContract h.2.2.2.2.2.1

theorem setOne : MeetsContract w p L.setOne (lsfSetWstrOneContract w 4) :=
  lsfSetWstrOne_meetsContract h.2.2.2.2.2.2.1

theorem delEdges (vCap eCap : ℕ) (G : MGraph) (l : List ℕ) :
    MeetsContract w p (L.loops + readIdxDelEdges) (delEdgesContract w vCap eCap G l) :=
  delEdges_meetsContract h.2.2.2.2.2.2.2 h.2.1 h.1

theorem setRoots (vCap : ℕ) (R : Finset ℕ) (l : List ℕ) :
    MeetsContract w p (L.loops + readIdxSetRoots) (setRootsContract w vCap R l) :=
  setRoots_meetsContract h.2.2.2.2.2.2.2

end ReadLib.Has

/-! ## Lists of edges -/

/-- A list of distinct names below `cap` has at most `cap` entries. -/
theorem length_le_of_nodup_lt {xs : List ℕ} {cap : ℕ} (hnd : xs.Nodup)
    (hlt : ∀ x ∈ xs, x < cap) : xs.length ≤ cap := by
  have hsub : xs.toFinset ⊆ Finset.range cap := fun x hx =>
    Finset.mem_range.mpr (hlt x (List.mem_toFinset.mp hx))
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Finset.card_range] at hcard
  exact hcard

/-- The list of the edges with tail at `x` and the list of the edges with head at `x`, each without
repeats, have together `deg x` entries. -/
theorem tails_add_heads_eq_deg {K : MGraph} {x : ℕ} {Lt Lh : List ℕ} (ht : Lt.Nodup)
    (hh : Lh.Nodup) (hLt : ∀ e, e ∈ Lt ↔ e ∈ K.E ∧ endAt K 0 e = x)
    (hLh : ∀ e, e ∈ Lh ↔ e ∈ K.E ∧ endAt K 1 e = x) : Lt.length + Lh.length = K.deg x := by
  unfold MGraph.deg
  rw [length_eq_card_of_mem_iff ht (S := K.E.filter fun e => K.tail e = x)
      (fun e => by rw [hLt, Finset.mem_filter]; simp [endAt]),
    length_eq_card_of_mem_iff hh (S := K.E.filter fun e => K.head e = x)
      (fun e => by rw [hLh, Finset.mem_filter]; simp [endAt])]

end MinCostFlow.SparseCore.Program.Read
