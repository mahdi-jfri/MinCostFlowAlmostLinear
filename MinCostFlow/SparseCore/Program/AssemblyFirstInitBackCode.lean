module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitRootTbl
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitS0
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitMark
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitEmbRun
public import MinCostFlow.SparseCore.Program.ReadMain

/-!
# The procedure blocks for the back of the build (`AssemblyFirstInitBackCode`)

The back of the build of a branch at its init (`asmFirstInitBackStmt`, `AssemblyFirstInitBody.lean`)
runs four procedures: the table of roots (`rootTblBody`), the output graph `S₀`
(`asmFirstInitS0Body`), the marks of `S₀` on the tour (`asmFirstInitMarkBody`), and the embedding
table (`asmFirstInitEmbBody`).

For `S₀`, P10's rebuild asks for the root of each endpoint through a `RootQueryAt`. P4's root
query may write into P4's cells below the build's heap pointer, so the build answers root queries
from its own table of roots (`rootTblQuery`). This file packs `S₀` together with `rootTblQueryBody`
and its own copy of `readRestartProcs` into one contiguous six-procedure module
`asmFirstInitS0Module`, and packs all twelve procedures of the back into `asmFirstInitBackModule`.
It also extracts `initGraphFromExportContract` from P10's `readBranchProcs` at offset `15`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Read MinCostFlow.SparseCore.Program.Restart

/-! ## The `S₀` module with its own `readRestartProcs` and `rootTblQueryBody` -/

/-- **The `S₀` module** at base `b` (6 procedures):
* `b + 0`: `asmFirstInitS0Body (bBatch + dgIdxInitFromLists) (b + 2 + readRestartIdxMain)`
* `b + 1`: `rootTblQueryBody`
* `b + 2 .. b + 5`: `readRestartProcs bOps bEdge bLoop (b + 1) (b + 2)`. -/
def asmFirstInitS0Module (bOps bEdge bBatch bLoop b : ℕ) : List Stmt :=
  asmFirstInitS0Body (bBatch + dgIdxInitFromLists) (b + 2 + readRestartIdxMain) ::
  rootTblQueryBody ::
  readRestartProcs bOps bEdge bLoop (b + 1) (b + 2)

theorem asmFirstInitS0Module_length (bOps bEdge bBatch bLoop b : ℕ) :
    (asmFirstInitS0Module bOps bEdge bBatch bLoop b).length = 6 := rfl

/-- The `S₀` module never reads random bits. -/
theorem asmFirstInitS0Module_noRand (bOps bEdge bBatch bLoop b : ℕ) :
    ∀ s ∈ asmFirstInitS0Module bOps bEdge bBatch bLoop b, s.NoRand := by
  intro s hs
  simp only [asmFirstInitS0Module, List.mem_cons] at hs
  rcases hs with rfl | rfl | hs
  · exact asmFirstInitS0Body_noRand _ _
  · exact rootTblQueryBody_noRand
  · exact readRestartProcs_noRand bOps bEdge bLoop (b + 1) (b + 2) s hs

/-- Placement of the three parts of `asmFirstInitS0Module` when placed at `b`. -/
theorem asmFirstInitS0Module_hasAt {p : Program} {bOps bEdge bBatch bLoop b : ℕ}
    (h : p.HasAt b (asmFirstInitS0Module bOps bEdge bBatch bLoop b)) :
    p.procs[b]? =
      some (asmFirstInitS0Body (bBatch + dgIdxInitFromLists) (b + 2 + readRestartIdxMain)) ∧
    p.procs[b + 1]? = some rootTblQueryBody ∧
    p.HasAt (b + 2) (readRestartProcs bOps bEdge bLoop (b + 1) (b + 2)) := by
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · simpa [asmFirstInitS0Module] using h 0 (by simp [asmFirstInitS0Module])
  · simpa [asmFirstInitS0Module] using h 1 (by simp [asmFirstInitS0Module])
  · have h2 := h (i + 2) (by simp only [asmFirstInitS0Module, List.length_cons]; omega)
    rw [show b + (i + 2) = b + 2 + i by omega] at h2
    simpa [asmFirstInitS0Module] using h2

/-! ## The full 12-procedure module of the back -/

private theorem hasAt_append_left {p : Program} {b : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) : p.HasAt b xs := fun i hi => by
  have h1 := h i (by simp only [List.length_append]; omega)
  rwa [List.getElem_append_left hi] at h1

private theorem hasAt_append_right {p : Program} {b : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) : p.HasAt (b + xs.length) ys := fun i hi => by
  have h1 := h (xs.length + i) (by simp only [List.length_append]; omega)
  rw [← Nat.add_assoc] at h1
  simpa only [List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] using h1

/-- **The procedure block of the back** at base `b` (12 procedures):
* `b + 0`: `rootTblBody (bRead + 15) bComp` (`fRootTbl`)
* `b + 1 .. b + 6`: `asmFirstInitS0Module L.ops L.edge L.batch L.loops (b + 1)` (`fS0`)
* `b + 7`: `asmFirstInitMarkBody fExp (b + 8)` (`fMark`)
* `b + 8`: `tourMarkExportStmt (tourOp bTour 7)`
* `b + 9`: `asmFirstInitEmbBody (b + 10) (b + 11)` (`fEmb`)
* `b + 10`: `asmFirstInitEmbTblBody`
* `b + 11`: `embRefreshStmt L.copy (bSpan + bsOffRead + spanReadIdxPiWalkPtr)`. -/
def asmFirstInitBackModule (L : ReadLib) (bRead bSpan bTour bComp fExp b : ℕ) : List Stmt :=
  [rootTblBody (bRead + 15) bComp] ++
  asmFirstInitS0Module L.ops L.edge L.batch L.loops (b + 1) ++
  [asmFirstInitMarkBody fExp (b + 8),
   tourMarkExportStmt (tourOp bTour 7),
   asmFirstInitEmbBody (b + 10) (b + 11),
   asmFirstInitEmbTblBody,
   embRefreshStmt L.copy (bSpan + bsOffRead + spanReadIdxPiWalkPtr)]

theorem asmFirstInitBackModule_length (L : ReadLib) (bRead bSpan bTour bComp fExp b : ℕ) :
    (asmFirstInitBackModule L bRead bSpan bTour bComp fExp b).length = 12 := rfl

/-- The back module never reads random bits. -/
theorem asmFirstInitBackModule_noRand (L : ReadLib) (bRead bSpan bTour bComp fExp b : ℕ) :
    ∀ s ∈ asmFirstInitBackModule L bRead bSpan bTour bComp fExp b, s.NoRand := by
  intro s hs
  simp only [asmFirstInitBackModule, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hs
  rcases hs with (rfl | hS0) | rfl | rfl | rfl | rfl | rfl
  · exact rootTblBody_noRand _ _
  · exact asmFirstInitS0Module_noRand L.ops L.edge L.batch L.loops (b + 1) s hS0
  · exact asmFirstInitMarkBody_noRand _ _
  · exact tourMarkExportStmt_noRand _
  · exact asmFirstInitEmbBody_noRand _ _
  · exact asmFirstInitEmbTblBody_noRand
  · exact embRefreshStmt_noRand _ _

/-- Placement of every procedure of `asmFirstInitBackModule` when placed at `b`. -/
theorem asmFirstInitBackModule_hasAt {p : Program} {L : ReadLib}
    {bRead bSpan bTour bComp fExp b : ℕ}
    (h : p.HasAt b (asmFirstInitBackModule L bRead bSpan bTour bComp fExp b)) :
    p.procs[b]? = some (rootTblBody (bRead + 15) bComp) ∧
    p.HasAt (b + 1) (asmFirstInitS0Module L.ops L.edge L.batch L.loops (b + 1)) ∧
    p.procs[b + 7]? = some (asmFirstInitMarkBody fExp (b + 8)) ∧
    p.procs[b + 8]? = some (tourMarkExportStmt (tourOp bTour 7)) ∧
    p.procs[b + 9]? = some (asmFirstInitEmbBody (b + 10) (b + 11)) ∧
    p.procs[b + 10]? = some asmFirstInitEmbTblBody ∧
    p.procs[b + 11]? =
      some (embRefreshStmt L.copy (bSpan + bsOffRead + spanReadIdxPiWalkPtr)) := by
  dsimp only [asmFirstInitBackModule] at h
  have h1 := hasAt_append_left h
  have hTail := hasAt_append_right h
  have hRoot := hasAt_append_left h1
  have hS0 := hasAt_append_right h1
  simp only [List.length_append, List.length_cons, List.length_nil,
    asmFirstInitS0Module_length] at hS0 hTail
  refine ⟨?_, hS0, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hRoot 0 (by simp)
  · simpa using hTail 0 (by simp)
  · simpa [Nat.add_assoc] using hTail 1 (by simp)
  · simpa [Nat.add_assoc] using hTail 2 (by simp)
  · simpa [Nat.add_assoc] using hTail 3 (by simp)
  · simpa [Nat.add_assoc] using hTail 4 (by simp)

/-! ## `initGraphFromExportContract` from `readBranchProcs` -/

/-- P10's `readBranchProcs` placed at `bRead` provides `initGraphFromExportContract` at
`bRead + 15`. -/
theorem initGraphFromExport_meetsContract_of_readBranch {w vCap eCap : ℕ} {p : Program}
    {L : ReadLib} {fRoot bRead : ℕ} {G : MGraph}
    (hL : L.Has p) (hp : p.HasAt bRead (readBranchProcs L fRoot bRead)) :
    MeetsContract w p (bRead + 15) (initGraphFromExportContract w vCap eCap G) := by
  dsimp only [readBranchProcs] at hp
  have hInit := hasAt_append_right hp
  simp only [List.length_append, List.length_cons, List.length_nil,
    readStepProcs, readRestartProcs, readInitOpsProcs] at hInit
  simpa [readInitIdxGraph] using
    initGraphFromExport_meetsContract (w := w) (vCap := vCap) (eCap := eCap) (G := G)
      hInit hL.2.2.2.1 hL.2.1 hL.1

end MinCostFlow.SparseCore.Program
