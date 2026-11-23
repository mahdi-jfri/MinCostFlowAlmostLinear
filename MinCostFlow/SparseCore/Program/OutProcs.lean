module

public import MinCostFlow.SparseCore.Program.OutStepSmallProof
public import MinCostFlow.SparseCore.Program.OutSmallSide
public import MinCostFlow.SparseCore.Program.OutReset

/-!
# Where the procedures of the output piece sit

The three statements of piece P7 (`sig_outSmallSide_runs`, `sig_outReset_runs` and
`sig_outStepSmall_runs`) take a predicate `HasOutProcs p b nm sm fm lm` that says where the
procedures sit in the program `p`: the block of the piece at `b`, the tour operations at
`nm sm fm lm`. This file fixes that block (`outProcs`) and proves the three statements for it.

The block has twenty procedures. The first five are those of the piece: the helper, the reset,
the step and the two small procedures of the step. Then come the procedures of the stored graph
that the reset and the step call: the edge procedures (`dgEdgeProcs`), the basic operations
(`dgOpsProcs`), the split procedures (`dgSplitProcs`) and the batch procedures (`dgBatchProcs`),
which hold `dgApplyUpdate`.

| offset | procedures |
|---|---|
| 0 | `outSmallSideBody` |
| 1 | `outResetBody` |
| 2 | `outStepBody` |
| 3, 4 | `outFilterBody`, `outWalkBody` |
| 5, 6 | `dgEdgeProcs` |
| 7 to 13 | `dgOpsProcs` (`dgGetDeg` at 13) |
| 14 to 16 | `dgSplitProcs` |
| 17 to 19 | `dgBatchProcs` (`dgApplyUpdate` at 17) |
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner.Program

/-- The five procedures of the piece, for the block at `b`. -/
def outMainProcs (b nm sm fm lm : ℕ) : List Stmt :=
  [outSmallSideBody nm fm lm, outResetBody sm (b + 5),
    outStepBody nm sm fm (b + 17 + dgIdxApplyUpdate) (b + 7 + dgIdxGetDeg) (b + 3) (b + 4),
    outFilterBody, outWalkBody]

/-- The block of the piece at `b`: its five procedures, then the stored-graph procedures. -/
def outProcs (b nm sm fm lm : ℕ) : List Stmt :=
  outMainProcs b nm sm fm lm ++ dgEdgeProcs (b + 7) ++ dgOpsProcs ++ dgSplitProcs (b + 7) (b + 14) ++
    dgBatchProcs (b + 7) (b + 5) (b + 14) (b + 17)

theorem outProcs_length (b nm sm fm lm : ℕ) : (outProcs b nm sm fm lm).length = 20 := rfl

/-- The program holds the block of the piece at `b`. -/
def OutProcsAt (p : Program) (b nm sm fm lm : ℕ) : Prop := p.HasAt b (outProcs b nm sm fm lm)

/-- The index of the helper. -/
def outIdxSmallSide (b : ℕ) : ℕ := b

/-- The index of the reset. -/
def outIdxReset (b : ℕ) : ℕ := b + 1

/-- The index of the step. -/
def outIdxStep (b : ℕ) : ℕ := b + 2

private theorem outHasAt_left {p : Program} {b : ℕ} {l₁ l₂ : List Stmt}
    (h : p.HasAt b (l₁ ++ l₂)) : p.HasAt b l₁ := by
  intro i hi
  have := h i (by simp only [List.length_append]; omega)
  rwa [List.getElem_append_left hi] at this

private theorem outHasAt_right {p : Program} {b : ℕ} {l₁ l₂ : List Stmt}
    (h : p.HasAt b (l₁ ++ l₂)) : p.HasAt (b + l₁.length) l₂ := by
  intro i hi
  have := h (l₁.length + i) (by simp only [List.length_append]; omega)
  rw [List.getElem_append_right (by omega)] at this
  simpa [Nat.add_assoc] using this

/-- The parts of the block. -/
theorem OutProcsAt.parts {p : Program} {b nm sm fm lm : ℕ} (h : OutProcsAt p b nm sm fm lm) :
    p.HasAt b (outMainProcs b nm sm fm lm) ∧ p.HasAt (b + 5) (dgEdgeProcs (b + 7)) ∧
      p.HasAt (b + 7) dgOpsProcs ∧ p.HasAt (b + 14) (dgSplitProcs (b + 7) (b + 14)) ∧
      p.HasAt (b + 17) (dgBatchProcs (b + 7) (b + 5) (b + 14) (b + 17)) := by
  unfold OutProcsAt outProcs at h
  have h4 := outHasAt_right h
  have h3 := outHasAt_left h
  have h3r := outHasAt_right h3
  have h2 := outHasAt_left h3
  have h2r := outHasAt_right h2
  have h1 := outHasAt_left h2
  have h1r := outHasAt_right h1
  have h0 := outHasAt_left h1
  exact ⟨h0, h1r, h2r, h3r, h4⟩

/-- The five procedures of the piece, one by one. -/
theorem OutProcsAt.main {p : Program} {b nm sm fm lm : ℕ} (h : OutProcsAt p b nm sm fm lm) :
    p.procs[b]? = some (outSmallSideBody nm fm lm) ∧
      p.procs[b + 1]? = some (outResetBody sm (b + 5)) ∧
      p.procs[b + 2]? = some (outStepBody nm sm fm (b + 17 + dgIdxApplyUpdate)
        (b + 7 + dgIdxGetDeg) (b + 3) (b + 4)) ∧
      p.procs[b + 3]? = some outFilterBody ∧ p.procs[b + 4]? = some outWalkBody := by
  have hm := h.parts.1
  have h0 := hm.get (i := 0) (by simp [outMainProcs])
  have h1 := hm.get (i := 1) (by simp [outMainProcs])
  have h2 := hm.get (i := 2) (by simp [outMainProcs])
  have h3 := hm.get (i := 3) (by simp [outMainProcs])
  have h4 := hm.get (i := 4) (by simp [outMainProcs])
  exact ⟨h0, h1, h2, h3, h4⟩

/-- **The helper** meets its statement for this block. -/
theorem sig_outSmallSide_runs_outProcs : sig_outSmallSide_runs OutProcsAt outIdxSmallSide :=
  sig_outSmallSide_runs_of OutProcsAt outIdxSmallSide fun _ _ _ _ _ _ h => h.main.1

/-- **The reset** meets its statement for this block. -/
theorem sig_outReset_runs_outProcs : sig_outReset_runs OutProcsAt outIdxReset :=
  sig_outReset_runs_of OutProcsAt outIdxReset (fun b => b + 5) (fun b => b + 7)
    fun _ _ _ _ _ _ h => ⟨h.main.2.1, h.parts.2.1, h.parts.2.2.1⟩

/-- **The step** meets its statement for this block. -/
theorem sig_outStepSmall_runs_outProcs : sig_outStepSmall_runs OutProcsAt outIdxStep :=
  sig_outStepSmall_runs_of OutProcsAt outIdxStep (fun b => b + 17 + dgIdxApplyUpdate)
    (fun b => b + 7 + dgIdxGetDeg) (fun b => b + 3) (fun b => b + 4)
    fun _ _ _ _ _ _ h => by
      obtain ⟨-, hE, hO, hS, hB⟩ := h.parts
      exact ⟨h.main.2.2.1, fun _ _ _ _ _ _ _ => dgApplyUpdate_meetsContract hB hE hS hO,
        fun _ _ _ _ => dgGetDeg_meetsContract hO, h.main.2.2.2.1, h.main.2.2.2.2⟩

end MinCostFlow.SparseCore.Program
