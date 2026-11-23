module

public import MinCostFlow.Final.AssemblyDryRunSCDeepSelectCode
public import MinCostFlow.MinRatio.WireUpdateSelect
import MinCostFlow.DynSpanner.Program.DynGraphBatch
import MinCostFlow.DynSpanner.Program.DynGraphDelete
import MinCostFlow.MinRatio.SelectUpdateG0One
import MinCostFlow.MinRatio.SelectNonRebuiltOps
import MinCostFlow.MinRatio.SelectUpdateNonRebuilt
import MinCostFlow.MinRatio.SelectUpdateLevelNoRoom
import Mathlib.Tactic

/-!
# Concrete select-aware `ordChainCore` block (`AssemblyDryRunSCCoreSelectCode`)

Packages the deterministic select-aware chain-update wrapper `ordChainUpdateCoreSelBody`
(`MinRatio/WireUpdateSelect.lean`), an arbitrary relocatable inner chain-update core block
`innerCoreCode : SolverInnerSubCode` (meeting `OrdChainUpdateCoreSpecWExtKFBL`), and the complete
103-procedure deterministic post-core select-maintenance block (`selectUpdatePostCoreBody` and all
its helper procedures and self-contained sub-modules: `dgRefillModule`, `dgSplitProcs`,
`dgBatchProcs`, `selectHeapOpsModule`, `selectPhiFillModule`, `evalKeyModule`) into a relocatable
deterministic `SolverInnerSubCode` block `dryCoreSelectCode innerCoreCode`:

* `dryCoreSelectPostLen := 103`, `dryCoreSelectCodeLen`, `dryCoreSelectProcs`,
  `dryCoreSelectCode`: the relocatable `SolverInnerSubCode` block (`off = 0`).
* `dryCoreSelectCode_hasAll`: extracts every procedure entry, the inner core placement at
  `lay.ordChainCore + 1`, and all sub-module placements inside `dryLinkedProgramSel`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Concrete relocatable `SolverInnerSubCode` block `dryCoreSelectCode` -/

/-- Fixed length (`103`) of the post-core select-maintenance block inside `dryCoreSelectProcs`. -/
def dryCoreSelectPostLen : ℕ := 103

/-- Total length (`1 + innerCoreCode.len + 103`) of `dryCoreSelectProcs innerCoreCode`. -/
def dryCoreSelectCodeLen (innerCoreCode : SolverInnerSubCode) : ℕ :=
  1 + innerCoreCode.len + dryCoreSelectPostLen

/-- Relocatable 103-procedure deterministic post-core select-maintenance block placed at `c`,
calling sparse-core ops `env.scOp` and fixed-point ops `env.opsBase`. -/
def dryCoreSelectPostProcs (env : SolverInnerEnv) (c : ℕ) : List Stmt :=
  let ops := env.opsBase
  let bDg := c + 32
  let bSplit := c + 44
  let bBatch := c + 47
  let bHeap := c + 50
  let bPhi := c + 72
  let bEval := c + 89
  [selectUpdatePostCoreBody (c + 1) (c + 3) (c + 7) (c + 13) (c + 16) (c + 22),
   selTableWriteBody (c + 2),
   selTableRowBody,
   selUpdateG0Body (c + 4) (c + 6),
   selCopyG0OneBody (bHeap + 12) (c + 5),
   selNegCopyToBody,
   selFilterPresentBody,
   selectUpdateFPhiLenLoopBody (c + 7) (c + 8),
   selectUpdateFPhiLenLevelBody (bBatch + dgIdxApplyBatch) (c + 9) (c + 10) (c + 6) (c + 11),
   dgDeleteEdgeListBody (bDg + 7 + dgIdxDeleteEdge),
   selBatchCopySplitsBody (bHeap + 12),
   selCoreLenFillBody (c + 12),
   selCoreLenEdgeBody (ops + 20) (c + 31),
   selectUpdateEmbLoopBody (c + 13) (c + 14),
   selectUpdateEmbLevelBody (env.scOp 4) (c + 15),
   selEmbUpdateFromListBody (c + 6) (c + 20) (c + 21),
   selectUpdateSuffixBlocksBody (c + 17) (env.scOp 3) (c + 19) (c + 30),
   selectInitInteriorLoopBody (c + 17) (c + 18),
   selectFillInteriorLevelBody (env.scOp 2) (env.scOp 4) (c + 29) (c + 11) (c + 20) (c + 21),
   selectFillLastLevelBody (c + 29) (c + 11),
   selFilterAbsentBody,
   selEmbCopyBody (bHeap + 12),
   selectUpdateHeapPhaseBody (c + 23) (c + 25),
   selectUpdateHeapPrefixLoopBody (c + 23) (c + 24),
   selectUpdateLevelBody (c + 27),
   selectRebuildSuffixBody (c + 25) (c + 26),
   selectRebuildLevelBody (bHeap + 21) (c + 27),
   selectProcessListBody (c + 27) (c + 28),
   selectProcessEdgeBody bEval (bHeap + 18) (bHeap + 20),
   dgCopyRefillBody (bDg + 11),
   selectPhiLoopBody (c + 30) (bPhi + 16),
   wireCoreLenEdgeBody (ops + 17) (ops + 11) (ops + 22) ops] ++
  (dgRefillModule bDg ++
  (dgSplitProcs bDg bSplit ++
  (dgBatchProcs bDg (bDg + 7) bSplit bBatch ++
  (selectHeapOpsModule bHeap 4 ++
  (selectPhiFillModule bPhi 4 ++
   evalKeyModule bEval 4)))))

/-- Concrete relocatable deterministic block placed at `env.innerBase` implementing
`ordChainUpdateCoreSelBody` (offset `0`), `innerCoreCode` (offsets `1 .. innerCoreCode.len`),
and `dryCoreSelectPostProcs` (offsets `1 + innerCoreCode.len .. 1 + innerCoreCode.len + 102`). -/
def dryCoreSelectProcs (innerCoreCode : SolverInnerSubCode) (env : SolverInnerEnv) : List Stmt :=
  let b := env.innerBase
  let c := b + 1 + innerCoreCode.len
  [ordChainUpdateCoreSelBody (b + 1 + innerCoreCode.off) c] ++
    (innerCoreCode.procs { env with innerBase := b + 1 } ++
     dryCoreSelectPostProcs env c)

theorem dryCoreSelectPostProcs_length (env : SolverInnerEnv) (c : ℕ) :
    (dryCoreSelectPostProcs env c).length = dryCoreSelectPostLen := by
  unfold dryCoreSelectPostProcs dryCoreSelectPostLen
  simp only [List.length_append, List.length_cons, List.length_nil,
    dgRefillModule_length, dgSplitProcs_length, dgBatchProcs_length,
    selectHeapOpsModule_length, selectPhiFillModule_length, evalKeyModule_length]

theorem dryCoreSelectProcs_length (innerCoreCode : SolverInnerSubCode) (env : SolverInnerEnv) :
    (dryCoreSelectProcs innerCoreCode env).length = dryCoreSelectCodeLen innerCoreCode := by
  unfold dryCoreSelectProcs dryCoreSelectCodeLen
  simp only [List.length_append, List.length_cons, List.length_nil,
    innerCoreCode.hlen, dryCoreSelectPostProcs_length]
  omega

theorem dryCoreSelectPostProcs_noRand (env : SolverInnerEnv) (c : ℕ) :
    ∀ s ∈ dryCoreSelectPostProcs env c, s.NoRand := by
  intro s hs
  unfold dryCoreSelectPostProcs at hs
  simp only [List.mem_append] at hs
  rcases hs with hWrap | hDgRef | hSplit | hBatch | hHeap | hPhi | hEval
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hWrap
    rcases hWrap with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · exact selectUpdatePostCoreBody_noRand ..
    · exact selTableWriteBody_noRand _
    · exact selTableRowBody_noRand
    · exact selUpdateG0Body_noRand ..
    · exact selCopyG0OneBody_noRand ..
    · exact selNegCopyToBody_noRand
    · exact selFilterPresentBody_noRand
    · exact selectUpdateFPhiLenLoopBody_noRand ..
    · exact selectUpdateFPhiLenLevelBody_noRand ..
    · exact dgDeleteEdgeListBody_noRand _
    · exact selBatchCopySplitsBody_noRand _
    · exact selCoreLenFillBody_noRand _
    · exact selCoreLenEdgeBody_noRand ..
    · exact selectUpdateEmbLoopBody_noRand ..
    · exact selectUpdateEmbLevelBody_noRand ..
    · exact selEmbUpdateFromListBody_noRand ..
    · exact selectUpdateSuffixBlocksBody_noRand ..
    · exact selectInitInteriorLoopBody_noRand ..
    · exact selectFillInteriorLevelBody_noRand ..
    · exact selectFillLastLevelBody_noRand ..
    · exact selFilterAbsentBody_noRand
    · exact selEmbCopyBody_noRand _
    · exact selectUpdateHeapPhaseBody_noRand ..
    · exact selectUpdateHeapPrefixLoopBody_noRand ..
    · exact selectUpdateLevelBody_noRand _
    · exact selectRebuildSuffixBody_noRand ..
    · exact selectRebuildLevelBody_noRand ..
    · exact selectProcessListBody_noRand ..
    · exact selectProcessEdgeBody_noRand ..
    · exact dgCopyRefillBody_noRand _
    · exact selectPhiLoopBody_noRand ..
    · exact wireCoreLenEdgeBody_noRand ..
  · exact dgRefillModule_noRand _ s hDgRef
  · exact dgSplitProcs_noRand _ _ s hSplit
  · exact dgBatchProcs_noRand _ _ _ _ s hBatch
  · exact selectHeapOpsModule_noRand _ _ s hHeap
  · exact selectPhiFillModule_noRand _ _ s hPhi
  · exact evalKeyModule_noRand _ _ s hEval

theorem dryCoreSelectProcs_noRand (innerCoreCode : SolverInnerSubCode) (env : SolverInnerEnv) :
    ∀ s ∈ dryCoreSelectProcs innerCoreCode env, s.NoRand := by
  intro s hs
  unfold dryCoreSelectProcs at hs
  simp only [List.mem_append] at hs
  rcases hs with hEntry | hIn | hPost
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hEntry
    subst hEntry
    exact ordChainUpdateCoreSelBody_noRand ..
  · exact innerCoreCode.hnoRand _ s hIn
  · exact dryCoreSelectPostProcs_noRand env _ s hPost

/-- Relocatable deterministic `SolverInnerSubCode` for select-aware `Update`
(`ordChainUpdateCoreSelBody` at offset `0`, wrapping `innerCoreCode` at offset `1`). -/
def dryCoreSelectCode (innerCoreCode : SolverInnerSubCode) : SolverInnerSubCode where
  procs := dryCoreSelectProcs innerCoreCode
  len := dryCoreSelectCodeLen innerCoreCode
  hlen := dryCoreSelectProcs_length innerCoreCode
  hnoRand := dryCoreSelectProcs_noRand innerCoreCode
  off := 0

end MinCostFlow.Final.DryRun

end

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 2. Procedure placement inside `dryLinkedProgramSel` -/

private theorem hasAt_peel_cs {p : Program} {b b' : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) (hlen : b + xs.length = b') :
    p.HasAt b xs ∧ p.HasAt b' ys :=
  ⟨Num.hasAt_append_left h, hlen ▸ Num.hasAt_append_right h⟩

/-- Extracts `dgOpsProcs` and `dgEdgeProcs bDg` from `dgRefillModule bDg`. -/
theorem dgRefillModule_hasOpsEdge {p : Program} {bDg : ℕ}
    (h : p.HasAt bDg (dgRefillModule bDg)) :
    p.HasAt bDg dgOpsProcs ∧ p.HasAt (bDg + 7) (dgEdgeProcs bDg) := by
  unfold dgRefillModule at h
  have h1 : p.HasAt bDg (dgOpsProcs ++ dgEdgeProcs bDg) := Num.hasAt_append_left h
  exact ⟨Num.hasAt_append_left h1, Num.hasAt_append_right h1⟩

/-- Extracts every procedure entry, the inner core placement at `lay.ordChainCore + 1`, and all
sub-module placements of `dryCoreSelectCode innerCoreCode` at `lay.ordChainCore` inside
`dryLinkedProgramSel`. -/
theorem dryCoreSelectCode_hasAll (Psc : DrySparseCorePieces)
    (initCode innerCoreCode selectCode termCode deepCode selInitCode : SolverInnerSubCode) :
    let inner := dryInnerCodeSel initCode (dryCoreSelectCode innerCoreCode) selectCode termCode deepCode
    let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
    let lay := dryTailLay Psc.sc inner
    let b := lay.ordChainCore
    let c := b + 1 + innerCoreCode.len
    let ops := mrdsCycleBase
    let bDg := c + 32
    let bSplit := c + 44
    let bBatch := c + 47
    let bHeap := c + 50
    let bPhi := c + 72
    let bEval := c + 89
    let env := solverTailInnerEnv mrdsCycleBase lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst
      Psc.sc solverTailBase
    p.procs[b]? = some (ordChainUpdateCoreSelBody (b + 1 + innerCoreCode.off) c) ∧
    p.HasAt (b + 1) (innerCoreCode.procs { env with innerBase := b + 1 }) ∧
    p.procs[c]? = some (selectUpdatePostCoreBody (c + 1) (c + 3) (c + 7) (c + 13) (c + 16) (c + 22)) ∧
    p.procs[c + 1]? = some (selTableWriteBody (c + 2)) ∧
    p.procs[c + 2]? = some selTableRowBody ∧
    p.procs[c + 3]? = some (selUpdateG0Body (c + 4) (c + 6)) ∧
    p.procs[c + 4]? = some (selCopyG0OneBody (bHeap + 12) (c + 5)) ∧
    p.procs[c + 5]? = some selNegCopyToBody ∧
    p.procs[c + 6]? = some selFilterPresentBody ∧
    p.procs[c + 7]? = some (selectUpdateFPhiLenLoopBody (c + 7) (c + 8)) ∧
    p.procs[c + 8]? = some (selectUpdateFPhiLenLevelBody (bBatch + dgIdxApplyBatch) (c + 9)
      (c + 10) (c + 6) (c + 11)) ∧
    p.procs[c + 9]? = some (dgDeleteEdgeListBody (bDg + 7 + dgIdxDeleteEdge)) ∧
    p.procs[c + 10]? = some (selBatchCopySplitsBody (bHeap + 12)) ∧
    p.procs[c + 11]? = some (selCoreLenFillBody (c + 12)) ∧
    p.procs[c + 12]? = some (selCoreLenEdgeBody (ops + 20) (c + 31)) ∧
    p.procs[c + 13]? = some (selectUpdateEmbLoopBody (c + 13) (c + 14)) ∧
    p.procs[c + 14]? = some (selectUpdateEmbLevelBody (lay.scOp 4) (c + 15)) ∧
    p.procs[c + 15]? = some (selEmbUpdateFromListBody (c + 6) (c + 20) (c + 21)) ∧
    p.procs[c + 16]? = some (selectUpdateSuffixBlocksBody (c + 17) (lay.scOp 3) (c + 19) (c + 30)) ∧
    p.procs[c + 17]? = some (selectInitInteriorLoopBody (c + 17) (c + 18)) ∧
    p.procs[c + 18]? = some (selectFillInteriorLevelBody (lay.scOp 2) (lay.scOp 4) (c + 29)
      (c + 11) (c + 20) (c + 21)) ∧
    p.procs[c + 19]? = some (selectFillLastLevelBody (c + 29) (c + 11)) ∧
    p.procs[c + 20]? = some selFilterAbsentBody ∧
    p.procs[c + 21]? = some (selEmbCopyBody (bHeap + 12)) ∧
    p.procs[c + 22]? = some (selectUpdateHeapPhaseBody (c + 23) (c + 25)) ∧
    p.procs[c + 23]? = some (selectUpdateHeapPrefixLoopBody (c + 23) (c + 24)) ∧
    p.procs[c + 24]? = some (selectUpdateLevelBody (c + 27)) ∧
    p.procs[c + 25]? = some (selectRebuildSuffixBody (c + 25) (c + 26)) ∧
    p.procs[c + 26]? = some (selectRebuildLevelBody (bHeap + 21) (c + 27)) ∧
    p.procs[c + 27]? = some (selectProcessListBody (c + 27) (c + 28)) ∧
    p.procs[c + 28]? = some (selectProcessEdgeBody bEval (bHeap + 18) (bHeap + 20)) ∧
    p.procs[c + 29]? = some (dgCopyRefillBody (bDg + 11)) ∧
    p.procs[c + 30]? = some (selectPhiLoopBody (c + 30) (bPhi + 16)) ∧
    p.procs[c + 31]? = some (wireCoreLenEdgeBody (ops + 17) (ops + 11) (ops + 22) ops) ∧
    p.HasAt bDg (dgRefillModule bDg) ∧
    p.HasAt bSplit (dgSplitProcs bDg bSplit) ∧
    p.HasAt bBatch (dgBatchProcs bDg (bDg + 7) bSplit bBatch) ∧
    p.HasAt bHeap (selectHeapOpsModule bHeap 4) ∧
    p.HasAt bPhi (selectPhiFillModule bPhi 4) ∧
    p.HasAt bEval (evalKeyModule bEval 4) := by
  intro inner p lay b c ops bDg bSplit bBatch bHeap bPhi bEval env
  have hInner := dryLinkedProgramSel_inner_hasAt dryWitnessUsed Psc.sc inner selInitCode
  have hInner' : p.HasAt env.innerBase (inner.procs env) := hInner
  unfold inner dryInnerCodeSel at hInner'
  dsimp only at hInner'
  obtain ⟨_, r1⟩ := hasAt_peel_cs (b' := env.innerBase + 1) hInner' (by simp)
  obtain ⟨_, r2⟩ := hasAt_peel_cs (b' := env.innerBase + 1 + initCode.len) r1
    (by simp [initCode.hlen])
  have hAtRaw : p.HasAt (env.innerBase + 1 + initCode.len)
      (dryCoreSelectProcs innerCoreCode { env with innerBase := env.innerBase + 1 + initCode.len }) :=
    Num.hasAt_append_left r2
  have hbEq : env.innerBase + 1 + initCode.len = b := by
    dsimp only [b, lay, inner, dryTailLay, solverTailLayout, dryInnerCodeSel, dryCoreSelectCode,
      env, solverTailInnerEnv]
    omega
  have hAt : p.HasAt b (dryCoreSelectProcs innerCoreCode { env with innerBase := b }) := by
    rw [hbEq] at hAtRaw
    exact hAtRaw
  unfold dryCoreSelectProcs at hAt
  obtain ⟨hEntry, s1⟩ := hasAt_peel_cs (b' := b + 1) hAt (by simp)
  obtain ⟨hInCore, hPost⟩ := hasAt_peel_cs (b' := c) s1
    (by rw [innerCoreCode.hlen])
  unfold dryCoreSelectPostProcs at hPost
  obtain ⟨hWrap, t1⟩ := hasAt_peel_cs (b' := bDg) hPost (by simp [bDg])
  obtain ⟨hDgRef, t2⟩ := hasAt_peel_cs (b' := bSplit) t1 (by rw [dgRefillModule_length])
  obtain ⟨hSplit, t3⟩ := hasAt_peel_cs (b' := bBatch) t2 (by rw [dgSplitProcs_length])
  obtain ⟨hBatch, t4⟩ := hasAt_peel_cs (b' := bHeap) t3 (by rw [dgBatchProcs_length])
  obtain ⟨hHeap, t5⟩ := hasAt_peel_cs (b' := bPhi) t4 (by rw [selectHeapOpsModule_length])
  obtain ⟨hPhi, hEval⟩ := hasAt_peel_cs (b' := bEval) t5 (by rw [selectPhiFillModule_length])
  have hScOp : ∀ j, env.scOp j = lay.scOp j := fun _ => rfl
  have hOpsEq : env.opsBase = ops := rfl
  have hWrapGet (i : ℕ) (hi : i < 32) := hWrap.get (i := i) (by simpa using hi)
  refine ⟨?_, hInCore, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hDgRef, hSplit, hBatch, hHeap, hPhi, hEval⟩
  · simpa using hEntry.get (i := 0) (by simp)
  · simpa using hWrapGet 0 (by omega)
  · simpa using hWrapGet 1 (by omega)
  · simpa using hWrapGet 2 (by omega)
  · simpa using hWrapGet 3 (by omega)
  · simpa using hWrapGet 4 (by omega)
  · simpa using hWrapGet 5 (by omega)
  · simpa using hWrapGet 6 (by omega)
  · simpa using hWrapGet 7 (by omega)
  · simpa using hWrapGet 8 (by omega)
  · simpa using hWrapGet 9 (by omega)
  · simpa using hWrapGet 10 (by omega)
  · simpa using hWrapGet 11 (by omega)
  · simpa [hOpsEq] using hWrapGet 12 (by omega)
  · simpa using hWrapGet 13 (by omega)
  · simpa [hScOp] using hWrapGet 14 (by omega)
  · simpa using hWrapGet 15 (by omega)
  · simpa [hScOp] using hWrapGet 16 (by omega)
  · simpa using hWrapGet 17 (by omega)
  · simpa [hScOp] using hWrapGet 18 (by omega)
  · simpa using hWrapGet 19 (by omega)
  · simpa using hWrapGet 20 (by omega)
  · simpa using hWrapGet 21 (by omega)
  · simpa using hWrapGet 22 (by omega)
  · simpa using hWrapGet 23 (by omega)
  · simpa using hWrapGet 24 (by omega)
  · simpa using hWrapGet 25 (by omega)
  · simpa using hWrapGet 26 (by omega)
  · simpa using hWrapGet 27 (by omega)
  · simpa using hWrapGet 28 (by omega)
  · simpa using hWrapGet 29 (by omega)
  · simpa using hWrapGet 30 (by omega)
  · simpa [hOpsEq] using hWrapGet 31 (by omega)

end MinCostFlow.Final.DryRun

end
