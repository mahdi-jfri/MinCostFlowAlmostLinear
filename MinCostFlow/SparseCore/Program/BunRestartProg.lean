module

public import MinCostFlow.SparseCore.Program.BunRestartModel
public import MinCostFlow.SparseCore.Program.BundleExportProcs
public import MinCostFlow.SparseCore.Program.OutStepProcs
public import MinCostFlow.DynSpanner.Program.SortOps

/-!
# The restart of the bundles: the program (`BunRestartProg`)

`bunRestartStmt`, called as `[tbl, tourH, n, slotsPtr, h]`, restarts the `n` slots listed at
`slotsPtr` of the bundle table at `tbl`. It keeps its heap arrays from `h` on:
the descriptors (`4 n` words at `h`), the specs `(s, 4 |E_s|)` (`2 n` words), and five arrays of
`2 E` words each, where `E` is the number of edges of the listed slots: the keys of their ends,
the pairs `(e, s)`, the owners of the keys, the scratch array of the sort, and the sorted owners
without repeats (`rList`). The heap pointer of the calls starts after them.

1. Loop A: copy the slots into the specs with `4 |E_s|` as block size, and add up `E`.
2. Loop B: walk the end list of every bundle of every listed slot (`outWalkBody`) into the keys.
3. Loop C: for an even key `2 e`, write the pair `(e, edgeSlot[e] - 1)`; for each key, ask the
   tour for its owner.
4. Loops D1, D2 (`brZeroBody`): clear `edgeSlot[e]` for the pairs and the slot pointers of the
   listed slots.
5. Sort the owners and drop repeats (`sortProcs`): this is `rList`.
6. Call `bundleInitSlotsStmt` on the specs, the pairs and `rList`.
7. Loop E: export the graph of each new slot (`bundleExportGraphStmt`) and copy its four header
   words to `h + 4 i`.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

@[expose] public section

/-- Loop A, round `r10`: the slot `s := slots[r10]`, its block `p := slotPtr[s]` and edge count
`nE := mem[p + 2]`; writes `(s, 4 nE)` at `specPtr + 2 r10` and adds `nE` to register `9`. -/
def brLoopABody : Stmt :=
  .assign 11 (.load (.bin .add (.reg 3) (.reg 10))) ;;
  .assign 12 (.load (.bin .add (.reg 5) (.reg 11))) ;;
  .assign 18 (.load (.bin .add (.reg 12) (.const 2))) ;;
  .store (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 10))) (.reg 11) ;;
  .store (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 10))) (.const 1))
    (.bin .mul (.const 4) (.reg 18)) ;;
  .assign 9 (.bin .add (.reg 9) (.reg 18))

/-- Loop B, inner round `r22`: walk the end list of bundle `r22` of the block at `r12` into the
keys, from position `r20` on, and advance `r20` by its length. -/
def brBundleBody (bWalk : ℕ) : Stmt :=
  .call 23 bWalk [.reg 7, .bin .add (.bin .add (.reg 12) (.const 3)) (.reg 22),
    .bin .add (.reg 13) (.reg 20)] ;;
  .assign 20 (.bin .add (.reg 20) (.reg 23))

/-- Loop B, round `r10`: the slot `s := specs[2 r10]`, its block `p`, its bundle count `nB`, and
the walk of all its bundles. -/
def brLoopBBody (bWalk : ℕ) : Stmt :=
  .assign 11 (.load (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 10)))) ;;
  .assign 12 (.load (.bin .add (.reg 5) (.reg 11))) ;;
  .assign 21 (.load (.bin .add (.reg 12) (.const 1))) ;;
  forRange 22 (.const 0) (.reg 21) (brBundleBody bWalk)

/-- Loop C, round `r10`, first part: the key `key := keys[r10]` (register `11`); for an even key,
the pair `(key / 2, edgeSlot[key / 2] - 1)` goes to position `r20` of the pairs. -/
def brLoopCPair : Stmt :=
  .assign 11 (.load (.bin .add (.reg 13) (.reg 10))) ;;
  .cond (.bin .eq (.bin .mod (.reg 11) (.const 2)) (.const 0))
    (.assign 21 (.bin .div (.reg 11) (.const 2)) ;;
     .assign 22 (.bin .sub (.load (.bin .add (.reg 6) (.reg 21))) (.const 1)) ;;
     .store (.bin .add (.reg 14) (.bin .mul (.const 2) (.reg 20))) (.reg 21) ;;
     .store (.bin .add (.bin .add (.reg 14) (.bin .mul (.const 2) (.reg 20))) (.const 1))
       (.reg 22) ;;
     .assign 20 (.bin .add (.reg 20) (.const 1)))
    .nop

/-- Loop C, round `r10`, second part: the owner of the key goes to `owners[r10]`, and the heap
pointer moves past the answer of the tour. -/
def brLoopCOwner (bOwner : ℕ) : Stmt :=
  .call 12 bOwner [.reg 1, .reg 11, .reg 19] ;;
  .store (.bin .add (.reg 15) (.reg 10)) (.load (.reg 19)) ;;
  .assign 19 (.reg 12)

/-- Loop C, round `r10`. -/
def brLoopCBody (bOwner : ℕ) : Stmt :=
  brLoopCPair ;; brLoopCOwner bOwner

/-- Loops D1 and D2, round `r10`: clear the word at `rDst + mem[rSrc + 2 r10]`. Loop D1 clears
`edgeSlot[e]` for the edge `e` of pair `r10` (`rSrc = 14`, `rDst = 6`); loop D2 clears the slot
pointer of the slot `specs[2 r10]` (`rSrc = 8`, `rDst = 5`). -/
def brZeroBody (rSrc rDst : ℕ) : Stmt :=
  .assign 11 (.load (.bin .add (.reg rSrc) (.bin .mul (.const 2) (.reg 10)))) ;;
  .store (.bin .add (.reg rDst) (.reg 11)) (.const 0)

/-- Loop E, round `r10`: export the graph of slot `specs[2 r10]` at the heap pointer and copy its
four header words to `h + 4 r10`. -/
def brLoopEBody (bExport : ℕ) : Stmt :=
  .assign 11 (.load (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 10)))) ;;
  .call 12 bExport [.reg 0, .reg 11, .reg 19] ;;
  .store (.bin .add (.reg 4) (.bin .mul (.const 4) (.reg 10))) (.load (.reg 19)) ;;
  .store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 4) (.reg 10))) (.const 1))
    (.load (.bin .add (.reg 19) (.const 1))) ;;
  .store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 4) (.reg 10))) (.const 2))
    (.load (.bin .add (.reg 19) (.const 2))) ;;
  .store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 4) (.reg 10))) (.const 3))
    (.load (.bin .add (.reg 19) (.const 3))) ;;
  .assign 19 (.reg 12)

/-- The start: the three bases of the table, the specs pointer `h + 4 n`, and `E := 0`. -/
def brStart : Stmt :=
  .assign 5 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const 4))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const 7))) ;;
  .assign 8 (.bin .add (.reg 4) (.bin .mul (.const 4) (.reg 2))) ;;
  .assign 9 (.const 0)

/-- The layout of the five arrays of `2 E` words after the specs, and the heap pointer. -/
def brLayout : Stmt :=
  .assign 13 (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 2))) ;;
  .assign 14 (.bin .add (.reg 13) (.bin .mul (.const 2) (.reg 9))) ;;
  .assign 15 (.bin .add (.reg 14) (.bin .mul (.const 2) (.reg 9))) ;;
  .assign 16 (.bin .add (.reg 15) (.bin .mul (.const 2) (.reg 9))) ;;
  .assign 17 (.bin .add (.reg 16) (.bin .mul (.const 2) (.reg 9))) ;;
  .assign 19 (.bin .add (.reg 17) (.bin .mul (.const 2) (.reg 9))) ;;
  .assign 20 (.const 0)

/-- The sort of the owners and the removal of repeats into `rList` (its length in register
`26`). -/
def brSortStmt (bSort : ℕ) : Stmt :=
  .call 21 (bSort + sortIdxMergeSort) [.reg 15, .bin .mul (.const 2) (.reg 9), .reg 16] ;;
  .call 26 (bSort + sortIdxDedup) [.reg 15, .bin .mul (.const 2) (.reg 9), .reg 17]

/-- The call of P5's initialization of slots (reads the bundle cap `k` from the table header). -/
def brInitStmt (bInit : ℕ) : Stmt :=
  .call 19 bInit [.reg 0, .reg 1, .reg 2, .reg 8, .reg 9, .reg 14, .reg 26, .reg 17, .reg 19]

/-- Phase A: the start, loop A and the layout. -/
def brPhaseA : Stmt :=
  brStart ;; forRange 10 (.const 0) (.reg 2) brLoopABody ;; brLayout

/-- Phase B: loop B, the walk of the end lists into the keys. -/
def brPhaseB (bWalk : ℕ) : Stmt :=
  forRange 10 (.const 0) (.reg 2) (brLoopBBody bWalk)

/-- Phase C: loop C, the owners of the keys and the pairs. -/
def brPhaseC (bOwner : ℕ) : Stmt :=
  .assign 20 (.const 0) ;;
  forRange 10 (.const 0) (.bin .mul (.const 2) (.reg 9)) (brLoopCBody bOwner)

/-- Phase D: loops D1 and D2, which clear the listed slots in the table. -/
def brPhaseD : Stmt :=
  forRange 10 (.const 0) (.reg 9) (brZeroBody 14 6) ;;
  forRange 10 (.const 0) (.reg 2) (brZeroBody 8 5)

/-- Phase E: loop E, the export of the new slots. -/
def brPhaseE (bExport : ℕ) : Stmt :=
  forRange 10 (.const 0) (.reg 2) (brLoopEBody bExport)

/-- **The restart of the bundles of the listed slots** (`[tbl, tourH, n, slotsPtr, h]`), with the
list walk at `bWalk`, the owner query of the tour at `bOwner`, the sort procedures at `bSort`,
P5's initialization of slots at `bInit` and P5's export at `bExport`. The bundle cap `k` is read at
run time from the table block (`btBunCapAddr`). -/
def bunRestartStmt (bWalk bOwner bSort bInit bExport : ℕ) : Stmt :=
  brPhaseA ;; brPhaseB bWalk ;; brPhaseC bOwner ;; brPhaseD ;; brSortStmt bSort ;;
  brInitStmt bInit ;; brPhaseE bExport ;; .ret (.reg 19)

theorem bunRestartStmt_noRand (bWalk bOwner bSort bInit bExport : ℕ) :
    (bunRestartStmt bWalk bOwner bSort bInit bExport).NoRand := by
  simp [bunRestartStmt, brPhaseA, brPhaseB, brPhaseC, brPhaseD, brPhaseE, brStart, brLayout,
    brLoopABody, brLoopBBody, brBundleBody, brLoopCBody, brLoopCPair, brLoopCOwner, brZeroBody,
    brSortStmt, brInitStmt, brLoopEBody, forRange, forUp, Stmt.NoRand]

/-- The contract of the list walk `outWalkBody` (`[nb, head, dst]`, `outWalk_runs`): it copies the
doubly linked list `L` at `head` to `dst` and returns its length. -/
def brWalkContract (w prevB nb head dst cap : ℕ) (L : List ℕ) : Contract where
  pre args mem := args = [nb, head, dst] ∧ IsDoublyLinkedList mem prevB nb head cap L ∧
    (∀ x ∈ L, nb + x + 1 < 2 ^ w) ∧ dst + L.length < 2 ^ w ∧ 2 < 2 ^ w ∧
    (∀ j < L.length, head ≠ dst + j) ∧ (∀ x ∈ L, ∀ j < L.length, nb + x ≠ dst + j)
  post _ mem ret mem' := ret = L.length ∧ ListAt mem' dst L ∧
    ∀ a, ¬ (dst ≤ a ∧ a < dst + L.length) → mem' a = mem a
  cost _ _ := 30 * (L.length + 1)

end

public section

/-- The list walk meets its contract. -/
theorem brWalk_meetsContract {w prevB nb head dst cap : ℕ} {L : List ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some outWalkBody) :
    MeetsContract w p b (brWalkContract w prevB nb head dst cap L) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  obtain ⟨rfl, hL, hw, hdst, h2w, hdh, hdnb⟩ := hpre
  obtain ⟨st', c, hrun, hlist, hfr, hc⟩ :=
    outWalk_runs (p := p) (ω := ω) mem pos hL hw hdst h2w hdh hdnb
  exact ⟨_, st', c, hrun, ⟨rfl, hlist, hfr⟩, hc⟩

end

end MinCostFlow.SparseCore.Program.Restart
