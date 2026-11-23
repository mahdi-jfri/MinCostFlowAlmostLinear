module

public import MinCostFlow.DynSpanner.Program.DynSpannerProjDefs
public import MinCostFlow.DynSpanner.Program.DynGraphEdges
public import MinCostFlow.DynSpanner.Program.StateLayout

/-!
# Building the projected graph `J`: program and contract

Algorithm 6 (lines 70–77) builds the graph `J` on the projected endpoints: for each affected edge
`e`, the edge `(â, b̂) = proj_{j-1}(e)` with the same name `e`, together with its embedding walk
`projWalk e`. The model is `buildProjGraph G' H_{<j} Π_{<j} S_{j-1} E_aff`.

The procedure `dsBuildProjStmt` gets the affected edges as a list `es` in memory and, at the same
positions, pointers to their walks `embLt e`. For each edge it reads the ends of `e`, calls
`dsProjEdgeStmt` with output at the current heap pointer and scratch just after that output, adds
`â` and `b̂` to `J`, inserts the edge `e = (â, b̂)` and stores the pointer to `projWalk e` in an
edge-indexed table. The heap pointer then moves past the written walk. The heap area that the
caller provides has `projHeapNeed embLt es = Σ (14 · |embLt e| + 15)` words, enough for all
outputs and the last scratch area.

The proof is in `DynSpannerBuildProj.lean`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-- Loop body of `dsBuildProjStmt` for the edge at position `reg 8`. -/
def dsBuildProjBodyStmt (bOps bEdge bProj : ℕ) : Stmt :=
  .assign 9 (.load (.bin .add (.reg 3) (.reg 8))) ;;
  .assign 10 (.load (.bin .add (.reg 5) (.reg 8))) ;;
  .call 11 (bOps + dgIdxGetTail) [.reg 0, .reg 9] ;;
  .call 12 (bOps + dgIdxGetHead) [.reg 0, .reg 9] ;;
  .assign 13 (.load (.reg 10)) ;;
  .assign 14 (.bin .add (.reg 7) (.bin .add (.bin .mul (.const 4) (.reg 13)) (.const 5))) ;;
  .call 15 (bProj + projIdxEdge)
    [.reg 0, .reg 9, .reg 11, .reg 12, .reg 10, .reg 2, .reg 14, .reg 7] ;;
  .assign 16 (.load (.reg 7)) ;;
  .assign 17 (.load (.bin .add (.reg 7) (.const 1))) ;;
  .call 18 (bOps + dgIdxAddVertex) [.reg 1, .reg 16] ;;
  .call 18 (bOps + dgIdxAddVertex) [.reg 1, .reg 17] ;;
  .call 18 (bEdge + dgIdxInsertEdge) [.reg 1, .reg 9, .reg 16, .reg 17] ;;
  .store (.bin .add (.reg 6) (.reg 9)) (.bin .add (.reg 7) (.const 2)) ;;
  .assign 7 (.reg 15)

/-- Build `J` and its embedding table
(`args = [gPtr, jPtr, sBitPtr, esPtr, esLen, wpPtr, embTab, heap]`); returns the final heap
pointer. -/
def dsBuildProjStmt (bOps bEdge bProj : ℕ) : Stmt :=
  forRange 8 (.const 0) (.reg 4) (dsBuildProjBodyStmt bOps bEdge bProj) ;;
  .ret (.reg 7)

/-- The procedures of the module. -/
def buildProjProcs (bOps bEdge bProj : ℕ) : List Stmt :=
  [dsBuildProjStmt bOps bEdge bProj]

def buildProjIdx : ℕ := 0

lemma buildProjProcs_noRand (bOps bEdge bProj : ℕ) :
    ∀ s ∈ buildProjProcs bOps bEdge bProj, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- Heap words needed by `dsBuildProjStmt`: `14 · |embLt e| + 15` per edge. -/
def projHeapNeed (embLt : Embedding) (es : List ℕ) : ℕ :=
  (es.map fun e => 14 * (embLt e).length + 15).sum

/-- Words written to the heap for edge `e`: `â`, `b̂` and the walk `projWalk e`. -/
def projOutLen (G : MGraph) (embLt : Embedding) (S : Finset ℕ) (e : ℕ) : ℕ :=
  2 + (2 * (projWalk G G embLt S e).length + 1)

/-- Heap pointer after the first `i` edges. -/
def projHeapAt (G : MGraph) (embLt : Embedding) (S : Finset ℕ) (es : List ℕ) (heap i : ℕ) : ℕ :=
  heap + ((es.take i).map (projOutLen G embLt S)).sum

/-- Total cost bound of `dsBuildProjStmt`: `800 · |embLt e| + 2000` per edge. -/
def buildProjCost (embLt : Embedding) (es : List ℕ) : ℕ :=
  (es.map fun e => 800 * (embLt e).length + 2000).sum + 20

/-- Contract of `dsBuildProjStmt`. The walk of `es[k]` is stored at `mem (wpPtr + k)`. `J` starts
empty at `jPtr`. On return `J` is `buildProjGraph G G embLt S es.toFinset`, and the table at
`embTab` points, for each `e ∈ es`, to `projWalk G G embLt S e` in the heap. -/
def dsBuildProjContract (w vCap eCap : ℕ) (G : MGraph) (embLt : Embedding) (S : Finset ℕ)
    (es : List ℕ) : Contract where
  pre args mem := ∃ gPtr jPtr sBitPtr esPtr wpPtr embTab heap,
    args = [gPtr, jPtr, sBitPtr, esPtr, es.length, wpPtr, embTab, heap] ∧ 16 ≤ 2 ^ w ∧
    gPtr + dynGraphSize vCap eCap < 2 ^ w ∧ jPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    sBitPtr + vCap < 2 ^ w ∧ esPtr + es.length < 2 ^ w ∧ wpPtr + es.length < 2 ^ w ∧
    embTab + eCap < 2 ^ w ∧ heap + projHeapNeed embLt es < 2 ^ w ∧
    IvlDisj heap (projHeapNeed embLt es) gPtr (dynGraphSize vCap eCap) ∧
    IvlDisj heap (projHeapNeed embLt es) jPtr (dynGraphSize vCap eCap) ∧
    IvlDisj heap (projHeapNeed embLt es) sBitPtr vCap ∧
    IvlDisj heap (projHeapNeed embLt es) esPtr es.length ∧
    IvlDisj heap (projHeapNeed embLt es) wpPtr es.length ∧
    IvlDisj heap (projHeapNeed embLt es) embTab eCap ∧
    IvlDisj jPtr (dynGraphSize vCap eCap) gPtr (dynGraphSize vCap eCap) ∧
    IvlDisj jPtr (dynGraphSize vCap eCap) sBitPtr vCap ∧
    IvlDisj jPtr (dynGraphSize vCap eCap) esPtr es.length ∧
    IvlDisj jPtr (dynGraphSize vCap eCap) wpPtr es.length ∧
    IvlDisj jPtr (dynGraphSize vCap eCap) embTab eCap ∧
    IvlDisj embTab eCap gPtr (dynGraphSize vCap eCap) ∧
    IvlDisj embTab eCap sBitPtr vCap ∧
    IvlDisj embTab eCap esPtr es.length ∧
    IvlDisj embTab eCap wpPtr es.length ∧
    (∀ k (hk : k < es.length),
      MWalkAt mem (mem (wpPtr + k)) (embLt es[k]) ∧
      mem (wpPtr + k) + (2 * (embLt es[k]).length + 1) < 2 ^ w ∧
      IvlDisj heap (projHeapNeed embLt es) (mem (wpPtr + k)) (2 * (embLt es[k]).length + 1) ∧
      IvlDisj jPtr (dynGraphSize vCap eCap) (mem (wpPtr + k)) (2 * (embLt es[k]).length + 1) ∧
      IvlDisj embTab eCap (mem (wpPtr + k)) (2 * (embLt es[k]).length + 1)) ∧
    DynGraphAt mem gPtr vCap eCap G ∧ G.IsValid ∧ (∀ v ∈ G.V, v < vCap) ∧
    (∀ e ∈ G.E, e < eCap) ∧
    DynGraphAt mem jPtr vCap eCap emptyMGraph ∧
    ListAt mem esPtr es ∧ es.Nodup ∧ (∀ e ∈ es, e ∈ G.E) ∧
    (∀ e ∈ es, PrefixWalksValid G S eCap (G.tail e) (G.head e) (embLt e)) ∧
    (∀ v < vCap, mem (sBitPtr + v) = if v ∈ S then 1 else 0)
  post args mem ret mem' := ∃ gPtr jPtr sBitPtr esPtr wpPtr embTab heap,
    args = [gPtr, jPtr, sBitPtr, esPtr, es.length, wpPtr, embTab, heap] ∧
    DynGraphAt mem' jPtr vCap eCap (buildProjGraph G G embLt S es.toFinset) ∧
    (∀ e ∈ es, heap ≤ mem' (embTab + e) ∧
      mem' (embTab + e) + (2 * (projWalk G G embLt S e).length + 1) ≤ ret ∧
      MWalkAt mem' (mem' (embTab + e)) (projWalk G G embLt S e)) ∧
    ret = projHeapAt G embLt S es heap es.length ∧
    ∀ addr, (addr < heap ∨ heap + projHeapNeed embLt es ≤ addr) →
      (addr < jPtr ∨ jPtr + dynGraphSize vCap eCap ≤ addr) →
      (∀ e ∈ es, addr ≠ embTab + e) → mem' addr = mem addr
  cost _ _ := buildProjCost embLt es

end

end MinCostFlow.DynSpanner.Program
