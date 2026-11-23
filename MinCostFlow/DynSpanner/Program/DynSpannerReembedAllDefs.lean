module

public import MinCostFlow.DynSpanner.Program.DynSpannerReembed
public import MinCostFlow.DynSpanner.Program.DynGraphOps

/-!
# Re-embedding all affected edges: program and contract

Algorithm 6 (line 85) gives every affected edge `e` the new walk `Π_j(e) = reembedWalk e`. The
procedure `dsReembedAllStmt` gets the affected edges as a list `es` in memory, and at the same
positions pointers to the walks `embLt e = Π_{<j}(e)` and `embMid e`. For each edge it reads the
ends of `e`, calls `dsReembedEdgeStmt` with output at the current heap pointer and scratch just
after the output area, and stores the pointer to the new walk in an edge-indexed table (the
pointer table of level `j`). The heap pointer then moves past the written walk.

The heap area has `reembHeapNeed embLt embMid es = Σ (14 · |embLt e| + 4 · |embMid e| + 15)`
words: per edge an output area of `4 · |embLt e| + 2 · |embMid e| + 5` words and a scratch area
of `10 · |embLt e| + 2 · |embMid e| + 10` words.

The proof is in `DynSpannerReembedAll.lean`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-- Loop body of `dsReembedAllStmt` for the edge at position `reg 8`. -/
def dsReembedAllBodyStmt (bOps bRe : ℕ) : Stmt :=
  .assign 9 (.load (.bin .add (.reg 2) (.reg 8))) ;;
  .assign 10 (.load (.bin .add (.reg 4) (.reg 8))) ;;
  .assign 11 (.load (.bin .add (.reg 5) (.reg 8))) ;;
  .call 12 (bOps + dgIdxGetTail) [.reg 0, .reg 9] ;;
  .call 13 (bOps + dgIdxGetHead) [.reg 0, .reg 9] ;;
  .assign 14 (.load (.reg 10)) ;;
  .assign 15 (.load (.reg 11)) ;;
  .assign 16 (.bin .add (.reg 7) (.bin .add (.bin .add (.bin .mul (.const 4) (.reg 14))
    (.bin .mul (.const 2) (.reg 15))) (.const 5))) ;;
  .call 17 (bRe + reembedIdxEdge)
    [.reg 0, .reg 12, .reg 13, .reg 10, .reg 11, .reg 1, .reg 16, .reg 7] ;;
  .store (.bin .add (.reg 6) (.reg 9)) (.reg 7) ;;
  .assign 7 (.reg 17)

/-- Re-embed all edges of a list
(`args = [gPtr, sBitPtr, esPtr, esLen, wpPtr, mpPtr, piTab, heap]`); returns the final heap
pointer. -/
def dsReembedAllStmt (bOps bRe : ℕ) : Stmt :=
  forRange 8 (.const 0) (.reg 3) (dsReembedAllBodyStmt bOps bRe) ;;
  .ret (.reg 7)

/-- The procedures of the module. -/
def reembedAllProcs (bOps bRe : ℕ) : List Stmt :=
  [dsReembedAllStmt bOps bRe]

def reembedAllIdx : ℕ := 0

lemma reembedAllProcs_noRand (bOps bRe : ℕ) : ∀ s ∈ reembedAllProcs bOps bRe, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- Heap words needed by `dsReembedAllStmt`. -/
def reembHeapNeed (embLt embMid : Embedding) (es : List ℕ) : ℕ :=
  (es.map fun e => 14 * (embLt e).length + 4 * (embMid e).length + 15).sum

/-- Words written to the heap for edge `e`: the walk `reembedWalk e`. -/
def reembOutLen (G : MGraph) (embLt embMid : Embedding) (S : Finset ℕ) (e : ℕ) : ℕ :=
  2 * (reembedWalk G G embLt embMid S e).length + 1

/-- Heap pointer after the first `i` edges. -/
def reembHeapAt (G : MGraph) (embLt embMid : Embedding) (S : Finset ℕ) (es : List ℕ)
    (heap i : ℕ) : ℕ :=
  heap + ((es.take i).map (reembOutLen G embLt embMid S)).sum

/-- Total cost bound of `dsReembedAllStmt`. -/
def reembedAllCost (embLt embMid : Embedding) (es : List ℕ) : ℕ :=
  (es.map fun e => 800 * ((embLt e).length + (embMid e).length) + 1100).sum + 20

/-- Contract of `dsReembedAllStmt`. The walk `embLt es[k]` is at `mem (wpPtr + k)` and the walk
`embMid es[k]` at `mem (mpPtr + k)`. On return the table at `piTab` points, for each `e ∈ es`, to
`reembedWalk G G embLt embMid S e` in the heap. -/
def dsReembedAllContract (w vCap eCap : ℕ) (G : MGraph) (embLt embMid : Embedding)
    (S : Finset ℕ) (es : List ℕ) : Contract where
  pre args mem := ∃ gPtr sBitPtr esPtr wpPtr mpPtr piTab heap,
    args = [gPtr, sBitPtr, esPtr, es.length, wpPtr, mpPtr, piTab, heap] ∧ 16 ≤ 2 ^ w ∧
    gPtr + dynGraphSize vCap eCap < 2 ^ w ∧ sBitPtr + vCap < 2 ^ w ∧
    esPtr + es.length < 2 ^ w ∧ wpPtr + es.length < 2 ^ w ∧ mpPtr + es.length < 2 ^ w ∧
    piTab + eCap < 2 ^ w ∧ heap + reembHeapNeed embLt embMid es < 2 ^ w ∧
    IvlDisj heap (reembHeapNeed embLt embMid es) gPtr (dynGraphSize vCap eCap) ∧
    IvlDisj heap (reembHeapNeed embLt embMid es) sBitPtr vCap ∧
    IvlDisj heap (reembHeapNeed embLt embMid es) esPtr es.length ∧
    IvlDisj heap (reembHeapNeed embLt embMid es) wpPtr es.length ∧
    IvlDisj heap (reembHeapNeed embLt embMid es) mpPtr es.length ∧
    IvlDisj heap (reembHeapNeed embLt embMid es) piTab eCap ∧
    IvlDisj piTab eCap gPtr (dynGraphSize vCap eCap) ∧
    IvlDisj piTab eCap sBitPtr vCap ∧
    IvlDisj piTab eCap esPtr es.length ∧
    IvlDisj piTab eCap wpPtr es.length ∧
    IvlDisj piTab eCap mpPtr es.length ∧
    (∀ k (hk : k < es.length),
      MWalkAt mem (mem (wpPtr + k)) (embLt es[k]) ∧
      mem (wpPtr + k) + (2 * (embLt es[k]).length + 1) < 2 ^ w ∧
      IvlDisj heap (reembHeapNeed embLt embMid es) (mem (wpPtr + k))
        (2 * (embLt es[k]).length + 1) ∧
      IvlDisj piTab eCap (mem (wpPtr + k)) (2 * (embLt es[k]).length + 1) ∧
      MWalkAt mem (mem (mpPtr + k)) (embMid es[k]) ∧
      mem (mpPtr + k) + (2 * (embMid es[k]).length + 1) < 2 ^ w ∧
      IvlDisj heap (reembHeapNeed embLt embMid es) (mem (mpPtr + k))
        (2 * (embMid es[k]).length + 1) ∧
      IvlDisj piTab eCap (mem (mpPtr + k)) (2 * (embMid es[k]).length + 1)) ∧
    DynGraphAt mem gPtr vCap eCap G ∧ G.IsValid ∧ (∀ v ∈ G.V, v < vCap) ∧
    (∀ e ∈ G.E, e < eCap) ∧
    ListAt mem esPtr es ∧ es.Nodup ∧ (∀ e ∈ es, e ∈ G.E) ∧
    (∀ e ∈ es, PrefixWalksValid G S eCap (G.tail e) (G.head e) (embLt e)) ∧
    (∀ e ∈ es, ∀ x ∈ embMid e, x.1 < eCap) ∧
    (∀ v < vCap, mem (sBitPtr + v) = if v ∈ S then 1 else 0)
  post args mem ret mem' := ∃ gPtr sBitPtr esPtr wpPtr mpPtr piTab heap,
    args = [gPtr, sBitPtr, esPtr, es.length, wpPtr, mpPtr, piTab, heap] ∧
    (∀ e ∈ es, heap ≤ mem' (piTab + e) ∧
      mem' (piTab + e) + reembOutLen G embLt embMid S e ≤ ret ∧
      MWalkAt mem' (mem' (piTab + e)) (reembedWalk G G embLt embMid S e)) ∧
    ret = reembHeapAt G embLt embMid S es heap es.length ∧
    ∀ addr, (addr < heap ∨ heap + reembHeapNeed embLt embMid es ≤ addr) →
      (∀ e ∈ es, addr ≠ piTab + e) → mem' addr = mem addr
  cost _ _ := reembedAllCost embLt embMid es

end

end MinCostFlow.DynSpanner.Program
