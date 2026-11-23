module

public import MinCostFlow.LSF.Program.CallSeq
public import MinCostFlow.LSF.Program.RootStage
public import MinCostFlow.LSF.Program.OrderStage
public import MinCostFlow.LSF.Program.TStage
public import MinCostFlow.LSF.Program.THStage
public import MinCostFlow.LSF.Program.T0Index

/-!
# The order phase of the initialization

After the `[AN19]` call, the tree `T₀` is in three index arrays. The order phase is a call
sequence (`callSeqStmt`) of five calls:
1. `rootStageProc`: root `T₀` at index `0`, copy the arrays into the aux block, fill the ancestor
   table;
2. `storeWordStmt`: set the parent edge of the root to `0`, so that every entry is an edge index;
3. `orderStageProc`: the end indices of the edges of `G₀`, the order `π`, the `upMin` table;
4. `tStageProc`: the `T` block;
5. `thStageProc`: the parents of `T_H` in the aux block, its depths in scratch.

`OrderLayout` names the places, and `OrderLayout.args` lists the arguments of the phase.
`orderPhaseItems` is the list of calls.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-- The places of the order phase. The root is index `0`. -/
structure OrderLayout where
  n : ℕ
  tM : ℕ
  tTail : ℕ
  tHead : ℕ
  rtOut : ℕ
  sPtr : ℕ
  auxPar : ℕ
  logCap : ℕ
  m0 : ℕ
  gPtr : ℕ
  vIdx : ℕ
  eu : ℕ
  ev : ℕ
  qPtr : ℕ
  Kq : ℕ
  dPtr : ℕ
  K : ℕ
  tmpPtr : ℕ
  arrPtr : ℕ
  scratchPtr : ℕ
  minPtr : ℕ
  tPtr : ℕ
  vCap : ℕ
  eCap : ℕ
  vListPtr : ℕ
  tOrigSrc : ℕ
  nOrig : ℕ
  thBase : ℕ
  thDst : ℕ

namespace OrderLayout

variable (X : OrderLayout)

/-- The top-down order `Q` that `rootStageProc` leaves in its scratch area. -/
def qOrd : ℕ := X.sPtr + X.n + 2 * X.tM + X.n

/-- The `41` arguments of the phase. -/
def args : List ℕ :=
  [X.n, X.tM, X.tTail, X.tHead, 0, X.rtOut, X.sPtr, X.auxPar, X.logCap,
    X.m0, dgEListBase X.gPtr X.vCap X.eCap, dgETailSlotBase X.gPtr X.vCap X.eCap,
    dgEHeadSlotBase X.gPtr X.vCap X.eCap, dgIntToExtBase X.gPtr X.vCap, X.vIdx, X.eu, X.ev,
    X.qPtr, X.Kq, X.dPtr, X.K, X.tmpPtr, X.auxPar + 3 * X.n, X.auxPar + X.n + X.n, X.qOrd,
    X.auxPar + X.n, X.arrPtr, X.scratchPtr, tPiBase X.tPtr X.vCap X.tM, X.minPtr,
    X.tPtr, X.vCap, X.eCap, X.vListPtr, X.tOrigSrc, X.nOrig, tOrigIdBase X.tPtr X.vCap X.tM,
    tDgTPtr X.tPtr, X.thBase, X.thDst, X.auxPar + X.n]

end OrderLayout

/-- The calls of the order phase. -/
def orderPhaseItems (w h : ℕ) (G₀ T₀ : MGraph) (vList eList : List ℕ)
    (bRoot bStore bOrder bT bTH : ℕ) : List CallItem :=
  [⟨bRoot, [0, 1, 2, 3, 4, 5, 6, 7, 8], rootStageContract w⟩,
   ⟨bStore, [40, 4], storeWordContract⟩,
   ⟨bOrder, [0, 4, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 8, 22, 23, 7, 24, 25, 26,
      27, 28, 29], orderStageContract w h G₀ vList eList⟩,
   ⟨bT, [30, 31, 32, 1, 33, 34, 2, 3, 0, 35, 36, 37], tStageContract w G₀ T₀ vList⟩,
   ⟨bTH, [0, 24, 7, 23, 38, 4, 39], thStageContract w T₀ vList⟩]

/-- Changing the parent edge of the root keeps `RootedArrays`: only the other entries are read. -/
lemma RootedArrays.congr_pe_root {n tM r : ℕ} {tl hd par pe pe' dep : ℕ → ℕ}
    (hR : RootedArrays n tM r tl hd par pe dep) (hpe : ∀ x < n, x ≠ r → pe x = pe' x) :
    RootedArrays n tM r tl hd par pe' dep := by
  refine ⟨hR.par_r, hR.dep_r, hR.par_lt, fun x hx hxr => ?_⟩
  rw [← hpe x hx hxr]
  exact hR.step x hx hxr

end

end MinCostFlow.LSF.Program
