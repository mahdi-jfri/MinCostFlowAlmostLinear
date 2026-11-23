module

public import MinCostFlow.DynSpanner.Program.DynSpannerAffectedFilter

/-!
# Walk pointers of the affected edges: program and contract

Building `J` (`dsBuildProjStmt`) needs, for each affected edge `e = es[k]`, a pointer to its walk
`Π_{<j}(e)` at position `k` of a table. This file gives the procedure that writes this table.

For each edge `e` of the list, `dsWalkPtrsStmt` finds the level `m = findEmbLevel inDom_mid j e`
with the same code as the filter of the affected edges (`dsFilterBodyStmt`), reads the pointer to
`Π_m(e)` from the pointer table of level `m`, and stores it at `outArrPtr + k`. Its arguments are
those of `dsFilterAffectedStmt`, so the same context `FilterCtx` describes the input, with the
list of edges in the field `cand`.

The proof is in `DynSpannerWalkPtrs.lean`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-- Loop body of `dsWalkPtrsStmt` for the edge at position `reg 14`. -/
def dsWalkPtrsBodyStmt : Stmt :=
  .assign 15 (.load (.bin .add (.reg 2) (.reg 14))) ;;
  .assign 16 (.const 0) ;;
  forRange 17 (.const 0) (.reg 1)
    (.assign 18 (.load (.bin .add (.reg 8) (.reg 17))) ;;
     .cond (.reg 18)
       (.cond (.bin .eq (.load (.bin .add (.reg 9)
           (.bin .add (.bin .mul (.reg 17) (.reg 6)) (.reg 15)))) (.reg 18))
         (.assign 16 (.reg 17))
         .nop)
       .nop) ;;
  .assign 17 (.load (.bin .add (.reg 10) (.bin .add (.bin .mul (.reg 16) (.reg 6)) (.reg 15)))) ;;
  .store (.bin .add (.reg 4) (.reg 14)) (.reg 17)

/-- Write the walk pointers of the edges of a list
(`args = [b, j, esPtr, esLen, outArrPtr]`). -/
def dsWalkPtrsStmt : Stmt :=
  dsFilterPrefixStmt ;;
  forRange 14 (.const 0) (.reg 3) dsWalkPtrsBodyStmt ;;
  .ret (.const 0)

/-- The procedures of the module. -/
def walkPtrsProcs : List Stmt := [dsWalkPtrsStmt]

def walkPtrsIdx : ℕ := 0

lemma walkPtrsProcs_noRand : ∀ s ∈ walkPtrsProcs, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- The pointer to the walk `Π_{<j}(e)` in the state: the entry of `e` in the pointer table of
level `findEmbLevel inDom_mid j e`. -/
def FilterCtx.walkPtr (c : FilterCtx) (e : ℕ) : ℕ :=
  c.mem0 (dsPiPtrBase c.b c.L c.vCap c.eCap + findEmbLevel c.inDom_mid c.j e * c.eCap + e)

/-- Contract of `dsWalkPtrsStmt`: position `k` of the table at `outArrPtr` points to the walk
`piLt_mid (cand[k])`, whose words lie in the footprint `footPi`. -/
def dsWalkPtrsContract (c : FilterCtx) : Contract where
  pre args mem :=
    args = [c.b, c.j, c.candPtr, c.candLen, c.outArrPtr] ∧ mem = c.mem0
  post _ mem _ mem' :=
    (∀ k (hk : k < c.cand.length),
      mem' (c.outArrPtr + k) = c.walkPtr c.cand[k] ∧
      MWalkAt mem' (c.walkPtr c.cand[k]) (c.piLt_mid c.cand[k]) ∧
      (∀ addr, c.walkPtr c.cand[k] ≤ addr →
        addr < c.walkPtr c.cand[k] + (mWalkEncode (c.piLt_mid c.cand[k])).length → c.footPi addr) ∧
      c.walkPtr c.cand[k] + (mWalkEncode (c.piLt_mid c.cand[k])).length < 2 ^ c.w) ∧
    ∀ addr, (addr < c.outArrPtr ∨ c.outArrPtr + c.candLen ≤ addr) → mem' addr = mem addr
  cost _ _ := c.cand.length * (35 * c.j + 60) + 150

end

end MinCostFlow.DynSpanner.Program
