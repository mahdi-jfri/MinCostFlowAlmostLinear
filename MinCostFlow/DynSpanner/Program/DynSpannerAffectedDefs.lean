module

public import MinCostFlow.DynSpanner.Program.DynSpannerAffectedCover
public import MinCostFlow.DynSpanner.Program.DynGraphOps

/-!
# Affected-Edge Procedures & Contracts (`DynSpannerAffectedDefs`)

Implements and specifies deterministic Word-RAM procedures (`affectedProcs bOps`, length `3`)
for the `0 < j` level-`S` update and affected-edge discovery:
* `dsUpdateSLevelsStmt` (`affIdxUpdateSLevels = 0`): extracts `touchedVertices`, adds them to
  `sLists[0..j-1]`, and clears `sGen[j..L]`, in `O(L + 1)` time and `O(j)` heap words.
* `dsCollectCandStmt` (`affIdxCollectCand = 1`): extracts `sPrev`, marks `sBit[v] := 1` for
  `v ∈ S_prev`, and collects deduplicated candidate edges `e ∈ revLists i v ∩ G'.E` (`i < j`),
  in `O(|S_prev| + j * |S_prev| + cand.length + 1)` time.
* `dsFilterAffectedStmt` (`affIdxFilterAffected = 2`): for each candidate `e`, finds
  `m₁ = findEmbLevel inDom_mid j e` and walks `piLt_mid e` checking `sBit` to emit exact `.Nodup`
  `affectedEdges G' H_lt piLt_mid S_prev`, in `O(∑_{e ∈ cand} (j + (piLt_mid e).length + 1))` time.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

def affIdxUpdateSLevels : ℕ := 0
def affIdxCollectCand : ℕ := 1
def affIdxFilterAffected : ℕ := 2

/-! ## Shared Offset-Computation Macro -/

/-- Compute `sGenBase (r11)`, `vsGenBase (r12)`, `sHeadBase (r13)` from
`b (r0)`, `vCap (r7)`, `eCap (r8)`, `L (r9)`. Clobbers `r14`. -/
def dsComputeSBasesStmt : Stmt :=
  .assign 14 (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 7)) (.bin .mul (.const 9) (.reg 8)))) ;;
  .assign 11 (.bin .add (.bin .add (.reg 0) (.const dsHdrSize))
    (.bin .mul (.const 3) (.reg 14))) ;;
  .assign 11 (.bin .add (.reg 11)
    (.bin .add (.bin .mul (.const 3) (.reg 8))
      (.bin .mul (.const 2) (.bin .add (.reg 9) (.const 1))))) ;;
  .assign 11 (.bin .add (.reg 11)
    (.bin .add (.bin .add (.reg 9) (.const 1))
      (.bin .mul (.const 2) (.bin .mul (.bin .add (.reg 9) (.const 1)) (.reg 8))))) ;;
  .assign 11 (.bin .add (.reg 11)
    (.bin .mul (.const 2) (.bin .mul (.bin .add (.reg 9) (.const 1)) (.reg 7)))) ;;
  .assign 12 (.bin .add (.reg 11) (.bin .add (.reg 9) (.const 1))) ;;
  .assign 13 (.bin .add (.reg 12) (.bin .mul (.bin .add (.reg 9) (.const 1)) (.reg 7)))

/-! ## Procedure 0: `dsUpdateSLevelsStmt` -/

/-- Inner step inserting vertex expression `vExpr` into level `i` (`r14`) of `S_level`.
Assumes `r0=b, r3=heapPtr, r11=sGenBase, r12=vsGenBase, r13=sHeadBase, r14=i, r15=sgi, r16=rowBase`. -/
def dsInsertSLevelVertexStmt (vExpr : Expr) : Stmt :=
  .cond (.bin .eq (.load (.bin .add (.reg 16) vExpr)) (.reg 15))
    .nop
    (.store (.bin .add (.reg 16) vExpr) (.reg 15) ;;
     .assign 17 (.load (.bin .add (.reg 13) (.reg 14))) ;;
     .store (.reg 3) vExpr ;;
     .store (.bin .add (.reg 3) (.const 1)) (.reg 17) ;;
     .store (.bin .add (.reg 13) (.reg 14)) (.reg 3) ;;
     .assign 3 (.bin .add (.reg 3) (.const 2)))

/-- `args = [b, j, updPtr, heapPtr]`: updates `S_level` for step `u` at level `0 < j`, returning
`newHeap`. Must be called before `G` is mutated if `u = delete e`. -/
def dsUpdateSLevelsStmt (bOps : ℕ) : Stmt :=
  .cond (.bin .eq (.load (.reg 2)) (.const 1))
    (.assign 7 (.load (.bin .add (.reg 2) (.const 1))) ;;
     .call 5 (bOps + dgIdxGetTail) [.bin .add (.reg 0) (.const dsHdrSize), .reg 7] ;;
     .call 6 (bOps + dgIdxGetHead) [.bin .add (.reg 0) (.const dsHdrSize), .reg 7])
    (.assign 5 (.load (.bin .add (.reg 2) (.const 1))) ;;
     .assign 6 (.load (.bin .add (.reg 2) (.const 2)))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const dsGenOff))) ;;
  dsComputeSBasesStmt ;;
  forRange 14 (.const 0) (.reg 1)
    (.assign 15 (.load (.bin .add (.reg 11) (.reg 14))) ;;
     .cond (.reg 15) .nop
       (.assign 10 (.bin .add (.reg 10) (.const 1)) ;;
        .store (.bin .add (.reg 0) (.const dsGenOff)) (.reg 10) ;;
        .store (.bin .add (.reg 11) (.reg 14)) (.reg 10) ;;
        .store (.bin .add (.reg 13) (.reg 14)) (.const 0) ;;
        .assign 15 (.reg 10)) ;;
     .assign 16 (.bin .add (.reg 12) (.bin .mul (.reg 14) (.reg 7))) ;;
     dsInsertSLevelVertexStmt (.reg 5) ;;
     dsInsertSLevelVertexStmt (.reg 6)) ;;
  forRange 14 (.reg 1) (.bin .add (.reg 9) (.const 1))
    (.store (.bin .add (.reg 11) (.reg 14)) (.const 0)) ;;
  .ret (.reg 3)

/-! ## Procedure 1: `dsCollectCandStmt` -/

/-- `args = [b, j, heapPtr]`: extracts `sPrev` from `S_level (j - 1)`, marks `sBit[v] := 1`,
scans `revLists[0..j-1, sPrev]` filtering by `e ∈ G'.E` and deduping via `eStamp`, writing
`[sPrevLen, candLen]` at `heapPtr..+2`, `sPrev` at `heapPtr+2..`, `cand` right after, returning `retHeap`. -/
def dsCollectCandStmt : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const dsGenOff))) ;;
  -- Compute bases into r7..r13: domGen(7), revGen(8), revHead(9), sGen(10), sHead(11), sBit(12), eStamp(13)
  .assign 14 (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 3)) (.bin .mul (.const 9) (.reg 4)))) ;;
  .assign 7 (.bin .add (.bin .add (.reg 0) (.const dsHdrSize)) (.bin .mul (.const 3) (.reg 14))) ;;
  .assign 7 (.bin .add (.reg 7)
    (.bin .add (.bin .mul (.const 3) (.reg 4)) (.bin .mul (.const 2) (.bin .add (.reg 5) (.const 1))))) ;;
  .assign 8 (.bin .add (.reg 7)
    (.bin .add (.bin .add (.reg 5) (.const 1))
      (.bin .mul (.const 2) (.bin .mul (.bin .add (.reg 5) (.const 1)) (.reg 4))))) ;;
  .assign 9 (.bin .add (.reg 8) (.bin .mul (.bin .add (.reg 5) (.const 1)) (.reg 3))) ;;
  .assign 10 (.bin .add (.reg 9) (.bin .mul (.bin .add (.reg 5) (.const 1)) (.reg 3))) ;;
  .assign 11 (.bin .add (.bin .add (.reg 10) (.bin .add (.reg 5) (.const 1)))
    (.bin .mul (.bin .add (.reg 5) (.const 1)) (.reg 3))) ;;
  .assign 12 (.bin .add (.reg 11) (.bin .add (.reg 5) (.const 1))) ;;
  .assign 13 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 3))) ;;
  -- Phase A: extract sPrev from S_level (j - 1) and mark sBit
  .assign 14 (.bin .add (.reg 2) (.const 2)) ;;
  .assign 15 (.bin .sub (.reg 1) (.const 1)) ;;
  .cond (.load (.bin .add (.reg 10) (.reg 15)))
    (.assign 15 (.load (.bin .add (.reg 11) (.reg 15))) ;;
     .loop (.reg 15)
       (.assign 16 (.load (.reg 15)) ;;
        .store (.reg 14) (.reg 16) ;;
        .assign 14 (.bin .add (.reg 14) (.const 1)) ;;
        .store (.bin .add (.reg 12) (.reg 16)) (.const 1) ;;
        .assign 15 (.load (.bin .add (.reg 15) (.const 1)))))
    .nop ;;
  .assign 15 (.bin .sub (.reg 14) (.bin .add (.reg 2) (.const 2))) ;;
  .store (.reg 2) (.reg 15) ;;
  -- Phase B: bump gen, scan revLists[0..j-1, sPrev], filter G'.E + eStamp
  .assign 6 (.bin .add (.reg 6) (.const 1)) ;;
  .store (.bin .add (.reg 0) (.const dsGenOff)) (.reg 6) ;;
  .assign 16 (.reg 14) ;;
  .assign 17 (.bin .add (.bin .add (.reg 0) (.const (dsHdrSize + 4))) (.bin .mul (.const 7) (.reg 3))) ;;
  forRange 18 (.const 0) (.reg 1)
    (.assign 19 (.load (.bin .add (.reg 7) (.reg 18))) ;;
     .cond (.reg 19)
       (.assign 20 (.bin .add (.reg 8) (.bin .mul (.reg 18) (.reg 3))) ;;
        .assign 21 (.bin .add (.reg 9) (.bin .mul (.reg 18) (.reg 3))) ;;
        forRange 22 (.const 0) (.reg 15)
          (.assign 23 (.load (.bin .add (.bin .add (.reg 2) (.const 2)) (.reg 22))) ;;
           .cond (.bin .eq (.load (.bin .add (.reg 20) (.reg 23))) (.reg 19))
             (.assign 24 (.load (.bin .add (.reg 21) (.reg 23))) ;;
              .loop (.reg 24)
                (.assign 25 (.load (.reg 24)) ;;
                 .cond (.load (.bin .add (.reg 17) (.reg 25)))
                   (.cond (.bin .eq (.load (.bin .add (.reg 13) (.reg 25))) (.reg 6))
                      .nop
                      (.store (.bin .add (.reg 13) (.reg 25)) (.reg 6) ;;
                       .store (.reg 14) (.reg 25) ;;
                       .assign 14 (.bin .add (.reg 14) (.const 1))))
                   .nop ;;
                 .assign 24 (.load (.bin .add (.reg 24) (.const 1)))))
             .nop))
       .nop) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.bin .sub (.reg 14) (.reg 16)) ;;
  .ret (.reg 14)

/-! ## Procedure 2: `dsFilterAffectedStmt` -/

/-- Loop body of `dsFilterAffectedStmt` for the candidate at index `reg 14`. It finds the level
`m₁ = findEmbLevel inDom_mid j e` of the candidate `e`, reads the pointer to its walk, loads the
`sBit` of the tail of `e` into the flag `reg 19` (the word is `0` or `1`), and scans the walk
until a vertex with `sBit = 1` is found. It appends `e` to the output when the flag is set. -/
def dsFilterBodyStmt (bOps : ℕ) : Stmt :=
  .assign 15 (.load (.bin .add (.reg 2) (.reg 14))) ;;
  .assign 16 (.const 0) ;;
  forRange 17 (.const 0) (.reg 1)
    (.assign 18 (.load (.bin .add (.reg 8) (.reg 17))) ;;
     .cond (.reg 18)
       (.cond (.bin .eq (.load (.bin .add (.reg 9) (.bin .add (.bin .mul (.reg 17) (.reg 6)) (.reg 15)))) (.reg 18))
         (.assign 16 (.reg 17))
         .nop)
       .nop) ;;
  .assign 17 (.load (.bin .add (.reg 10) (.bin .add (.bin .mul (.reg 16) (.reg 6)) (.reg 15)))) ;;
  .call 18 (bOps + dgIdxGetTail) [.reg 13, .reg 15] ;;
  .assign 19 (.load (.bin .add (.reg 11) (.reg 18))) ;;
  .assign 20 (.load (.reg 17)) ;;
  .assign 21 (.const 0) ;;
  .loop (.bin .mul (.bin .lt (.reg 21) (.reg 20)) (.bin .eq (.reg 19) (.const 0)))
    (.assign 22 (.load (.bin .add (.reg 17) (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 21))))) ;;
     .assign 23 (.load (.bin .add (.reg 17) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 21))))) ;;
     .cond (.reg 23)
       (.call 18 (bOps + dgIdxGetHead) [.reg 13, .reg 22])
       (.call 18 (bOps + dgIdxGetTail) [.reg 13, .reg 22]) ;;
     .cond (.load (.bin .add (.reg 11) (.reg 18))) (.assign 19 (.const 1)) .nop ;;
     .assign 21 (.bin .add (.reg 21) (.const 1))) ;;
  .cond (.reg 19)
    (.store (.bin .add (.reg 4) (.reg 12)) (.reg 15) ;;
     .assign 12 (.bin .add (.reg 12) (.const 1)))
    .nop

/-- The first eleven assignments of `dsFilterAffectedStmt`: read `vCap`, `eCap`, `L` from the
header and compute the bases `domGen` (`reg 8`), `edgeDomGen` (`reg 9`), `piPtr` (`reg 10`),
`sBit` (`reg 11`) and the host graph pointer (`reg 13`); `reg 12` (the output count) is `0`. -/
def dsFilterPrefixStmt : Stmt :=
  .assign 5 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
  .assign 12 (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 5)) (.bin .mul (.const 9) (.reg 6)))) ;;
  .assign 8 (.bin .add (.bin .add (.reg 0) (.const dsHdrSize)) (.bin .mul (.const 3) (.reg 12))) ;;
  .assign 8 (.bin .add (.reg 8)
    (.bin .add (.bin .mul (.const 3) (.reg 6)) (.bin .mul (.const 2) (.bin .add (.reg 7) (.const 1))))) ;;
  .assign 9 (.bin .add (.reg 8) (.bin .add (.reg 7) (.const 1))) ;;
  .assign 10 (.bin .add (.reg 9) (.bin .mul (.bin .add (.reg 7) (.const 1)) (.reg 6))) ;;
  .assign 11 (.bin .add (.reg 10)
    (.bin .add (.bin .mul (.bin .add (.reg 7) (.const 1)) (.reg 6))
      (.bin .add (.bin .mul (.const 3) (.bin .mul (.bin .add (.reg 7) (.const 1)) (.reg 5)))
        (.bin .mul (.const 2) (.bin .add (.reg 7) (.const 1)))))) ;;
  .assign 12 (.const 0) ;;
  .assign 13 (.bin .add (.reg 0) (.const dsHdrSize))

/-- `args = [b, j, candPtr, candLen, outArrPtr]`: for each candidate edge `e`, runs
`dsFilterBodyStmt`, which emits `e` exactly when it lies in
`affectedEdges G' H_lt piLt_mid S_prev`, and returns the number of emitted edges. -/
def dsFilterAffectedStmt (bOps : ℕ) : Stmt :=
  dsFilterPrefixStmt ;;
  forRange 14 (.const 0) (.reg 3) (dsFilterBodyStmt bOps) ;;
  .ret (.reg 12)

/-- Affected-edge discovery module (`3` deterministic procedures). -/
def affectedProcs (bOps : ℕ) : List Stmt :=
  [dsUpdateSLevelsStmt bOps, dsCollectCandStmt, dsFilterAffectedStmt bOps]

lemma affectedProcs_length (bOps : ℕ) : (affectedProcs bOps).length = 3 := rfl

lemma affectedProcs_noRand (bOps : ℕ) : ∀ s ∈ affectedProcs bOps, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-! ## Layout Equations for `dsS*`, `dsDomGen*`, `dsEStamp*` -/

lemma dsSGenBase_eq (b L vCap eCap : ℕ) :
    dsSGenBase b L vCap eCap =
      dsRevHeadBase b L vCap eCap + (L + 1) * vCap := rfl

lemma dsSBitBase_add_double_vCap (b L vCap eCap : ℕ) :
    dsSBitBase b L vCap eCap + 2 * vCap = dsEStampBase b L vCap eCap := by
  simp only [dsEStampBase, dsVStampBase, dsSBitBase]; omega

end

end MinCostFlow.DynSpanner.Program
