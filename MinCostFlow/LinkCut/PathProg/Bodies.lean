module

public import MinCostFlow.LinkCut.Path.Point
public import MinCostFlow.LinkCut.Path.ReadSum
public import MinCostFlow.LinkCut.Path.ReadyTest
public import MinCostFlow.LinkCut.Gen.FindReady
public import MinCostFlow.LinkCut.Gen.Cut
public import MinCostFlow.Num.Add
public import MinCostFlow.Num.Negate
public import MinCostFlow.Num.IsZero
public import MinCostFlow.Num.Less
public import MinCostFlow.Num.SignExtend
public import MinCostFlow.Num.ModulePlacement

/-!
# The fixed program of the path tree

Section 6 calls the path tree with numbers of `L` limbs, and `L` grows with the input. So the
program must not contain `L`, or any number computed from it, as a constant. This file gives
the program as one list of procedure bodies, `pathTreeBodies h b0`, which depends only on the
limb width `h` (fixed for the whole algorithm) and on the index `b0` of its first procedure.

**The arena.** The initialization, called on `[n, L, heap]`, builds the tree at the heap
pointer `b`, which becomes the handle. Its first five words hold the free list head, `n`, `L`,
the tree width `K = 4 L + 8`, and the address `nb` of the node records (`arenaNb`). The index
of noted roots fills the `2 (2 n) + 3` words below `nb`, and the records of nodes `0 .. 2 n`
follow from `nb` on. Every record carries the layout words of its value block, so the tree
procedures read the record width and `K` from memory (`NodeLayout.val_hdr`).

**The operations.** Each operation wrapper reads `nb`, `n`, `L` and `K` from the arena and
calls the tree procedure of `LinkCut/Gen` or `LinkCut/Path`. Link first widens the new edge
value to `K` limbs in scratch memory, and a path update widens its tag the same way. A path
summary copies the summary out in `L` limbs (`readSumBody`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open WordRAM MinCostFlow.Num MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.Path

/-- The tree width for interface width `L`. -/
def treeLimbs (L : ℕ) : ℕ := 4 * L + 8

/-- The address of the node records of the arena at `b` for `n` vertices. -/
def arenaNb (b n : ℕ) : ℕ := b + 4 * n + 8

/-- The record width of the path layout with `K` limbs. -/
def recW (K : ℕ) : ℕ := 13 + 9 * K

/-- The end of the arena at `b`. -/
def arenaEnd (b n L : ℕ) : ℕ := arenaNb b n + recW (treeLimbs L) * (2 * n + 1)

/-! ### Procedure indices -/

namespace Ix

/-- Offsets from `b0` of the procedures. -/
abbrev init := 0
abbrev link := 1
abbrev cut := 2
abbrev apply := 3
abbrev summary := 4
abbrev read := 5
abbrev write := 6
abbrev find := 7
abbrev copy := 8
abbrev note := 9
abbrev pop := 10
abbrev pick := 11
abbrev rev := 12
abbrev act := 13
abbrev pullP := 14
abbrev isId := 15
abbrev setId := 16
abbrev negB := 17
abbrev addB := 18
abbrev maxI := 19
abbrev seg := 20
abbrev sumT := 21
abbrev valT := 22
abbrev readV := 23
abbrev readS := 24
abbrev widen := 25
abbrev writeV := 26
abbrev revNode := 27
abbrev applyTag := 28
abbrev pdRev := 29
abbrev pdTag := 30
abbrev pushDown := 31
abbrev pull := 32
abbrev rotate := 33
abbrev step := 34
abbrev sLoop := 35
abbrev pushPath := 36
abbrev splay := 37
abbrev detachR := 38
abbrev attachR := 39
abbrev eLoop := 40
abbrev expose := 41
abbrev reroot := 42
abbrev rerootE := 43
abbrev pathApply := 44
abbrev mkSingle := 45
abbrev glink := 46
abbrev detachC := 47
abbrev gcut := 48
abbrev desc := 49
abbrev gfind := 50
abbrev pRead := 51
abbrev pWrite := 52
abbrev neg := 53
abbrev add := 55
abbrev isZ := 57
abbrev less := 58
abbrev ext := 61

end Ix

/-! ### The initialization -/

/-- The words of record `i` that are not zero at the start: the size `1`, the layout words, and
for an edge slot that is not the last one, the next free slot in the parent word. Registers:
`0 = n`, `3 = K`, `4 = nb`, `5 =` record width, `7 = i`. -/
def initRecord : Stmt :=
  .assign 8 (.bin .add (.reg 4) (.bin .mul (.reg 5) (.reg 7))) ;;
  .store (.bin .add (.reg 8) (.const 4)) (.const 1) ;;
  .store (.bin .add (.reg 8) (.const 6)) (.reg 5) ;;
  .store (.bin .add (.reg 8) (.const 7)) (.bin .add (.const 6) (.bin .mul (.const 4) (.reg 3))) ;;
  .store (.bin .add (.reg 8) (.const 8)) (.bin .mul (.const 2) (.reg 3)) ;;
  .store (.bin .add (.reg 8) (.const 9)) (.reg 3) ;;
  .store (.bin .add (.reg 8) (.const 2))
    (.bin .mul (.bin .mul (.bin .lt (.reg 0) (.reg 7))
      (.bin .lt (.bin .add (.reg 7) (.const 1)) (.bin .mul (.const 2) (.reg 0))))
      (.bin .add (.reg 7) (.const 1)))

/-- `init [n, L, heap]`: write the arena header and the nonzero words of the records of nodes
`0 .. 2 n`, and return the end of the arena. -/
def pathInitBody : Stmt :=
  .assign 3 (.bin .add (.bin .mul (.const 4) (.reg 1)) (.const 8)) ;;
  .assign 4 (.bin .add (.reg 2) (.bin .add (.bin .mul (.const 4) (.reg 0)) (.const 8))) ;;
  .assign 5 (.bin .add (.const 13) (.bin .mul (.const 9) (.reg 3))) ;;
  .assign 6 (.bin .add (.bin .mul (.const 2) (.reg 0)) (.const 1)) ;;
  .store (.reg 2) (.bin .mul (.bin .sub (.const 1) (.bin .lt (.reg 0) (.const 2)))
    (.bin .add (.reg 0) (.const 1))) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.reg 0) ;;
  .store (.bin .add (.reg 2) (.const 2)) (.reg 1) ;;
  .store (.bin .add (.reg 2) (.const 3)) (.reg 3) ;;
  .store (.bin .add (.reg 2) (.const 4)) (.reg 4) ;;
  forRange 7 (.const 0) (.reg 6) initRecord ;;
  .ret (.bin .add (.reg 4) (.bin .mul (.reg 5) (.reg 6)))

/-! ### The operation wrappers

Every wrapper gets the handle `b` in register `0` and reads the arena header: `b + 0` the free
list head, `b + 1` the number `n` of vertices, `b + 2` the width `L`, `b + 3` the width `K`,
`b + 4` the record address `nb`. The splay fuel is `2 n + 1`. -/

/-- The splay fuel `2 n + 1`, read from the header at register `0`. -/
abbrev fuelExpr : Expr :=
  .bin .add (.bin .mul (.const 2) (.load (.bin .add (.reg 0) (.const 1)))) (.const 1)

/-- A header word. -/
abbrev hdr (k : ℕ) : Expr := .load (.bin .add (.reg 0) (.const k))

/-- Link, `[b, u, v, value, heap]`. The edge value at `value` has `L` limbs. The wrapper writes
the value block in `K` limbs at `heap + 1`, links, and stores the slot it used at `heap`. -/
def linkWrap (b0 : ℕ) : Stmt :=
  .assign 10 (hdr 3) ;;
  .assign 14 (.bin .add (.reg 4) (.const 1)) ;;
  .assign 15 (.bin .add (.reg 14) (.bin .add (.const 6) (.bin .mul (.const 4) (.reg 10)))) ;;
  .store (.reg 14) (.bin .add (.const 13) (.bin .mul (.const 9) (.reg 10))) ;;
  .store (.bin .add (.reg 14) (.const 1)) (.bin .add (.const 6) (.bin .mul (.const 4) (.reg 10))) ;;
  .store (.bin .add (.reg 14) (.const 2)) (.bin .mul (.const 2) (.reg 10)) ;;
  .store (.bin .add (.reg 14) (.const 3)) (.reg 10) ;;
  .call 16 (b0 + Ix.writeV) [.reg 3, .bin .add (.reg 14) (.const 4), hdr 2, .reg 10, .reg 15] ;;
  .assign 17 (.load (.reg 0)) ;;
  .call 16 (b0 + Ix.glink) [hdr 4, .reg 0, .reg 1, .reg 2, .reg 14, fuelExpr, .reg 15] ;;
  .store (.reg 4) (.reg 17) ;;
  .ret (.reg 15)

/-- Cut, `[b, u, v, heap]`. -/
def cutWrap (b0 : ℕ) : Stmt :=
  .call 5 (b0 + Ix.gcut) [hdr 4, .reg 0, .reg 1, .reg 2, hdr 1, .reg 3] ;;
  .ret (.reg 3)

/-- Path update, `[b, u, v, tag, heap]`. The tag at `tag` has two numbers of `L` limbs; the
wrapper widens them to `K` limbs at `heap`. -/
def applyWrap (b0 : ℕ) : Stmt :=
  .assign 10 (hdr 3) ;;
  .assign 13 (hdr 2) ;;
  .assign 15 (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 10))) ;;
  .call 16 (b0 + Ix.widen) [.reg 3, .reg 4, .reg 13, .reg 10, .reg 15] ;;
  .call 16 (b0 + Ix.widen) [.bin .add (.reg 3) (.reg 13), .bin .add (.reg 4) (.reg 10), .reg 13,
    .reg 10, .reg 15] ;;
  .call 16 (b0 + Ix.pathApply) [hdr 4, .reg 1, .reg 2, .reg 4, fuelExpr, .reg 15] ;;
  .ret (.reg 15)

/-- Path summary, `[b, u, v, heap]`. The summary of the exposed path is copied to `heap` in `L`
limbs. -/
def summaryWrap (b0 : ℕ) : Stmt :=
  .call 5 (b0 + Ix.rerootE) [hdr 4, .reg 1, .reg 2, fuelExpr, .reg 3] ;;
  .assign 10 (hdr 3) ;;
  .assign 13 (hdr 2) ;;
  .assign 14 (.bin .add (.bin .add (hdr 4)
    (.bin .mul (.bin .add (.const 13) (.bin .mul (.const 9) (.reg 10))) (.reg 2)))
    (.bin .add (.const 12) (.bin .mul (.const 4) (.reg 10)))) ;;
  .call 5 (b0 + Ix.readS) [.reg 14, .reg 3, .reg 10, .reg 13] ;;
  .ret (.bin .add (.reg 3) (.bin .add (.bin .mul (.const 3) (.reg 13)) (.const 1)))

/-- Point read, `[b, x, heap]`. -/
def readWrap (b0 : ℕ) : Stmt :=
  .call 5 (b0 + Ix.pRead) [hdr 4, .reg 1, fuelExpr, hdr 2, .reg 2] ;;
  .ret (.reg 5)

/-- Point write, `[b, x, value, heap]`. The wrapper first copies the `2 + 4 L` words of the
value to `heap`, so the write reads the value as it was when the call started. -/
def writeWrap (b0 : ℕ) : Stmt :=
  .assign 13 (hdr 2) ;;
  .assign 14 (.bin .add (.const 2) (.bin .mul (.const 4) (.reg 13))) ;;
  .call 5 (b0 + Ix.copy) [.reg 2, .reg 3, .reg 14] ;;
  .call 5 (b0 + Ix.pWrite) [hdr 4, .reg 1, .reg 3, fuelExpr, .reg 13,
    .bin .add (.reg 3) (.reg 14)] ;;
  .ret (.bin .add (.reg 3) (.reg 14))

/-- Find a ready edge, `[b, heap]`. The answer is stored at `heap`. -/
def findWrap (b0 : ℕ) : Stmt :=
  .call 5 (b0 + Ix.gfind) [hdr 4, fuelExpr, .bin .add (.reg 1) (.const 1)] ;;
  .store (.reg 1) (.reg 5) ;;
  .ret (.bin .add (.reg 1) (.const 1))

/-! ### The program -/

/-- The procedures at offsets `0 .. 52` from `b0`. -/
def pathCoreBodies (h b0 : ℕ) : List Stmt :=
  [pathInitBody, linkWrap b0, cutWrap b0, applyWrap b0, summaryWrap b0, readWrap b0,
    writeWrap b0, findWrap b0,
    copyWords, noteBody, popBody, pickBody,
    pathRevBody (b0 + Ix.negB), pathActBody (b0 + Ix.addB),
    pathPullBody (b0 + Ix.seg) (b0 + Ix.copy), pathIsIdBody (b0 + Ix.isZ),
    pathSetIdBody (b0 + Ix.copy),
    negBlockBody (b0 + Ix.neg) (b0 + Ix.copy), addBlockBody (b0 + Ix.add) (b0 + Ix.copy),
    maxIntoBody (b0 + Ix.less) (b0 + Ix.copy), segBody (b0 + Ix.addB) (b0 + Ix.maxI),
    pathSumTestBody h, pathValTestBody h,
    readValBody (b0 + Ix.copy), readSumBody (b0 + Ix.copy),
    widenBody (b0 + Ix.ext) (b0 + Ix.copy), writeValBody (b0 + Ix.widen) (b0 + Ix.copy),
    revNodeBody (b0 + Ix.rev), applyTagBody (b0 + Ix.act),
    pushDownRevBody (b0 + Ix.revNode),
    pushDownTagBody (b0 + Ix.isId) (b0 + Ix.setId) (b0 + Ix.copy) (b0 + Ix.applyTag),
    pushDownBody (b0 + Ix.pdRev) (b0 + Ix.pdTag),
    pullBody (b0 + Ix.pullP), rotateBody (b0 + Ix.pull), splayStepBody (b0 + Ix.rotate),
    splayLoopBody (b0 + Ix.sLoop) (b0 + Ix.step),
    pushPathBody (b0 + Ix.pushPath) (b0 + Ix.pushDown),
    splayBody (b0 + Ix.pushPath) (b0 + Ix.sLoop),
    detachRightBody (b0 + Ix.pull) (b0 + Ix.note), attachRightBody (b0 + Ix.pull),
    exposeLoopBody (b0 + Ix.splay) (b0 + Ix.detachR) (b0 + Ix.attachR) (b0 + Ix.eLoop),
    exposeBody (b0 + Ix.splay) (b0 + Ix.detachR) (b0 + Ix.eLoop),
    rerootBody (b0 + Ix.expose) (b0 + Ix.revNode),
    rerootExposeBody (b0 + Ix.reroot) (b0 + Ix.expose),
    pathApplyBody (b0 + Ix.rerootE) (b0 + Ix.applyTag),
    makeSingletonBody (b0 + Ix.copy) (b0 + Ix.setId) (b0 + Ix.pull),
    linkBody (b0 + Ix.reroot) (b0 + Ix.mkSingle) (b0 + Ix.note),
    detachRootChildrenBody (b0 + Ix.pull) (b0 + Ix.note),
    cutBody (b0 + Ix.rerootE) (b0 + Ix.pushDown) (b0 + Ix.splay) (b0 + Ix.detachC)
      (b0 + Ix.pick),
    descendBody (b0 + Ix.desc) (b0 + Ix.pushDown) (b0 + Ix.sumT) (b0 + Ix.valT),
    findReadyBody (b0 + Ix.gfind) (b0 + Ix.desc) (b0 + Ix.expose) (b0 + Ix.sumT) (b0 + Ix.pop),
    pointReadBody (b0 + Ix.expose) (b0 + Ix.readV),
    pointWriteBody (b0 + Ix.expose) (b0 + Ix.writeV) (b0 + Ix.pull)]

/-- The whole program of the path tree, from index `b0` on. The number procedures follow the
tree procedures. -/
def pathTreeBodies (h b0 : ℕ) : List Stmt :=
  pathCoreBodies h b0 ++ (negateModule (b0 + Ix.neg) h ++ (addModule (b0 + Ix.add) h ++
    (isZeroModule (b0 + Ix.isZ) ++ (lessModule (b0 + Ix.less) h ++
      signExtendModule (b0 + Ix.ext) h))))

theorem pathCoreBodies_length (h b0 : ℕ) : (pathCoreBodies h b0).length = 53 := rfl

end MinCostFlow.LinkCut.PathProg
