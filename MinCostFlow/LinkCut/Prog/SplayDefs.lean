module

public import MinCostFlow.LinkCut.Prog.SplayTree
public import MinCostFlow.Num.Zero
public import MinCostFlow.Num.Copy
public import MinCostFlow.Num.Add
public import MinCostFlow.Num.Subtract
public import MinCostFlow.Num.Less
public import MinCostFlow.Num.Equal
public import WordRAM.Model

namespace MinCostFlow.LinkCut.Prog

/-!
This file defines the shared Word-RAM splay-node memory layout (`NODE_STRIDE = 30`),
storing pointers to `MinCostFlow.Num` multi-limb blocks for directional path availability,
flow, cost sum, and lazy path-add tags, together with the splay procedures
(`reverseNode`, `applyTag`, `pushDown`, `pull`, `pushPath`, `rotate`, `splay`) and
the splay potential `splayMemPhi`.
-/

open WordRAM MinCostFlow.Num

@[expose] public section

/-- Words occupied per node slot `0 .. cap` in the shared splay arena (slot `0` is null). -/
def NODE_STRIDE : ℕ := 30

def OFF_LEFT : ℕ := 0
def OFF_RIGHT : ℕ := 1
def OFF_PARENT : ℕ := 2
def OFF_PPAR : ℕ := 3
def OFF_REV : ℕ := 4
def OFF_ISV : ℕ := 5
def OFF_VCNT : ℕ := 6
def OFF_HASE : ℕ := 7
def OFF_EU : ℕ := 8
def OFF_EV : ℕ := 9
def OFF_EID : ℕ := 10
def OFF_DIR : ℕ := 11
def OFF_FLOW_PTR : ℕ := 12
def OFF_AF_PTR : ℕ := 13
def OFF_AB_PTR : ℕ := 14
def OFF_COST_FWD : ℕ := 15
def OFF_COST_BWD : ℕ := 16
def OFF_CSUM_FWD : ℕ := 17
def OFF_CSUM_BWD : ℕ := 18
def OFF_HAS_TAG : ℕ := 19
def OFF_TAG_PTR : ℕ := 20
def OFF_TAG_NEG : ℕ := 21
def OFF_MIN1_HAS : ℕ := 22
def OFF_MIN1_VAL : ℕ := 23
def OFF_MIN1_FIRST : ℕ := 24
def OFF_MIN1_LAST : ℕ := 25
def OFF_MIN2_HAS : ℕ := 26
def OFF_MIN2_VAL : ℕ := 27
def OFF_MIN2_FIRST : ℕ := 28
def OFF_MIN2_LAST : ℕ := 29

/-- Read field `off` of node `x` from memory `mem` at `nodesBase`. -/
def nodeField (mem : ℕ → ℕ) (nodesBase x off : ℕ) : ℕ :=
  mem (nodesBase + NODE_STRIDE * x + off)

/-- Memory address expression `nodesBase + NODE_STRIDE * x`. -/
def nodePtrExpr (baseReg nodeReg : ℕ) : Expr :=
  .bin .add (.reg baseReg) (.bin .mul (.const NODE_STRIDE) (.reg nodeReg))

/-- Memory address expression `ptr + off`. -/
def fieldAddrExpr (ptrReg off : ℕ) : Expr :=
  .bin .add (.reg ptrReg) (.const off)

/-- Load expression `mem[ptr + off]`. -/
def fieldLoadExpr (ptrReg off : ℕ) : Expr :=
  .load (fieldAddrExpr ptrReg off)

/-- Procedure indices of the `MinCostFlow.Num` primitives and 7 splay procedures in a `Program`. -/
structure SplayProcs where
  numZero : ℕ
  numCopy : ℕ
  numAdd : ℕ
  numSub : ℕ
  numLess : ℕ
  numEqual : ℕ
  revNode : ℕ
  applyTag : ℕ
  pushDown : ℕ
  pull : ℕ
  pushPath : ℕ
  rotate : ℕ
  splay : ℕ

/-- Contiguous procedure numbering starting at `b`. -/
def SplayProcs.atBase (b : ℕ) : SplayProcs where
  numZero := b
  numCopy := b + 1
  numAdd := b + 2
  numSub := b + 4
  numLess := b + 9
  numEqual := b + 12
  revNode := b + 13
  applyTag := b + 14
  pushDown := b + 15
  pull := b + 16
  pushPath := b + 17
  rotate := b + 18
  splay := b + 19

/-- Total number of `Num` + splay procedure slots starting at `b`. -/
def SplayProcs.count : ℕ := 20

/-- Swap fields `f1` and `f2` on the node pointed to by `ptrReg`. -/
def swapFieldsStmt (ptrReg f1 f2 tmp1 tmp2 : ℕ) : Stmt :=
  Stmt.assign tmp1 (fieldLoadExpr ptrReg f1) ;;
  Stmt.assign tmp2 (fieldLoadExpr ptrReg f2) ;;
  Stmt.store (fieldAddrExpr ptrReg f1) (.reg tmp2) ;;
  Stmt.store (fieldAddrExpr ptrReg f2) (.reg tmp1)

/-- `reverseNode(nodesBase, x)`: swaps `left/right`, directional min aggregates, cost sums,
edge direction/availabilities/costs, and negates any pending lazy tag on non-zero node `x`. -/
def revNodeBody : Stmt :=
  Stmt.cond (.reg 1)
    (Stmt.assign 2 (nodePtrExpr 0 1) ;;
     swapFieldsStmt 2 OFF_LEFT OFF_RIGHT 3 4 ;;
     swapFieldsStmt 2 OFF_MIN1_HAS OFF_MIN2_HAS 3 4 ;;
     swapFieldsStmt 2 OFF_MIN1_VAL OFF_MIN2_VAL 3 4 ;;
     swapFieldsStmt 2 OFF_MIN1_FIRST OFF_MIN2_LAST 3 4 ;;
     swapFieldsStmt 2 OFF_MIN1_LAST OFF_MIN2_FIRST 3 4 ;;
     swapFieldsStmt 2 OFF_CSUM_FWD OFF_CSUM_BWD 3 4 ;;
     Stmt.assign 3 (fieldLoadExpr 2 OFF_REV) ;;
     Stmt.store (fieldAddrExpr 2 OFF_REV) (.bin .sub (.const 1) (.reg 3)) ;;
     Stmt.cond (fieldLoadExpr 2 OFF_HASE)
       (Stmt.assign 3 (fieldLoadExpr 2 OFF_DIR) ;;
        Stmt.store (fieldAddrExpr 2 OFF_DIR) (.bin .sub (.const 1) (.reg 3)) ;;
        swapFieldsStmt 2 OFF_AF_PTR OFF_AB_PTR 3 4 ;;
        swapFieldsStmt 2 OFF_COST_FWD OFF_COST_BWD 3 4)
       Stmt.nop ;;
     Stmt.cond (fieldLoadExpr 2 OFF_HAS_TAG)
       (Stmt.assign 3 (fieldLoadExpr 2 OFF_TAG_NEG) ;;
        Stmt.store (fieldAddrExpr 2 OFF_TAG_NEG) (.bin .sub (.const 1) (.reg 3)))
       Stmt.nop ;;
     Stmt.ret (.const 0))
    (Stmt.ret (.const 0))

/-- Add or subtract `tPtrReg` from `valPtrReg` on `LReg`-limb blocks at `hpReg`,
updating `hpReg` and writing the resulting block pointer into `outPtrReg`. -/
def shiftPtrStmt (sp : SplayProcs) (isAddExpr : Expr)
    (valPtrReg tPtrReg LReg hpReg outPtrReg : ℕ) : Stmt :=
  Stmt.cond isAddExpr
    (Stmt.call hpReg sp.numAdd [.reg valPtrReg, .reg tPtrReg, .reg LReg, .reg hpReg] ;;
     Stmt.assign outPtrReg (.bin .sub (.reg hpReg) (.reg LReg)))
    (Stmt.call hpReg sp.numSub [.reg valPtrReg, .reg tPtrReg, .reg LReg, .reg hpReg] ;;
     Stmt.assign outPtrReg (.bin .sub (.reg hpReg) (.reg LReg)))

/-- `applyTag(nodesBase, x, tPtr, tNeg)`: applies a lazy path-add tag `±mem[tPtr]`
to subtree `x`'s own edge values, path-min aggregates, and pending child tag, reading
`L = mem[nodesBase - 3]` and updating the bump heap `mem[nodesBase - 1]`. -/
def applyTagBody (sp : SplayProcs) : Stmt :=
  Stmt.cond (.reg 1)
    (Stmt.assign 4 (nodePtrExpr 0 1) ;;
     Stmt.assign 5 (fieldLoadExpr 4 OFF_MIN1_HAS) ;;
     Stmt.cond (.reg 5)
       (Stmt.assign 6 (.load (.bin .sub (.reg 0) (.const 3))) ;;
        Stmt.assign 7 (.load (.bin .sub (.reg 0) (.const 1))) ;;
        Stmt.cond (fieldLoadExpr 4 OFF_HASE)
          (Stmt.assign 8 (fieldLoadExpr 4 OFF_AF_PTR) ;;
           shiftPtrStmt sp (.reg 3) 8 2 6 7 9 ;;
           Stmt.store (fieldAddrExpr 4 OFF_AF_PTR) (.reg 9) ;;
           Stmt.assign 8 (fieldLoadExpr 4 OFF_AB_PTR) ;;
           shiftPtrStmt sp (.bin .sub (.const 1) (.reg 3)) 8 2 6 7 9 ;;
           Stmt.store (fieldAddrExpr 4 OFF_AB_PTR) (.reg 9) ;;
           Stmt.assign 8 (fieldLoadExpr 4 OFF_FLOW_PTR) ;;
           Stmt.assign 10 (fieldLoadExpr 4 OFF_DIR) ;;
           shiftPtrStmt sp (.bin .sub (.const 1) (.bin .eq (.reg 10) (.reg 3))) 8 2 6 7 9 ;;
           Stmt.store (fieldAddrExpr 4 OFF_FLOW_PTR) (.reg 9))
          Stmt.nop ;;
        Stmt.assign 8 (fieldLoadExpr 4 OFF_MIN1_VAL) ;;
        shiftPtrStmt sp (.reg 3) 8 2 6 7 9 ;;
        Stmt.store (fieldAddrExpr 4 OFF_MIN1_VAL) (.reg 9) ;;
        Stmt.assign 8 (fieldLoadExpr 4 OFF_MIN2_VAL) ;;
        shiftPtrStmt sp (.bin .sub (.const 1) (.reg 3)) 8 2 6 7 9 ;;
        Stmt.store (fieldAddrExpr 4 OFF_MIN2_VAL) (.reg 9) ;;
        Stmt.assign 10 (fieldLoadExpr 4 OFF_LEFT) ;;
        Stmt.assign 10 (nodePtrExpr 0 10) ;;
        Stmt.assign 11 (fieldLoadExpr 4 OFF_RIGHT) ;;
        Stmt.assign 11 (nodePtrExpr 0 11) ;;
        Stmt.assign 9 (.bin .add (fieldLoadExpr 10 OFF_MIN1_HAS) (fieldLoadExpr 11 OFF_MIN1_HAS)) ;;
        Stmt.cond (.reg 9)
          (Stmt.cond (fieldLoadExpr 4 OFF_HAS_TAG)
            (Stmt.assign 8 (fieldLoadExpr 4 OFF_TAG_PTR) ;;
             Stmt.assign 10 (fieldLoadExpr 4 OFF_TAG_NEG) ;;
             shiftPtrStmt sp (.bin .eq (.reg 10) (.reg 3)) 8 2 6 7 9 ;;
             Stmt.store (fieldAddrExpr 4 OFF_TAG_PTR) (.reg 9))
            (Stmt.store (fieldAddrExpr 4 OFF_HAS_TAG) (.const 1) ;;
             Stmt.store (fieldAddrExpr 4 OFF_TAG_PTR) (.reg 2) ;;
             Stmt.store (fieldAddrExpr 4 OFF_TAG_NEG) (.reg 3)))
          Stmt.nop ;;
        Stmt.store (.bin .sub (.reg 0) (.const 1)) (.reg 7) ;;
        Stmt.ret (.const 0))
       (Stmt.ret (.const 0)))
    (Stmt.ret (.const 0))

/-- `pushDown(nodesBase, x)`: pushes lazy reversal and lazy path-add tag from `x`
down to its physical children `left` and `right`. -/
def pushDownBody (sp : SplayProcs) : Stmt :=
  Stmt.cond (.reg 1)
    (Stmt.assign 2 (nodePtrExpr 0 1) ;;
     Stmt.assign 3 (fieldLoadExpr 2 OFF_REV) ;;
     Stmt.cond (.reg 3)
       (Stmt.assign 4 (fieldLoadExpr 2 OFF_LEFT) ;;
        Stmt.call 5 sp.revNode [.reg 0, .reg 4] ;;
        Stmt.assign 4 (fieldLoadExpr 2 OFF_RIGHT) ;;
        Stmt.call 5 sp.revNode [.reg 0, .reg 4] ;;
        Stmt.store (fieldAddrExpr 2 OFF_REV) (.const 0))
       Stmt.nop ;;
     Stmt.assign 3 (fieldLoadExpr 2 OFF_HAS_TAG) ;;
     Stmt.cond (.reg 3)
       (Stmt.assign 4 (fieldLoadExpr 2 OFF_TAG_PTR) ;;
        Stmt.assign 5 (fieldLoadExpr 2 OFF_TAG_NEG) ;;
        Stmt.store (fieldAddrExpr 2 OFF_HAS_TAG) (.const 0) ;;
        Stmt.store (fieldAddrExpr 2 OFF_TAG_PTR) (.const 0) ;;
        Stmt.store (fieldAddrExpr 2 OFF_TAG_NEG) (.const 0) ;;
        Stmt.assign 6 (fieldLoadExpr 2 OFF_LEFT) ;;
        Stmt.call 7 sp.applyTag [.reg 0, .reg 6, .reg 4, .reg 5] ;;
        Stmt.assign 6 (fieldLoadExpr 2 OFF_RIGHT) ;;
        Stmt.call 7 sp.applyTag [.reg 0, .reg 6, .reg 4, .reg 5])
       Stmt.nop ;;
     Stmt.ret (.const 0))
    (Stmt.ret (.const 0))

/-- Add optional `Num` pointers `p1Reg` and `p2Reg` (`0` = canonical zero) into `outReg`,
distinct from `p1Reg` and `p2Reg`, allocating on `hpReg` when both are non-zero. -/
def addOptPtrStmt (sp : SplayProcs) (p1Reg p2Reg LReg hpReg outReg : ℕ) : Stmt :=
  Stmt.cond (.reg p1Reg)
    (Stmt.cond (.reg p2Reg)
      (Stmt.call hpReg sp.numAdd [.reg p1Reg, .reg p2Reg, .reg LReg, .reg hpReg] ;;
       Stmt.assign outReg (.bin .sub (.reg hpReg) (.reg LReg)))
      (Stmt.assign outReg (.reg p1Reg)))
    (Stmt.assign outReg (.reg p2Reg))

/-- Merge `(rHB, rVB, rFB, rLB)` into `(rHA, rVA, rFA, rLA)` using multi-limb
`Num.Less` and `Num.Equal` on `LReg`-limb pointers, using scratch `cmpReg`. -/
def combineNumAggStmt (sp : SplayProcs) (rHA rVA rFA rLA rHB rVB rFB rLB LReg cmpReg : ℕ) :
    Stmt :=
  Stmt.cond (.reg rHB)
    (Stmt.cond (.reg rHA)
      (Stmt.call cmpReg sp.numLess [.reg rVB, .reg rVA, .reg LReg] ;;
       Stmt.cond (.reg cmpReg)
         (Stmt.assign rVA (.reg rVB) ;;
          Stmt.assign rFA (.reg rFB) ;;
          Stmt.assign rLA (.reg rLB))
         (Stmt.call cmpReg sp.numEqual [.reg rVA, .reg rVB, .reg LReg] ;;
          Stmt.cond (.reg cmpReg)
            (Stmt.assign rLA (.reg rLB))
            Stmt.nop))
      (Stmt.assign rHA (.const 1) ;;
       Stmt.assign rVA (.reg rVB) ;;
       Stmt.assign rFA (.reg rFB) ;;
       Stmt.assign rLA (.reg rLB)))
    Stmt.nop

/-- Parameterized statement updating one 4-field `MinAgg` aggregate `(fMinHas, fMinVal,
fMinFirst, fMinLast)` on node `xReg` (`xPtr = ptrReg`) from left (`lPtrReg`) and right
(`rPtrReg`) children using own fields `(OFF_HASE, fSelfVal)`, `L` in `reg 15`, cmp in `reg 17`. -/
def pullMinNumStmt (sp : SplayProcs)
    (xReg ptrReg lPtrReg rPtrReg fSelfVal fMinHas fMinVal fMinFirst fMinLast : ℕ) : Stmt :=
  Stmt.assign 7 (fieldLoadExpr lPtrReg fMinHas) ;;
  Stmt.assign 8 (fieldLoadExpr lPtrReg fMinVal) ;;
  Stmt.assign 9 (fieldLoadExpr lPtrReg fMinFirst) ;;
  Stmt.assign 10 (fieldLoadExpr lPtrReg fMinLast) ;;
  Stmt.assign 11 (fieldLoadExpr ptrReg OFF_HASE) ;;
  Stmt.assign 12 (fieldLoadExpr ptrReg fSelfVal) ;;
  Stmt.assign 13 (.reg xReg) ;;
  Stmt.assign 14 (.reg xReg) ;;
  combineNumAggStmt sp 7 8 9 10 11 12 13 14 15 17 ;;
  Stmt.assign 11 (fieldLoadExpr rPtrReg fMinHas) ;;
  Stmt.assign 12 (fieldLoadExpr rPtrReg fMinVal) ;;
  Stmt.assign 13 (fieldLoadExpr rPtrReg fMinFirst) ;;
  Stmt.assign 14 (fieldLoadExpr rPtrReg fMinLast) ;;
  combineNumAggStmt sp 7 8 9 10 11 12 13 14 15 17 ;;
  Stmt.store (fieldAddrExpr ptrReg fMinHas) (.reg 7) ;;
  Stmt.store (fieldAddrExpr ptrReg fMinVal) (.reg 8) ;;
  Stmt.store (fieldAddrExpr ptrReg fMinFirst) (.reg 9) ;;
  Stmt.store (fieldAddrExpr ptrReg fMinLast) (.reg 10)

/-- `pull(nodesBase, x)`: recomputes `vcnt`, `csumFwd`, `csumBwd`, `min1*`, `min2*`
on node `x` from its children `left[x]`, `right[x]` and own fields. -/
def pullBody (sp : SplayProcs) : Stmt :=
  Stmt.cond (.reg 1)
    (Stmt.assign 2 (nodePtrExpr 0 1) ;;
     Stmt.assign 3 (fieldLoadExpr 2 OFF_LEFT) ;;
     Stmt.assign 4 (nodePtrExpr 0 3) ;;
     Stmt.assign 5 (fieldLoadExpr 2 OFF_RIGHT) ;;
     Stmt.assign 6 (nodePtrExpr 0 5) ;;
     Stmt.assign 7 (.bin .add
       (.bin .add (fieldLoadExpr 4 OFF_VCNT) (fieldLoadExpr 2 OFF_ISV))
       (fieldLoadExpr 6 OFF_VCNT)) ;;
     Stmt.store (fieldAddrExpr 2 OFF_VCNT) (.reg 7) ;;
     Stmt.assign 15 (.load (.bin .sub (.reg 0) (.const 3))) ;;
     Stmt.assign 16 (.load (.bin .sub (.reg 0) (.const 1))) ;;
     Stmt.assign 7 (fieldLoadExpr 4 OFF_CSUM_FWD) ;;
     Stmt.assign 8 (fieldLoadExpr 2 OFF_COST_FWD) ;;
     addOptPtrStmt sp 7 8 15 16 18 ;;
     Stmt.assign 7 (fieldLoadExpr 6 OFF_CSUM_FWD) ;;
     addOptPtrStmt sp 18 7 15 16 8 ;;
     Stmt.store (fieldAddrExpr 2 OFF_CSUM_FWD) (.reg 8) ;;
     Stmt.assign 7 (fieldLoadExpr 4 OFF_CSUM_BWD) ;;
     Stmt.assign 8 (fieldLoadExpr 2 OFF_COST_BWD) ;;
     addOptPtrStmt sp 7 8 15 16 18 ;;
     Stmt.assign 7 (fieldLoadExpr 6 OFF_CSUM_BWD) ;;
     addOptPtrStmt sp 18 7 15 16 8 ;;
     Stmt.store (fieldAddrExpr 2 OFF_CSUM_BWD) (.reg 8) ;;
     pullMinNumStmt sp 1 2 4 6 OFF_AF_PTR OFF_MIN1_HAS OFF_MIN1_VAL OFF_MIN1_FIRST OFF_MIN1_LAST ;;
     pullMinNumStmt sp 1 2 4 6 OFF_AB_PTR OFF_MIN2_HAS OFF_MIN2_VAL OFF_MIN2_FIRST OFF_MIN2_LAST ;;
     Stmt.store (.bin .sub (.reg 0) (.const 1)) (.reg 16) ;;
     Stmt.ret (.const 0))
    (Stmt.ret (.const 0))

/-- Recursive `pushPath(nodesBase, x)`: pushes lazy reversals and tags top-down
from the splay root to `x` and returns the old splay root ID. -/
def pushPathBody (sp : SplayProcs) : Stmt :=
  Stmt.cond (.reg 1)
    (Stmt.assign 2 (nodePtrExpr 0 1) ;;
     Stmt.assign 3 (fieldLoadExpr 2 OFF_PARENT) ;;
     Stmt.cond (.reg 3)
       (Stmt.call 4 sp.pushPath [.reg 0, .reg 3] ;;
        Stmt.call 5 sp.pushDown [.reg 0, .reg 1] ;;
        Stmt.ret (.reg 4))
       (Stmt.call 5 sp.pushDown [.reg 0, .reg 1] ;;
        Stmt.ret (.reg 1)))
    (Stmt.ret (.const 0))

/-- Helper updating child pointer of `parent` (`p`) to `b` (`left` or `right` depending on
`isRight`) and setting `parent[b] := p` when `b ≠ 0`, used by both rotation directions. -/
def setChildAndParentStmt (pPtrReg childOff bReg pReg bPtrReg : ℕ) : Stmt :=
  Stmt.store (fieldAddrExpr pPtrReg childOff) (.reg bReg) ;;
  Stmt.cond (.reg bReg)
    (Stmt.assign bPtrReg (nodePtrExpr 0 bReg) ;;
     Stmt.store (fieldAddrExpr bPtrReg OFF_PARENT) (.reg pReg))
    Stmt.nop

/-- `rotate(nodesBase, x)`: single splay rotation of non-root `x` above `p = parent[x]`,
transferring `ppar` to the new subtree root if `p` was root and calling `pull p; pull x`. -/
def rotateBody (sp : SplayProcs) : Stmt :=
  Stmt.assign 2 (nodePtrExpr 0 1) ;;
  Stmt.assign 3 (fieldLoadExpr 2 OFF_PARENT) ;;
  Stmt.cond (.reg 3)
    (Stmt.assign 4 (nodePtrExpr 0 3) ;;
     Stmt.assign 5 (fieldLoadExpr 4 OFF_PARENT) ;;
     Stmt.assign 6 (fieldLoadExpr 4 OFF_PPAR) ;;
     Stmt.store (fieldAddrExpr 2 OFF_PPAR) (.reg 6) ;;
     Stmt.store (fieldAddrExpr 4 OFF_PPAR) (.const 0) ;;
     Stmt.assign 7 (fieldLoadExpr 4 OFF_RIGHT) ;;
     Stmt.assign 8 (.bin .eq (.reg 1) (.reg 7)) ;;
     Stmt.cond (.reg 8)
       (Stmt.assign 9 (fieldLoadExpr 2 OFF_LEFT) ;;
        setChildAndParentStmt 4 OFF_RIGHT 9 3 10 ;;
        Stmt.store (fieldAddrExpr 2 OFF_LEFT) (.reg 3))
       (Stmt.assign 9 (fieldLoadExpr 2 OFF_RIGHT) ;;
        setChildAndParentStmt 4 OFF_LEFT 9 3 10 ;;
        Stmt.store (fieldAddrExpr 2 OFF_RIGHT) (.reg 3)) ;;
     Stmt.store (fieldAddrExpr 4 OFF_PARENT) (.reg 1) ;;
     Stmt.store (fieldAddrExpr 2 OFF_PARENT) (.reg 5) ;;
     Stmt.cond (.reg 5)
       (Stmt.assign 10 (nodePtrExpr 0 5) ;;
        Stmt.assign 11 (fieldLoadExpr 10 OFF_LEFT) ;;
        Stmt.cond (.bin .eq (.reg 3) (.reg 11))
          (Stmt.store (fieldAddrExpr 10 OFF_LEFT) (.reg 1))
          (Stmt.store (fieldAddrExpr 10 OFF_RIGHT) (.reg 1)))
       Stmt.nop ;;
     Stmt.call 11 sp.pull [.reg 0, .reg 3] ;;
     Stmt.call 11 sp.pull [.reg 0, .reg 1] ;;
     Stmt.ret (.const 0))
    (Stmt.ret (.const 0))

/-- `splay(nodesBase, x)`: pushes lazy flags along ancestors of `x`, then loops performing
zig / zig-zig / zig-zag rotations until `x` is the auxiliary root, returning `x`. -/
def splayBody (sp : SplayProcs) : Stmt :=
  Stmt.cond (.reg 1)
    (Stmt.call 2 sp.pushPath [.reg 0, .reg 1] ;;
     Stmt.assign 3 (nodePtrExpr 0 1) ;;
     Stmt.assign 4 (fieldLoadExpr 3 OFF_PARENT) ;;
     Stmt.loop (.reg 4)
       (Stmt.assign 5 (nodePtrExpr 0 4) ;;
        Stmt.assign 6 (fieldLoadExpr 5 OFF_PARENT) ;;
        Stmt.cond (.reg 6)
          (Stmt.assign 7 (nodePtrExpr 0 6) ;;
           Stmt.assign 8 (fieldLoadExpr 7 OFF_LEFT) ;;
           Stmt.assign 9 (fieldLoadExpr 5 OFF_LEFT) ;;
           Stmt.assign 10 (.bin .eq (.reg 4) (.reg 8)) ;;
           Stmt.assign 11 (.bin .eq (.reg 1) (.reg 9)) ;;
           Stmt.cond (.bin .eq (.reg 10) (.reg 11))
             (Stmt.call 12 sp.rotate [.reg 0, .reg 4] ;;
              Stmt.call 12 sp.rotate [.reg 0, .reg 1])
             (Stmt.call 12 sp.rotate [.reg 0, .reg 1] ;;
              Stmt.call 12 sp.rotate [.reg 0, .reg 1]))
          (Stmt.call 12 sp.rotate [.reg 0, .reg 1]) ;;
        Stmt.assign 4 (fieldLoadExpr 3 OFF_PARENT)) ;;
     Stmt.ret (.reg 1))
    (Stmt.ret (.const 0))

/-- List of the `Num` and splay procedure bodies matching `SplayProcs.atBase`. -/
def splayBodies (sp : SplayProcs) (h : ℕ) : List Stmt :=
  zeroModule sp.numZero ++ copyModule sp.numCopy ++ addModule sp.numAdd h ++
  subtractModule sp.numSub h ++ lessModule sp.numLess h ++ equalModule sp.numEqual ++
  [revNodeBody, applyTagBody sp, pushDownBody sp, pullBody sp,
    pushPathBody sp, rotateBody sp, splayBody sp]

/-- Extract the `AuxTree` rooted at `x` from `mem` up to depth `fuel`, stopping if `x > cap`. -/
def readAuxTree (mem : ℕ → ℕ) (nodesBase cap : ℕ) : ℕ → ℕ → AuxTree
  | _, 0 => .leaf
  | 0, _ => .leaf
  | fuel + 1, x =>
      if x ≤ cap then
        .node x
          (readAuxTree mem nodesBase cap fuel (nodeField mem nodesBase x OFF_LEFT))
          (readAuxTree mem nodesBase cap fuel (nodeField mem nodesBase x OFF_RIGHT))
      else .leaf

/-- All auxiliary root node IDs in `1 .. cap` (`parent = 0`). -/
def auxRootIds (mem : ℕ → ℕ) (nodesBase cap : ℕ) : List ℕ :=
  ((List.range cap).map (· + 1)).filter fun r =>
    nodeField mem nodesBase r OFF_PARENT = 0

/-- Sum of `treePhi vSize` across all auxiliary trees rooted in `1 .. cap`, scaled by `K`. -/
def splayMemPhi (K : ℕ) (mem : ℕ → ℕ) (nodesBase cap : ℕ) (vSize : ℕ → ℕ) : ℕ :=
  K * ((auxRootIds mem nodesBase cap).map
    fun r => (readAuxTree mem nodesBase cap cap r).treePhi vSize).sum

end

end MinCostFlow.LinkCut.Prog
