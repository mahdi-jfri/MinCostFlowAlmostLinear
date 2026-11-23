module

public import MinCostFlow.LSF.Program.CallSeq3
public import MinCostFlow.LSF.Program.InitPlaces

/-!
# The init driver: the steps of the main path

The main path of `Initialize` (when `2 ≤ n₀` and `1 ≤ m₀`) is one step sequence
(`CallSeq3.lean`). Registers `0 … 9` hold the arguments
`[g0Ptr, lenArr, wtArr, L_in, P_fp, k_nat, L_w, vCap, eCap, b]`, and step `j` writes register
`10 + j`. The steps compute the places of `InitPlaces.lean` from the arguments, the sizes of `G₀`
and the results of the calls, and call the phases in order: `prepStage`, `widths`, the tree phase,
the order phase, `wstrLB`, the decomposition phase and the forest phase. Then two `storeArgs`
calls write the header of the aux block and the header of the state, and the last step computes
the end of the used memory, which the body returns.

The procedure indices are fixed numbers of the program (`InitIdx`). Every other number is read
from a register or from memory.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-- The procedure indices that the driver calls. -/
structure InitIdx where
  log2 : ℕ
  prep : ℕ
  widths : ℕ
  tree : ℕ
  order : ℕ
  lb : ℕ
  decomp : ℕ
  forest : ℕ
  store20 : ℕ
  store24 : ℕ

namespace InitDriver

/-- Short names for expressions. -/
abbrev r (i : ℕ) : Expr := .reg i
abbrev k (c : ℕ) : Expr := .const c
abbrev add (a b : Expr) : Expr := .bin .add a b
abbrev mul (a b : Expr) : Expr := .bin .mul a b
abbrev sub (a b : Expr) : Expr := .bin .sub a b
abbrev ld (a : Expr) : Expr := .load a

/-- `dynGraphSize vCap eCap = 4 + 7 vCap + 9 eCap`. -/
abbrev eDyn (vc ec : Expr) : Expr := add (add (k 4) (mul (k 7) vc)) (mul (k 9) ec)

/-- `wsStep n tM m0 LB j` as an expression (`WstrStage.lean`). -/
def eWsStep (n tM m0 LB : Expr) : ℕ → Expr
  | 0 => n
  | 1 => mul tM LB
  | 2 => mul n LB
  | 3 => mul m0 LB
  | 4 => n
  | 5 => n
  | 6 => tM
  | 7 => n
  | 8 => mul n LB
  | 9 => mul m0 LB
  | 10 => mul m0 LB
  | _ => LB

/-- `wsPt idPtr n tM m0 LB j` as an expression. -/
def eWsPt (id n tM m0 LB : Expr) : ℕ → Expr
  | 0 => id
  | j + 1 => add (eWsPt id n tM m0 LB j) (eWsStep n tM m0 LB j)

-- the registers of the numbers and places
abbrev rG0 : ℕ := 0
abbrev rLen : ℕ := 1
abbrev rWt : ℕ := 2
abbrev rLin : ℕ := 3
abbrev rPfp : ℕ := 4
abbrev rKn : ℕ := 5
abbrev rLw : ℕ := 6
abbrev rVc : ℕ := 7
abbrev rEc : ℕ := 8
abbrev rB : ℕ := 9
abbrev rN : ℕ := 10
abbrev rM : ℕ := 11
abbrev rTM : ℕ := 12
abbrev rLg1 : ℕ := 13
abbrev rLg0 : ℕ := 14
abbrev rLog : ℕ := 15
abbrev rD : ℕ := 16
abbrev rAuxSz : ℕ := 17
abbrev rDyn : ℕ := 18
abbrev rTB : ℕ := 19
abbrev rGP : ℕ := 20
abbrev rTP : ℕ := 21
abbrev rFP : ℕ := 22
abbrev rFA : ℕ := 23
abbrev rWP : ℕ := 24
abbrev rAux : ℕ := 25
abbrev rNumSt : ℕ := 26
abbrev rDenSt : ℕ := 27
abbrev rEnd : ℕ := 28
abbrev rCnt : ℕ := 29
abbrev rKw : ℕ := 31
abbrev rK : ℕ := 32
abbrev rQ : ℕ := 33
abbrev rMult : ℕ := 34
abbrev rCT : ℕ := 35
abbrev rCH : ℕ := 36
abbrev rCL : ℕ := 37
abbrev rCW : ℕ := 38
abbrev rCO : ℕ := 39
abbrev rCS : ℕ := 40
abbrev rOO : ℕ := 41
abbrev rOB : ℕ := 42
abbrev rOH : ℕ := 43
abbrev rUB : ℕ := 44
abbrev rTO : ℕ := 45
abbrev rTT : ℕ := 46
abbrev rTH : ℕ := 47
abbrev rLH : ℕ := 48
abbrev rH : ℕ := 49
abbrev rNO : ℕ := 50
abbrev rVI : ℕ := 51
abbrev rVL : ℕ := 52
abbrev rAP : ℕ := 53
abbrev rMin : ℕ := 54
abbrev rThD : ℕ := 55
abbrev rS : ℕ := 56
abbrev rEu : ℕ := 57
abbrev rEv : ℕ := 58
abbrev rDP : ℕ := 59
abbrev rTmp : ℕ := 60
abbrev rArr : ℕ := 61
abbrev rScr : ℕ := 62
abbrev rThB : ℕ := 63
abbrev rTh : ℕ := 65
abbrev rLB : ℕ := 66
abbrev rDB : ℕ := 67
abbrev rHi : ℕ := 68
abbrev rInR : ℕ := 69
abbrev rNumS : ℕ := 70
abbrev rId : ℕ := 71
abbrev rWB : ℕ := 73

/-- `tOrigIdBase tPtr vCap tM` from the registers. -/
abbrev eTOrigId : Expr :=
  add (add (r rTP) (k tHdrSize)) (eDyn (r rVc) (add (mul (k 2) (r rTM)) (k 1)))

/-- The arguments of the order phase (`OrderLayout.args`). -/
def orderArgs : List Expr :=
  [r rN, r rTM, r rTT, r rTH, k 0, r rH, r rS, r rAP, r rLog, r rM,
    add (add (add (r rGP) (k 4)) (mul (k 7) (r rVc))) (r rEc),
    add (add (add (r rGP) (k 4)) (mul (k 7) (r rVc))) (mul (k 3) (r rEc)),
    add (add (add (r rGP) (k 4)) (mul (k 7) (r rVc))) (mul (k 4) (r rEc)),
    add (add (r rGP) (k 4)) (mul (k 4) (r rVc)),
    r rVI, r rEu, r rEv, r rQ, add (r rKw) (k 6), r rDP, r rK, r rTmp,
    add (r rAP) (mul (k 3) (r rN)), add (add (r rAP) (r rN)) (r rN),
    add (add (add (r rS) (r rN)) (mul (k 2) (r rTM))) (r rN),
    add (r rAP) (r rN), r rArr, r rScr, add eTOrigId (r rTM), r rMin,
    r rTP, r rVc, r rEc, r rVL, r rTO, r rNO, eTOrigId, add (r rTP) (k tHdrSize), r rThB,
    r rThD, add (r rAP) (r rN)]

/-- The arguments of the decomposition phase (`DecompLayout.args`). -/
def decompArgs : List Expr :=
  [r rN, r rM, r rEu, r rEv, add (add (add (r rS) (r rN)) (mul (k 2) (r rTM))) (r rN), r rAP,
    k 0, r rTh, r rDB, r rD, r rLw, r rTM, r rKn, r rLin, r rNO, r rLog, r rLen, eTOrigId,
    add (r rAP) (r rN), add eTOrigId (r rTM), add (r rThB) (mul (k 7) (r rN)),
    add (r rAP) (mul (k 3) (r rN)), add (add (r rAP) (r rN)) (r rN),
    add (add (add (r rGP) (k 4)) (mul (k 7) (r rVc))) (r rEc), r rNumS,
    add (r rNumS) (mul (r rEc) (r rLw)), r rId, r rHi, r rCnt,
    add (r rDB) (mul (k 11) (r rN)), add (r rThD) (add (r rN) (mul (k 3) (r rVc))),
    r rVI, r rInR, r rThD, add (r rInR) (r rN), add (add (r rInR) (r rN)) (r rN),
    add (add (add (r rInR) (r rN)) (r rN)) (r rTM), r rNumSt, r rDenSt, mul (r rEc) (r rLw)]

/-- The arguments of the forest phase (`FLayout.args`). -/
def forestArgs : List Expr :=
  [r rFP, r rVc, add (mul (k 3) (r rEc)) (r rN), r rN, r rVL, r rTM, r rTT, r rTH, eTOrigId,
    add (add (r rInR) (r rN)) (r rN), r rFA, r rInR,
    add (add (add (r rInR) (r rN)) (r rN)) (r rTM), k 0, add (r rAP) (r rN),
    add (r rDB) (mul (k 6) (r rN)), add (r rDB) (mul (k 7) (r rN)), r rLog, r rWB, r rAP, r rWP]

/-- The arguments of the tree phase (`treePhaseProc`). The index table `auxVIdxBase` is computed
here, since register `rVI` is set only in the order segment. -/
def treeArgs : List Expr :=
  [r rGP, add (add (add (r rGP) (k 4)) (mul (k 7) (r rVc))) (r rEc), r rLen, r rWt, r rLin,
    r rM, r rKw, r rQ, r rLH, add (r rAux) (k auxHdrSize), r rN, r rEc, r rMult, r rCT, r rCH,
    r rCL, r rCW, r rCO, r rCS, r rUB, r rOO, r rOB, r rOH, r rTO, r rTT, r rTH]

/-- The words of the aux header (`AuxAt`), after the place `auxPtr`. The index of `r₀` in the
vertex list is `0`. -/
def auxHdrArgs : List Expr :=
  let base := add (r rAux) (k auxHdrSize)
  let vl := add base (r rVc)
  let par := add vl (r rN)
  let pti := add par (r rN)
  let dep := add pti (r rN)
  let upV := add dep (r rN)
  let upMin := add upV (mul (r rN) (r rLog))
  let thP := add upMin (mul (r rN) (r rLog))
  let ov := add thP (r rN)
  let iov := add ov (r rVc)
  let qa := add iov (r rVc)
  let qb := add qa (r rVc)
  let va := add qb (r rVc)
  let vb := add va (r rVc)
  let ts := add vb (r rVc)
  let fs := add ts (add (r rD) (k 2))
  [r rAux, base, vl, par, pti, dep, r rLog, upV, upMin, thP, ov, iov, qa, qb, va, vb, ts, fs, k 0,
    k 0, k 0]

/-- The words of the state header (`lsfHeaderAt`), after the handle `b`. -/
def lsfHdrArgs (h : ℕ) : List Expr :=
  [r rB, r rVc, r rEc, r rN, r rM, r rGP, r rTP, r rFP, r rFA, r rWP, r rNumSt, r rDenSt, r rLw,
    k h, r rPfp, r rLin, k 0, ld (r rFA), k 0, r rAux, r rEnd, ld (r rVL), r rKn, r rTM, k 0]

/-- Steps `0 … 18`: the sizes, the logarithms and the static blocks. -/
def segA (I : InitIdx) : List DStep :=
  [ -- sizes and logarithms
    .assign (ld (add (r rG0) (k dgNOff))),
    .assign (ld (add (r rG0) (k dgMOff))),
    .assign (sub (r rN) (k 1)),
    .call I.log2 [add (r rN) (k 1)],
    .call I.log2 [r rN],
    .assign (add (r rLg1) (k 1)),
    .assign (mul (add (r rLg0) (k 1)) (add (r rLg0) (k 2))),
    .assign (add (add (add (add (add (k auxHdrSize) (mul (k 7) (r rVc))) (mul (k 5) (r rN)))
      (mul (k 2) (mul (r rN) (r rLog)))) (add (r rD) (k 2))) (add (k 4) (r rN))),
    .assign (eDyn (r rVc) (r rEc)),
    .assign (add (add (add (add (k tHdrSize) (eDyn (r rVc) (add (mul (k 2) (r rTM)) (k 1))))
      (mul (k 4) (r rTM))) (r rEc)) (add (k 4) (mul (k 2) (r rTM)))),
    -- the static blocks
    .assign (add (r rB) (k lsfHdrSize)),
    .assign (add (r rGP) (r rDyn)),
    .assign (add (r rTP) (r rTB)),
    .assign (add (r rFP) (eDyn (r rVc) (add (mul (k 3) (r rEc)) (r rN)))),
    .assign (add (r rFA) (add (k fAncHdrSize) (mul (k 5) (r rVc)))),
    .assign (add (r rWP) (add (add (add (add (k wHdrSize) (add (r rN) (k 1))) (mul (k 2) (r rN)))
      (add (r rN) (k 1))) (r rN))),
    .assign (add (r rAux) (r rAuxSz)),
    .assign (add (r rNumSt) (mul (r rEc) (r rLw))),
    .assign (add (r rDenSt) (mul (r rEc) (r rLw)))]

/-- Steps `19 … 39`: the copy of `G₀`, the widths and the tree phase. -/
def segB (I : InitIdx) : List DStep :=
  [ -- the copy of `G₀`, the vertex list, the parameters
    .call I.prep [r rG0, r rVc, r rEc, r rKn, r rAux, r rGP, r rEnd, r rN, r rM,
      add (add (add (r rG0) (k 4)) (mul (k 7) (ld (add (r rG0) (k dgVCapOff)))))
        (ld (add (r rG0) (k dgECapOff))),
      add (add (r rAux) (k auxHdrSize)) (r rVc)],
    .call I.widths [r rM, r rLin, add (r rEnd) (k 3)],
    .assign (ld (add (r rEnd) (k 3))),
    .assign (ld (add (r rEnd) (k 5))),
    -- the tree phase
    .assign (add (r rEnd) (k 6)),
    .assign (add (r rQ) (mul (r rM) (add (r rKw) (k 6)))),
    .assign (add (add (add (r rMult) (r rM)) (mul (k 5) (r rKw))) (mul (k 2) (add (r rKw) (k 6)))),
    .assign (add (r rCT) (mul (k 2) (r rM))),
    .assign (add (r rCH) (mul (k 2) (r rM))),
    .assign (add (r rCL) (mul (mul (k 2) (r rM)) (r rLin))),
    .assign (add (r rCW) (mul (mul (k 2) (r rM)) (r rLin))),
    .assign (add (r rCO) (mul (k 2) (r rM))),
    .assign (add (r rCS) (mul (k 2) (r rM))),
    .assign (add (r rOO) (r rN)),
    .assign (add (r rOB) (mul (k 2) (r rN))),
    .assign (add (r rOH) (k 2)),
    .assign (add (r rUB) (add (mul (k 2) (r rM)) (r rN))),
    .assign (add (r rTO) (r rN)),
    .assign (add (r rTT) (r rN)),
    .assign (add (r rTH) (r rN)),
    .call I.tree treeArgs]

/-- Steps `40 … 54`: the order phase. -/
def segC (I : InitIdx) : List DStep :=
  [ -- the order phase
    .assign (ld (r rOH)),
    .assign (add (r rAux) (k auxHdrSize)),
    .assign (add (r rVI) (r rVc)),
    .assign (add (r rVL) (r rN)),
    .assign (add (add (r rAP) (mul (k 3) (r rN))) (mul (r rN) (r rLog))),
    .assign (add (r rMin) (mul (r rN) (r rLog))),
    .assign (add (r rH) (mul (k 3) (r rN))),
    .assign (add (add (r rS) (mul (k 4) (r rN))) (mul (k 2) (r rTM))),
    .assign (add (r rEu) (r rM)),
    .assign (add (r rEv) (r rM)),
    .assign (add (r rDP) (mul (r rN) (r rK))),
    .assign (add (r rTmp) (r rK)),
    .assign (add (r rArr) (r rN)),
    .assign (add (r rScr) (r rN)),
    .call I.order orderArgs]

/-- Steps `55 … 62`: the decomposition phase. -/
def segD (I : InitIdx) : List DStep :=
  [ -- the decomposition phase
    .assign (ld (add (r rEnd) (k 2))),
    .call I.lb [r rN, r rD, r rLw],
    .assign (add (r rThB) (mul (k 8) (r rN))),
    .assign (add (r rDB) (mul (k 12) (r rN))),
    .assign (add (r rHi) (r rM)),
    .assign (add (add (r rInR) (mul (k 3) (r rN))) (r rTM)),
    .assign (add (r rNumS) (mul (k 2) (mul (r rEc) (r rLw)))),
    .call I.decomp decompArgs]

/-- Steps `63, 64`: the forest phase. -/
def segE (I : InitIdx) : List DStep :=
  [ -- the forest phase
    .assign (add (eWsPt (r rId) (r rN) (r rTM) (r rM) (r rLB) 18) (r rM)),
    .call I.forest forestArgs]

/-- Steps `65 … 67`: the headers and the end of the used memory. -/
def segF (I : InitIdx) (h : ℕ) : List DStep :=
  [ -- the headers and the end of the used memory
    .call I.store20 auxHdrArgs,
    .call I.store24 (lsfHdrArgs h),
    .assign (add (r rWB) (add (mul (r rN) (mul (k 3) (r rLog))) (mul (k 3) (r rN))))]

/-- The steps of the main path. -/
def mainSteps (I : InitIdx) (h : ℕ) : List DStep :=
  segA I ++ (segB I ++ (segC I ++ (segD I ++ (segE I ++ segF I h))))

/-- The register of the last step, which the body returns. -/
def rRet : ℕ := 77

lemma mainSteps_length (I : InitIdx) (h : ℕ) : (mainSteps I h).length = 68 := rfl

/-- The body of the main path. -/
def mainBody (I : InitIdx) (h : ℕ) : Stmt := dseqStmt 10 rRet 0 (mainSteps I h)

lemma mainBody_noRand (I : InitIdx) (h : ℕ) : (mainBody I h).NoRand :=
  dseqStmt_noRand _ _ _ _

end InitDriver

end

end MinCostFlow.LSF.Program
