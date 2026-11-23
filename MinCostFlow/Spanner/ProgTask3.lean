module

public import MinCostFlow.Spanner.ProgTask2
public import MinCostFlow.Spanner.ProgTask1Proof

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM Cited

/-!
# Word-RAM Implementation and Contract of Task 3 (Embedding `J` into `W`)

Defines header offsets (`t3HdrSize = 32`), Word-RAM expressions and procedures
(`t3InitEmbBody`, `t3DrainQueueBody`, `t3MiddleEdgeBody`, `t3RoundBody`,
`task3Body`, `task3Module`), capacity/word-width predicates (`Task3Input.Valid`,
`Task3OutAt`), runtime bound `task3Cost`, and `task3Contract`.
-/

/-- Word-RAM expression shorthands for Task 3. -/
def t3Add (a b : Expr) : Expr := .bin .add a b
def t3Mul (a b : Expr) : Expr := .bin .mul a b
def t3Lt (a b : Expr) : Expr := .bin .lt a b
def t3Eq (a b : Expr) : Expr := .bin .eq a b
def t3Or (a b : Expr) : Expr := .bin .or a b
def t3Ld (base off : Expr) : Expr := .load (t3Add base off)
def t3St (base off val : Expr) : Stmt := .store (t3Add base off) val

/-- Task 3 header size in words at `base := inp.v2`. -/
def t3HdrSize : ℕ := 32

/-- Packed Task 3 header layout offsets (`0..31`) relative to `base`. -/
def t3OffEmbJW : ℕ := 0
def t3OffEta2 : ℕ := 1
def t3OffGetPath : ℕ := 2
def t3OffDel : ℕ := 3
def t3OffEcongUpd : ℕ := 4
def t3OffHCur : ℕ := 5
def t3OffJAddr : ℕ := 6
def t3OffT1Addr : ℕ := 7
def t3OffJm : ℕ := 8
def t3OffWm : ℕ := 9
def t3OffK : ℕ := 10
def t3OffPrepH : ℕ := 11
def t3OffWInpH : ℕ := 12
def t3OffAComps : ℕ := 13
def t3OffACompExt : ℕ := 14
def t3OffWAddr : ℕ := 15
def t3OffWWNum : ℕ := 16
def t3OffWSrc : ℕ := 17
def t3OffJSrc : ℕ := 18
def t3OffTau2 : ℕ := 19
def t3OffPhiDen : ℕ := 20
def t3OffMw : ℕ := 21
def t3OffPhiNumC : ℕ := 22
def t3OffPhiDenC : ℕ := 23
def t3OffDsHdl : ℕ := 24
def t3OffECnt : ℕ := 25
def t3OffWDel : ℕ := 26
def t3OffQueue : ℕ := 27
def t3OffVOff : ℕ := 28
def t3OffVStmp : ℕ := 29
def t3OffNextU : ℕ := 30
def t3OffCont : ℕ := 31

/-- Loop `regIdx` over `[lo, hi)` (mutating `regIdx` from `lo` to `hi`). -/
def t3ForRange (regIdx : ℕ) (lo hi : Expr) (body : Stmt) : Stmt :=
  Stmt.seq (.assign regIdx lo)
    (.loop (t3Lt (.reg regIdx) hi)
      (.seq body (.assign regIdx (t3Add (.reg regIdx) (.const 1)))))

/-- Procedure 1 (`selfBase + 1`): `t3InitEmb([base])`
Initializes `embJW[0..J.m-1]`, increments `econgCount[eW]` for `inJ0` edges,
records `base + t3OffCont = 1` iff any `inComp` edge exists, and updates `hCur`. -/
def t3InitEmbBody : Stmt :=
  let base := Expr.reg 0
  let rJm := Expr.reg 1
  let rWAddr := Expr.reg 2
  let rJSrc := Expr.reg 3
  let rEmb := Expr.reg 4
  let rECnt := Expr.reg 5
  let rHCur := Expr.reg 6
  let rCont := Expr.reg 7
  let rEJ := Expr.reg 8
  let rTag := Expr.reg 9
  let rEW := Expr.reg 10
  let rU := Expr.reg 11
  let rV := Expr.reg 12
  let loopBody :=
    Stmt.seq (.assign 9 (.load (t3Add rJSrc (t3Mul (.const 3) rEJ))))
      (.cond (t3Eq rTag (.const 0))
        (Stmt.seq (.store rHCur (.const 0))
          (Stmt.seq (t3St rHCur (.const 1) (.const 0))
            (Stmt.seq (.store (t3Add rEmb rEJ) rHCur)
              (.assign 6 (t3Add rHCur (.const 2))))))
        (.cond (t3Eq rTag (.const 1))
          (Stmt.seq (.assign 10 (t3Ld rJSrc (t3Add (t3Mul (.const 3) rEJ) (.const 1))))
            (Stmt.seq (.assign 11 (t3Ld rWAddr (t3Add (.const 2) (t3Mul (.const 2) rEW))))
              (Stmt.seq (.assign 12 (t3Ld rWAddr (t3Add (.const 3) (t3Mul (.const 2) rEW))))
                (Stmt.seq (.store rHCur (.const 2))
                  (Stmt.seq (t3St rHCur (.const 1) rU)
                    (Stmt.seq (t3St rHCur (.const 2) rV)
                      (Stmt.seq (t3St rHCur (.const 3) (.const 1))
                        (Stmt.seq (t3St rHCur (.const 4) rEW)
                          (Stmt.seq (.store (t3Add rEmb rEJ) rHCur)
                            (Stmt.seq (.assign 6 (t3Add rHCur (.const 5)))
                              (.store (t3Add rECnt rEW)
                                (t3Add (.load (t3Add rECnt rEW)) (.const 1)))))))))))))
          (.assign 7 (.const 1))))
  Stmt.seq (.assign 1 (t3Ld base (.const t3OffJm)))
    (Stmt.seq (.assign 2 (t3Ld base (.const t3OffWAddr)))
      (Stmt.seq (.assign 3 (t3Ld base (.const t3OffJSrc)))
        (Stmt.seq (.assign 4 (t3Ld base (.const t3OffEmbJW)))
          (Stmt.seq (.assign 5 (t3Ld base (.const t3OffECnt)))
            (Stmt.seq (.assign 6 (t3Ld base (.const t3OffHCur)))
              (Stmt.seq (.assign 7 (.const 0))
                (Stmt.seq (t3ForRange 8 (.const 0) rJm loopBody)
                  (Stmt.seq (t3St base (.const t3OffHCur) rHCur)
                    (Stmt.seq (t3St base (.const t3OffCont) rCont)
                      (.ret rHCur))))))))))

/-- Procedure 2 (`selfBase + 2`): `t3DrainQueue([base, r_cur, qLen])`
Deletes each queued edge `eW = (ci, eL)` from `dsW[ci]` via `dsBase + 1`
and stamps newly isolated `Vhat` vertices in `vhatStamp` with `r_cur`. -/
def t3DrainQueueBody (dsBase : ℕ) : Stmt :=
  let base := Expr.reg 0
  let rCur := Expr.reg 1
  let rQLen := Expr.reg 2
  let rWSrc := Expr.reg 3
  let rHdl := Expr.reg 4
  let rQueue := Expr.reg 5
  let rVOff := Expr.reg 6
  let rVStmp := Expr.reg 7
  let rQi := Expr.reg 8
  let rEW := Expr.reg 9
  let rCi := Expr.reg 10
  let rEL := Expr.reg 11
  let rHCur := Expr.reg 12
  let rB := Expr.reg 13
  let rHNext := Expr.reg 14
  let rKLen := Expr.reg 15
  let rVOffCi := Expr.reg 16
  let rJ := Expr.reg 17
  let rUL := Expr.reg 18
  let innerStamp :=
    Stmt.seq (.assign 18 (t3Ld rHCur (t3Add (.const 1) rJ)))
      (.store (t3Add rVStmp (t3Add rVOffCi rUL)) rCur)
  let drainStep :=
    Stmt.seq (.assign 9 (.load (t3Add rQueue rQi)))
      (Stmt.seq (.assign 10 (t3Ld rWSrc (t3Add (t3Mul (.const 3) rEW) (.const 1))))
        (Stmt.seq (.assign 11 (t3Ld rWSrc (t3Add (t3Mul (.const 3) rEW) (.const 2))))
          (Stmt.seq (.assign 12 (t3Ld base (.const t3OffHCur)))
            (Stmt.seq (.assign 13 (.load (t3Add rHdl rCi)))
              (Stmt.seq (.call 14 (dsBase + 1) [rB, rEL, rHCur])
                (Stmt.seq (t3St base (.const t3OffHCur) rHNext)
                  (Stmt.seq (t3St base (.const t3OffDel) (t3Add (t3Ld base (.const t3OffDel)) (.const 1)))
                    (Stmt.seq (.assign 15 (.load rHCur))
                      (Stmt.seq (.assign 16 (.load (t3Add rVOff rCi)))
                        (t3ForRange 17 (.const 0) rKLen innerStamp))))))))))
  Stmt.seq (.assign 3 (t3Ld base (.const t3OffWSrc)))
    (Stmt.seq (.assign 4 (t3Ld base (.const t3OffDsHdl)))
      (Stmt.seq (.assign 5 (t3Ld base (.const t3OffQueue)))
        (Stmt.seq (.assign 6 (t3Ld base (.const t3OffVOff)))
          (Stmt.seq (.assign 7 (t3Ld base (.const t3OffVStmp)))
            (Stmt.seq (t3ForRange 8 (.const 0) rQLen drainStep)
              (.ret (.const 0)))))))

/-- Procedure 3 (`selfBase + 3`): `t3MiddleEdge([base, r_cur, eJ, ci, jL])`
Calls `dsBase + 2` (`getPath`) on `c.J_sub.edges[jL]`, writes lifted `W`-walk
to `dst := hMid`, updates `embJW[eJ]`, `econgCount`, queues newly congested
active edges (`wDelStamp < r_cur`), and calls `drainBase` if queue non-empty. -/
def t3MiddleEdgeBody (dsBase drainBase : ℕ) : Stmt :=
  let base := Expr.reg 0
  let rCur := Expr.reg 1
  let rEJ := Expr.reg 2
  let rCi := Expr.reg 3
  let rJL := Expr.reg 4
  let rAComps := Expr.reg 5
  let rAExt := Expr.reg 6
  let rHdl := Expr.reg 7
  let rJSub := Expr.reg 8
  let rUL := Expr.reg 9
  let rVL := Expr.reg 10
  let rHCur := Expr.reg 11
  let rB := Expr.reg 12
  let rHMid := Expr.reg 13
  let rVCnt := Expr.reg 14
  let rECnt := Expr.reg 15
  let rVerts := Expr.reg 16
  let rWStart := Expr.reg 17
  let rQLen := Expr.reg 18
  let rWWNum := Expr.reg 19
  let rPhiDen := Expr.reg 20
  let rThresh := Expr.reg 21
  let rECntAddr := Expr.reg 22
  let rWDelAddr := Expr.reg 23
  let rQueue := Expr.reg 24
  let rI := Expr.reg 25
  let rEL := Expr.reg 26
  let rEW := Expr.reg 27
  let rCnt := Expr.reg 28
  let rLhs := Expr.reg 29
  let rRhs := Expr.reg 30
  let copyVert :=
    Stmt.seq (.assign 19 (t3Ld rHCur (t3Add (.const 1) (.reg 18))))
      (Stmt.seq (.assign 20 (.load (t3Add rVerts (.reg 19))))
        (t3St rHMid (t3Add (.const 1) (.reg 18)) (.reg 20)))
  let edgeStep :=
    Stmt.seq (.assign 26 (t3Ld rHCur (t3Add (t3Add (.const 2) rVCnt) rI)))
      (Stmt.seq (.assign 27 (t3Add rWStart rEL))
        (Stmt.seq (t3St rHMid (t3Add (t3Add (.const 2) rVCnt) rI) rEW)
          (Stmt.seq (t3St base (.const t3OffEcongUpd) (t3Add (t3Ld base (.const t3OffEcongUpd)) (.const 1)))
            (Stmt.seq (.assign 28 (t3Add (.load (t3Add rECntAddr rEW)) (.const 1)))
              (Stmt.seq (.store (t3Add rECntAddr rEW) rCnt)
                (Stmt.seq (.assign 29 (t3Mul rThresh (.load (t3Add rWWNum rEW))))
                  (Stmt.seq (.assign 30 (t3Mul rCnt rPhiDen))
                    (.cond (t3Lt rRhs rLhs)
                      .nop
                      (.cond (t3Lt (.load (t3Add rWDelAddr rEW)) rCur)
                        (Stmt.seq (.store (t3Add rWDelAddr rEW) rCur)
                          (Stmt.seq (.store (t3Add rQueue rQLen) rEW)
                            (.assign 18 (t3Add rQLen (.const 1)))))
                        .nop)))))))))
  Stmt.seq (.assign 5 (t3Ld base (.const t3OffAComps)))
    (Stmt.seq (.assign 6 (t3Ld base (.const t3OffACompExt)))
      (Stmt.seq (.assign 7 (t3Ld base (.const t3OffDsHdl)))
        (Stmt.seq (.assign 8 (t3Ld rAComps (t3Add (t3Mul (.const 7) rCi) (.const 3))))
          (Stmt.seq (.assign 9 (t3Ld rJSub (t3Add (.const 2) (t3Mul (.const 2) rJL))))
            (Stmt.seq (.assign 10 (t3Ld rJSub (t3Add (.const 3) (t3Mul (.const 2) rJL))))
              (Stmt.seq (.assign 11 (t3Ld base (.const t3OffHCur)))
                (Stmt.seq (.assign 12 (.load (t3Add rHdl rCi)))
                  (Stmt.seq (.call 13 (dsBase + 2) [rB, rUL, rVL, rHCur])
                    (Stmt.seq (t3St base (.const t3OffGetPath) (t3Add (t3Ld base (.const t3OffGetPath)) (.const 1)))
                      (Stmt.seq (.assign 14 (.load rHCur))
                        (Stmt.seq (.assign 15 (t3Ld rHCur (t3Add (.const 1) rVCnt)))
                          (Stmt.seq (.assign 16 (t3Ld rAComps (t3Add (t3Mul (.const 7) rCi) (.const 2))))
                            (Stmt.seq (.assign 17 (.load (t3Add rAExt (t3Mul (.const 6) rCi))))
                              (Stmt.seq (t3St rHMid (t3Add (.const 1) rVCnt) rECnt)
                                (Stmt.seq (t3ForRange 18 (.const 0) rVCnt copyVert)
                                  (Stmt.seq (.assign 18 (.const 0))
                                    (Stmt.seq (.assign 19 (t3Ld base (.const t3OffWWNum)))
                                      (Stmt.seq (.assign 20 (t3Ld base (.const t3OffPhiDen)))
                                        (Stmt.seq (.assign 21 (t3Mul rCur (t3Ld base (.const t3OffTau2))))
                                          (Stmt.seq (.assign 22 (t3Ld base (.const t3OffECnt)))
                                            (Stmt.seq (.assign 23 (t3Ld base (.const t3OffWDel)))
                                              (Stmt.seq (.assign 24 (t3Ld base (.const t3OffQueue)))
                                                (Stmt.seq (t3ForRange 25 (.const 0) rECnt edgeStep)
                                                  (Stmt.seq (.store rHMid rVCnt)
                                                    (Stmt.seq (t3St base (.const t3OffHCur) (t3Add rHMid (t3Add (t3Add (.const 2) rVCnt) rECnt)))
                                                      (Stmt.seq (.store (t3Add (t3Ld base (.const t3OffEmbJW)) rEJ) rHMid)
                                                        (Stmt.seq (.cond (t3Lt (.const 0) rQLen)
                                                            (.call 25 drainBase [base, rCur, rQLen])
                                                            .nop)
                                                          (.ret (.const 0)))))))))))))))))))))))))))))

/-- Procedure 4 (`selfBase + 4`): `t3Round([base])`
Runs one Task 3 round `r_cur := η₂ + 1`: initializes `dsW[0..K-1]` on `W_sub`,
scans `eJ = 0 .. J.m - 1`, sets `nextHasUnemb := 1` when an unembedded edge
hits `Vhat`, else embeds via `middleBase`, then commits `η₂` and `cont`. -/
def t3RoundBody (dsBase middleBase : ℕ) : Stmt :=
  let base := Expr.reg 0
  let rCur := Expr.reg 1
  let rK := Expr.reg 2
  let rAExt := Expr.reg 3
  let rHdl := Expr.reg 4
  let rPhiNumC := Expr.reg 5
  let rPhiDenC := Expr.reg 6
  let rMw := Expr.reg 7
  let initStep :=
    Stmt.seq (.assign 9 (t3Ld base (.const t3OffHCur)))
      (Stmt.seq (.assign 10 (t3Ld rAExt (t3Add (t3Mul (.const 6) (.reg 8)) (.const 1))))
        (Stmt.seq (.store (t3Add rHdl (.reg 8)) (.reg 9))
          (Stmt.seq (.call 11 dsBase [.reg 10, rPhiNumC, rPhiDenC, rMw, .reg 9])
            (t3St base (.const t3OffHCur) (.reg 11)))))
  let rJm := Expr.reg 8
  let rEmb := Expr.reg 9
  let rJSrc := Expr.reg 10
  let rAComps := Expr.reg 11
  let rVOff := Expr.reg 12
  let rVStmp := Expr.reg 13
  let rEJ := Expr.reg 14
  let rCi := Expr.reg 16
  let rJL := Expr.reg 17
  let rJSub := Expr.reg 18
  let rUL := Expr.reg 19
  let rVL := Expr.reg 20
  let rVOffCi := Expr.reg 21
  let edgeScanStep :=
    Stmt.seq (.assign 15 (.load (t3Add rEmb rEJ)))
      (.cond (t3Eq (.reg 15) (.const 0))
        (Stmt.seq (.assign 16 (t3Ld rJSrc (t3Add (t3Mul (.const 3) rEJ) (.const 1))))
          (Stmt.seq (.assign 17 (t3Ld rJSrc (t3Add (t3Mul (.const 3) rEJ) (.const 2))))
            (Stmt.seq (.assign 18 (t3Ld rAComps (t3Add (t3Mul (.const 7) rCi) (.const 3))))
              (Stmt.seq (.assign 19 (t3Ld rJSub (t3Add (.const 2) (t3Mul (.const 2) rJL))))
                (Stmt.seq (.assign 20 (t3Ld rJSub (t3Add (.const 3) (t3Mul (.const 2) rJL))))
                  (Stmt.seq (.assign 21 (.load (t3Add rVOff rCi)))
                    (Stmt.seq (.assign 22 (.load (t3Add rVStmp (t3Add rVOffCi rUL))))
                      (Stmt.seq (.assign 23 (.load (t3Add rVStmp (t3Add rVOffCi rVL))))
                        (.cond (t3Eq (t3Or (t3Eq (.reg 22) rCur) (t3Eq (.reg 23) rCur)) (.const 1))
                          (t3St base (.const t3OffNextU) (.const 1))
                          (.call 22 middleBase [base, rCur, rEJ, rCi, rJL]))))))))))
        .nop)
  Stmt.seq (.assign 1 (t3Add (t3Ld base (.const t3OffEta2)) (.const 1)))
    (Stmt.seq (t3St base (.const t3OffNextU) (.const 0))
      (Stmt.seq (.assign 2 (t3Ld base (.const t3OffK)))
        (Stmt.seq (.assign 3 (t3Ld base (.const t3OffACompExt)))
          (Stmt.seq (.assign 4 (t3Ld base (.const t3OffDsHdl)))
            (Stmt.seq (.assign 5 (t3Ld base (.const t3OffPhiNumC)))
              (Stmt.seq (.assign 6 (t3Ld base (.const t3OffPhiDenC)))
                (Stmt.seq (.assign 7 (t3Ld base (.const t3OffMw)))
                  (Stmt.seq (t3ForRange 8 (.const 0) rK initStep)
                    (Stmt.seq (.assign 8 (t3Ld base (.const t3OffJm)))
                      (Stmt.seq (.assign 9 (t3Ld base (.const t3OffEmbJW)))
                        (Stmt.seq (.assign 10 (t3Ld base (.const t3OffJSrc)))
                          (Stmt.seq (.assign 11 (t3Ld base (.const t3OffAComps)))
                            (Stmt.seq (.assign 12 (t3Ld base (.const t3OffVOff)))
                              (Stmt.seq (.assign 13 (t3Ld base (.const t3OffVStmp)))
                                (Stmt.seq (t3ForRange 14 (.const 0) rJm edgeScanStep)
                                  (Stmt.seq (t3St base (.const t3OffEta2) rCur)
                                    (Stmt.seq (t3St base (.const t3OffCont) (t3Ld base (.const t3OffNextU)))
                                      (.ret rCur))))))))))))))))))

/-- Procedure 0 (`selfBase + 0`): `task3([jAddr, t1OutAddr, v2])`
Populates header and static array pointers starting at `base := v2`,
computes `vhatOffset`, initializes `embJW` via `selfBase + 1`, runs outer
round loop while `cont = 1` via `selfBase + 4`, and returns final `hCur`. -/
def task3Body (phiNumConst phiDenConst selfBase : ℕ) : Stmt :=
  let rJAddr := Expr.reg 0
  let rT1 := Expr.reg 1
  let base := Expr.reg 2
  let rJm := Expr.reg 3
  let rPrepH := Expr.reg 4
  let rWInpH := Expr.reg 5
  let rAComps := Expr.reg 6
  let rK := Expr.reg 7
  let rAExt := Expr.reg 8
  let rWAddr := Expr.reg 9
  let rWm := Expr.reg 10
  let rPtr := Expr.reg 11
  let rVOff := Expr.reg 12
  let rVSum := Expr.reg 13
  let rCi := Expr.reg 14
  let rN := Expr.reg 15
  let vhatLoop :=
    Stmt.seq (.store (t3Add rVOff rCi) rVSum)
      (Stmt.seq (.assign 15 (t3Ld rAExt (t3Add (t3Mul (.const 6) rCi) (.const 4))))
        (.assign 13 (t3Add rVSum rN)))
  Stmt.seq (.assign 3 (t3Ld rJAddr (.const 1)))
    (Stmt.seq (.assign 4 (t3Ld rT1 (.const 4)))
      (Stmt.seq (.assign 5 (t3Ld rT1 (.const 5)))
        (Stmt.seq (.assign 6 (t3Ld rPrepH (.const 3)))
          (Stmt.seq (.assign 7 (t3Ld rPrepH (.const 2)))
            (Stmt.seq (.assign 8 (t3Ld rWInpH (.const 12)))
              (Stmt.seq (.assign 9 (t3Ld rWInpH (.const 13)))
                (Stmt.seq (.assign 10 (t3Ld rWAddr (.const 1)))
                  (Stmt.seq (t3St base (.const t3OffJAddr) rJAddr)
                    (Stmt.seq (t3St base (.const t3OffT1Addr) rT1)
                      (Stmt.seq (t3St base (.const t3OffJm) rJm)
                        (Stmt.seq (t3St base (.const t3OffWm) rWm)
                          (Stmt.seq (t3St base (.const t3OffK) rK)
                            (Stmt.seq (t3St base (.const t3OffPrepH) rPrepH)
                              (Stmt.seq (t3St base (.const t3OffWInpH) rWInpH)
                                (Stmt.seq (t3St base (.const t3OffAComps) rAComps)
                                  (Stmt.seq (t3St base (.const t3OffACompExt) rAExt)
                                    (Stmt.seq (t3St base (.const t3OffWAddr) rWAddr)
                                      (Stmt.seq (t3St base (.const t3OffWWNum) (t3Ld rWInpH (.const 14)))
                                        (Stmt.seq (t3St base (.const t3OffWSrc) (t3Ld rWInpH (.const 15)))
                                          (Stmt.seq (t3St base (.const t3OffJSrc) (t3Ld rWInpH (.const 16)))
                                            (Stmt.seq (t3St base (.const t3OffTau2) (t3Ld rWInpH (.const 11)))
                                              (Stmt.seq (t3St base (.const t3OffPhiDen) (t3Ld rWInpH (.const 18)))
                                                (Stmt.seq (t3St base (.const t3OffMw) (.load rWInpH))
                                                  (Stmt.seq (t3St base (.const t3OffPhiNumC) (.const phiNumConst))
                                                    (Stmt.seq (t3St base (.const t3OffPhiDenC) (.const phiDenConst))
                                                      (Stmt.seq (.assign 11 (t3Add base (.const t3HdrSize)))
                                                        (Stmt.seq (t3St base (.const t3OffEmbJW) rPtr)
                                                          (Stmt.seq (.assign 11 (t3Add rPtr rJm))
                                                            (Stmt.seq (t3St base (.const t3OffDsHdl) rPtr)
                                                              (Stmt.seq (.assign 11 (t3Add rPtr rK))
                                                                (Stmt.seq (t3St base (.const t3OffECnt) rPtr)
                                                                  (Stmt.seq (.assign 11 (t3Add rPtr rWm))
                                                                    (Stmt.seq (t3St base (.const t3OffWDel) rPtr)
                                                                      (Stmt.seq (.assign 11 (t3Add rPtr rWm))
                                                                        (Stmt.seq (t3St base (.const t3OffQueue) rPtr)
                                                                          (Stmt.seq (.assign 12 (t3Add rPtr rWm))
                                                                            (Stmt.seq (t3St base (.const t3OffVOff) rVOff)
                                                                              (Stmt.seq (.assign 13 (.const 0))
                                                                                (Stmt.seq (t3ForRange 14 (.const 0) rK vhatLoop)
                                                                                  (Stmt.seq (.assign 11 (t3Add rVOff rK))
                                                                                    (Stmt.seq (t3St base (.const t3OffVStmp) rPtr)
                                                                                      (Stmt.seq (t3St base (.const t3OffHCur) (t3Add rPtr rVSum))
                                                                                        (Stmt.seq (.call 15 (selfBase + 1) [base])
                                                                                          (Stmt.seq (.loop (t3Eq (t3Ld base (.const t3OffCont)) (.const 1))
                                                                                              (.call 15 (selfBase + 4) [base]))
                                                                                            (.ret (t3Ld base (.const t3OffHCur)))))))))))))))))))))))))))))))))))))))))))))))

/-- Five-procedure Word-RAM module for Task 3 installed at `[selfBase .. selfBase + 4]`. -/
def task3Module (phiNumConst phiDenConst selfBase dsBase : ℕ) : List Stmt :=
  [ task3Body phiNumConst phiDenConst selfBase
  , t3InitEmbBody
  , t3DrainQueueBody dsBase
  , t3MiddleEdgeBody dsBase (selfBase + 2)
  , t3RoundBody dsBase (selfBase + 3) ]

/-- Input descriptor for Word-RAM Task 3 (`[jAddr, t1OutAddr, v2]`). -/
structure Task3Input where
  jAddr : ℕ
  t1OutAddr : ℕ
  v2 : ℕ
  H' : Graph
  J : Graph
  embJH : ℕ → Walk

namespace Task3Input

noncomputable def dsOneW (impl : SpannerToolImpl) (J : Graph) : ℕ :=
  let mw := Task1Input.mwCap impl J
  let ce := impl.constructExpander
  let pds := impl.pathDS.params
  let dW := WitnessCoreInput.dWInt ce
  pds.C_space * (ce.phiDen + 4 * mw + pds.gExp dW mw + 2) ^ pds.c_space

noncomputable def staticEndCap (impl : SpannerToolImpl) (inp : Task3Input) : ℕ :=
  inp.v2 + t3HdrSize + 5 * inp.J.m + 3 * Task1Input.mwCap impl inp.J

noncomputable def maxHeapEnd (impl : SpannerToolImpl) (inp : Task3Input) : ℕ :=
  let mw := Task1Input.mwCap impl inp.J
  let pds := impl.pathDS.params
  let γW := pds.gExp (WitnessCoreInput.dWInt impl.constructExpander) mw
  let η₂ := eta2Bound inp.J
  staticEndCap impl inp + 5 * inp.J.m +
    (η₂ * inp.J.m + inp.J.m + inp.J.m * γW) * dsOneW impl inp.J +
    inp.J.m * (2 * γW + 3)

noncomputable def maxWordBound (impl : SpannerToolImpl) (inp : Task3Input) : ℕ :=
  let mw := Task1Input.mwCap impl inp.J
  let pdCap := Task1Input.phiDenCap impl inp.J
  let tau2Cap := Task1Input.tau2Cap impl inp.J
  let η₂ := eta2Bound inp.J
  max (maxHeapEnd impl inp + 3)
    (max (η₂ * tau2Cap * maxDeg inp.J * pdCap + 2)
      (max (inp.J.m * pdCap + 2) (3 * mw + 2 * inp.J.m + 4)))

def WordWidthOK (impl : SpannerToolImpl) (inp : Task3Input) (w : ℕ) : Prop :=
  let mw := Task1Input.mwCap impl inp.J
  let ce := impl.constructExpander
  let pds := impl.pathDS.params
  let dW := WitnessCoreInput.dWInt ce
  1 < 2 ^ w ∧
    pds.cw * (Nat.log 2 (ce.phiDen + 4 * mw + pds.gExp dW mw + 2) + 1) ≤ w ∧
    maxWordBound impl inp < 2 ^ w

def Valid (inp : Task3Input) (impl : SpannerToolImpl) (mem : ℕ → ℕ) (w : ℕ) : Prop :=
  inp.J.IsValid ∧
    GraphAt mem inp.jAddr inp.J ∧
    inp.jAddr + inp.J.encode.length ≤ inp.t1OutAddr ∧
    (∃ memPre memT1 v1,
      (∀ x < v1, mem x = memT1 x) ∧
      v1 ≤ inp.v2 ∧
      ZeroFrom mem inp.v2 ∧
      Task1OutAt impl inp.jAddr inp.t1OutAddr inp.H' inp.J inp.embJH memPre memT1 v1 w) ∧
    WordWidthOK impl inp w

end Task3Input

/-- Postcondition of Word-RAM Task 3 preserving `< inp.v2` and writing `embJW` + stats at `inp.v2`. -/
def Task3OutAt (impl : SpannerToolImpl) (inp : Task3Input) (mem mem' : ℕ → ℕ) (v3 w : ℕ) : Prop :=
  (∀ x < inp.v2, mem' x = mem x) ∧
  ZeroFrom mem' v3 ∧
  inp.v2 + t3HdrSize ≤ v3 ∧
  v3 ≤ Task3Input.maxHeapEnd impl inp ∧
  ∃ (wInp : WitnessCoreInput) (WSubs : List Graph)
    (embJW : ℕ → Walk) (eta2 getPathCountW deleteCountW econgUpdates : ℕ),
    let wd := wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs
    wInp.H' = inp.H' ∧
    (∀ e < inp.J.m, wInp.embJH e = inp.embJH e) ∧
    wInp.prep.J = inp.J ∧
    wInp.prep.jAddr = inp.jAddr ∧
    (∃ memPre memT1 v1,
      (∀ x < v1, mem x = memT1 x) ∧
      v1 ≤ inp.v2 ∧
      Task1OutAt impl inp.jAddr inp.t1OutAddr inp.H' inp.J inp.embJH memPre memT1 v1 w ∧
      memT1 (inp.t1OutAddr + 5) = wInp.h ∧
      memT1 (inp.t1OutAddr + 3) = wInp.prep.decAddr ∧
      wInp.prep.StaticValid memT1 w ∧ wInp.prep.hEnd ≤ wInp.h ∧
      wInp.OutputAt impl.constructExpander impl.pathDS.params
        (fun x => if x < wInp.h then memT1 x else memPre x) memT1 v1 wd) ∧
    (∃ memS, wInp.prep.StaticValid memS w) ∧
    wInp.ValidWSubs impl.constructExpander WSubs ∧
    (∀ {N_max : ℕ} {W_max : ℝ} (tools : LocalSpannerTools N_max W_max),
      WitnessOK tools inp.H' inp.J inp.embJH wd) ∧
    mem' inp.v2 = inp.v2 + t3HdrSize ∧
    mem' (inp.v2 + t3OffEta2) = eta2 ∧
    mem' (inp.v2 + t3OffGetPath) = getPathCountW ∧
    mem' (inp.v2 + t3OffDel) = deleteCountW ∧
    mem' (inp.v2 + t3OffEcongUpd) = econgUpdates ∧
    mem' (inp.v2 + t3OffHCur) = v3 ∧
    EmbAt mem' (inp.v2 + t3HdrSize) inp.J.m embJW ∧
    EmbBounded mem' (inp.v2 + t3HdrSize) inp.J.m embJW v3 ∧
    IsEmbedding inp.J wd.W embJW ∧
    eta2 ≤ eta2Bound inp.J ∧
    (∀ eW < wd.W.m, econgAt inp.J (fun _ => 1) wd.wW embJW eW ≤ ((eta2 : ℝ) + 1 / 2) * wd.τ₂) ∧
    (∀ eW < wd.j0Edges.length, econgAt inp.J (fun _ => 1) wd.wW embJW eW ≤ wd.τ₂ / 2) ∧
    (∀ eJ < inp.J.m, (embJW eJ).edges.length ≤ ⌈wd.γ_ExpPath⌉₊) ∧
    ((length inp.J embJW : ℝ) ≤ wd.γ_ExpPath) ∧
    getPathCountW ≤ inp.J.m ∧
    (deleteCountW : ℝ) ≤ (getPathCountW : ℝ) * wd.γ_ExpPath ∧
    (econgUpdates : ℝ) ≤ (getPathCountW : ℝ) * wd.γ_ExpPath

/-- Worst-case Word-RAM cost bound for Task 3. -/
noncomputable def task3Cost (impl : SpannerToolImpl) (J : Graph) : ℕ :=
  let m := J.m
  let pds := impl.pathDS.params
  let ce := impl.constructExpander
  let mw := Task1Input.mwCap impl J
  let γW := pds.gExp (WitnessCoreInput.dWInt ce) mw
  let γWq := pds.gQuery (WitnessCoreInput.dWInt ce) mw
  let η₂ := eta2Bound J
  η₂ * (mw * ⌈pds.K_init * (γW : ℝ)⌉₊ + 80 * mw + 300 * m + 400) +
    m * (⌈pds.K_query * (γWq : ℝ)⌉₊ + γW * (⌈pds.K_del * (γWq : ℝ)⌉₊ + 300) + 600) +
    600

open Classical in
/-- Word-RAM contract for Task 3 (`task3Module`). -/
noncomputable def task3Contract (impl : SpannerToolImpl) (w : ℕ) : Contract where
  pre args mem := ∃ inp : Task3Input, args = [inp.jAddr, inp.t1OutAddr, inp.v2] ∧ inp.Valid impl mem w
  post args mem v3 mem' := ∀ inp : Task3Input, args = [inp.jAddr, inp.t1OutAddr, inp.v2] →
    inp.Valid impl mem w → Task3OutAt impl inp mem mem' v3 w
  cost args mem :=
    if h : ∃ inp : Task3Input, args = [inp.jAddr, inp.t1OutAddr, inp.v2] ∧ inp.Valid impl mem w then
      task3Cost impl (Classical.choose h).J
    else 0

end MinCostFlow.Spanner
