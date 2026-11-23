module

public import MinCostFlow.ExpanderDecomp.RouteProgCsr
public import MinCostFlow.ExpanderDecomp.RouteProgPairs
public import MinCostFlow.ExpanderDecomp.RouteProgLoop
public import MinCostFlow.ExpanderDecomp.ProgStepCSpec

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Top-Level `RouteOrCut` Relocatable Module, Layout, and Helper Stages (`RouteProgWrapBase`)

Defines the relocatable 14-procedure deterministic Word-RAM module `routerProcs base` for the
static multi-pair matching player `routeOrCut`:
- `routeOrCutPairsSetupCost`, `routeOrCutPairsTotalCost`, `routeOrCutPairsHeapSpace`: explicit
  closed-form cost and bump-heap space bounds for the `RouteProgLayout` entry (`base + 12`).
- `routeOrCutMultiSetupCost`, `routeOrCutMultiTotalCost`, `routeOrCutMultiHeapSpace`: bounds for
  the flat `MultiPairsAt` entry (`base + 13`).
- `routeOrCutParamBound`: parameter word-size bound ensuring all intermediate arithmetic and stamp
  generations fit strictly below `2 ^ w`.
- `mkWrapLoopCfg`, `mkWrapLoopDisj`: contiguous bump-heap layout from `h` (with `walksAddr = h`
  and `pathHeap` placed last so `h' = mem'[cfgAddr + 22] + 15 * nX` automatically satisfies
  `ZeroFrom mem' h'`).
- `multiPairsToTableStmt`, `multiPairsToTable_triple`: `O(k)` scan turning flat `MultiPairsAt`
  into pointer-table `PairsAt` + `PairsBounded`.
- `writeRouteLoopCfgStmt`, `writeRouteLoopCfg_triple`: `O(1)` initializer writing all 32 fields
  of `RouteLoopCfg` at `cfgAddr`.
- `routeOrCutPairsProc`, `routeOrCutMultiProc`, `routerProcs`, `routerProcs_noRand`,
  `routeOrCutProgram`, `routeOrCutProgram_noRand`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Cost, Space, and Word-Size Bounds -/

/-- Setup step overhead of `routeOrCutPairsProc` for building the compact local CSR of `G[X]`,
building the compact local terminal pairs, initializing `RouteLoopCfg`, and sorting any cut `U`
into increasing vertex order. -/
def routeOrCutPairsSetupCost (m nX k : ℕ) : ℕ :=
  2 * buildLocalCsrCost m nX + buildLocalPairsCost nX k + 600

/-- Total step bound of `routeOrCutPairsProc` (`base + 12`). -/
def routeOrCutPairsTotalCost (m nX k rcost : ℕ) : ℕ :=
  routeCsrProgCost rcost + routeOrCutPairsSetupCost m nX k

/-- Setup step overhead of `routeOrCutMultiProc` (`base + 13`), adding the `O(k)` flat-to-table
scan of `MultiPairsAt`. -/
def routeOrCutMultiSetupCost (m nX k : ℕ) : ℕ :=
  routeOrCutPairsSetupCost m nX k + 60 * k + 100

/-- Total step bound of `routeOrCutMultiProc` (`base + 13`). -/
def routeOrCutMultiTotalCost (m nX k rcost : ℕ) : ℕ :=
  routeCsrProgCost rcost + routeOrCutMultiSetupCost m nX k

/-- Bump-heap space above `h` used by `routeOrCutPairsProc` (`base + 12`): linear in
`(n, m, nX, k, rcost)` and free of explicit `Δ, L, b`. -/
def routeOrCutPairsHeapSpace (n m nX k rcost : ℕ) : ℕ :=
  (1 + nX) + localCsrSpace n m nX + localPairsSpace nX k +
  2 * k + 32 + batchScratchSize nX (2 * m) k + 1 + (2 * nX + 2) + 5 * rcost + 15 * nX

/-- Bump-heap space above `h` used by `routeOrCutMultiProc` (`base + 13`), adding `1 + 2 * k`
words for the pointer table `pTable` at `h`. -/
def routeOrCutMultiHeapSpace (n m nX k rcost : ℕ) : ℕ :=
  (1 + 2 * k) + routeOrCutPairsHeapSpace n m nX k rcost

/-- Parameter word-size bound ensuring all intermediate arithmetic and stamp generations fit
strictly below `2 ^ w`. -/
def routeOrCutParamBound (m nX k Δ L b z : ℕ) : ℕ :=
  let d := routeD Δ b L
  let Hbatch := routeHBatch Δ b L
  let R := routeR Δ b L
  R * (k * (d + 3) + 1) + (nX + 1) * Hbatch + d + 16 * b * (2 * m + Δ + 1) + z + 32

/-! ## 2. Contiguous Bump-Heap Address Map and `RouteLoopDisj` Constructor -/

def wrapCsrWorkAddr (h nX : ℕ) : ℕ := h + 1 + nX
def wrapPairsWorkAddr (h n m nX : ℕ) : ℕ := wrapCsrWorkAddr h nX + localCsrSpace n m nX
def wrapAccHeadAddr (h n m nX k : ℕ) : ℕ := wrapPairsWorkAddr h n m nX + localPairsSpace nX k
def wrapAccTailAddr (h n m nX k : ℕ) : ℕ := wrapAccHeadAddr h n m nX k + k
def wrapCfgAddr (h n m nX k : ℕ) : ℕ := wrapAccTailAddr h n m nX k + k
def wrapWsAddr (h n m nX k : ℕ) : ℕ := wrapCfgAddr h n m nX k + 32
def wrapCLo (h n m nX m2 k : ℕ) : ℕ := wrapWsAddr h n m nX k + batchScratchSize nX m2 k + 1
def wrapCHi (h n m nX m2 k : ℕ) : ℕ := wrapCLo h n m nX m2 k + 2 * nX + 2
def wrapPLo (h n m nX m2 k : ℕ) : ℕ := wrapCHi h n m nX m2 k
def wrapPHi (h n m nX m2 k rcost : ℕ) : ℕ := wrapPLo h n m nX m2 k + 5 * rcost + 15 * nX

/-- Construct the `RouteLoopCfg` corresponding to the contiguous bump-heap allocation from `h`
inside `routeOrCutPairsProc`. -/
def mkWrapLoopCfg (h n m nX m2 k Δ L b z outAddr initDem : ℕ) : RouteLoopCfg :=
  { batch :=
      { nX := nX, k := k, d := routeD Δ b L, b := b, Hbatch := routeHBatch Δ b L,
        offAddr := csrOffAddr (wrapCsrWorkAddr h nX) nX,
        nbAddr := csrNbAddr (wrapCsrWorkAddr h nX) nX,
        edgeAddr := csrEdgeAddr (wrapCsrWorkAddr h nX) nX m,
        pairBAddr := pairsBAddr (wrapPairsWorkAddr h n m nX),
        aOffAddr := pairsAOffAddr (wrapPairsWorkAddr h n m nX) nX,
        aLenAddr := pairsALenAddr (wrapPairsWorkAddr h n m nX) nX k,
        aDataAddr := pairsADataAddr (wrapPairsWorkAddr h n m nX) nX k,
        accHeadAddr := wrapAccHeadAddr h n m nX k,
        accTailAddr := wrapAccTailAddr h n m nX k,
        ws := wrapWsAddr h n m nX k, m2 := m2, curDemandIn := initDem,
        batchGenIn := 0, bfsGenIn := 0, dfsGenIn := 0, ballGenIn := 0, liveGenIn := 0,
        pathHeapIn := wrapPLo h n m nX m2 k,
        chunkHeapIn := wrapCLo h n m nX m2 k },
    R := routeR Δ b L, z := z, hL := routeH Δ b * L,
    origVertAddr := csrOrigAddr (wrapCsrWorkAddr h nX), outAddr := outAddr, walksAddr := h }

lemma mkWrapLoopDisj {w h n m nX m2 k Δ L b z outAddr initDem rcost : ℕ}
    (hm2_le : m2 ≤ 2 * m) (hnX_le : nX ≤ n) (hdem_le : initDem ≤ nX)
    (hout_h : outAddr + 2 + 2 * n ≤ h)
    (hw_sp : h + routeOrCutPairsHeapSpace n m nX k rcost + 16 < 2 ^ w)
    (hw_par : routeOrCutParamBound m nX k Δ L b z < 2 ^ w)
    (hw16 : 16 < 2 ^ w) :
    RouteLoopDisj w (wrapCfgAddr h n m nX k)
      (wrapPLo h n m nX m2 k) (wrapPHi h n m nX m2 k rcost)
      (wrapCLo h n m nX m2 k) (wrapCHi h n m nX m2 k)
      (mkWrapLoopCfg h n m nX m2 k Δ L b z outAddr initDem) := by
  set aOrig := csrOrigAddr (wrapCsrWorkAddr h nX)
  set aOff := csrOffAddr (wrapCsrWorkAddr h nX) nX
  set aNb := csrNbAddr (wrapCsrWorkAddr h nX) nX
  set aEdge := csrEdgeAddr (wrapCsrWorkAddr h nX) nX m
  set aPB := pairsBAddr (wrapPairsWorkAddr h n m nX)
  set aAO := pairsAOffAddr (wrapPairsWorkAddr h n m nX) nX
  set aAL := pairsALenAddr (wrapPairsWorkAddr h n m nX) nX k
  set aAD := pairsADataAddr (wrapPairsWorkAddr h n m nX) nX k
  set aAH := wrapAccHeadAddr h n m nX k
  set aAT := wrapAccTailAddr h n m nX k
  set aCfg := wrapCfgAddr h n m nX k
  set aWs := wrapWsAddr h n m nX k
  set wsSz := batchScratchSize nX m2 k
  set aCLo := wrapCLo h n m nX m2 k
  set aCHi := wrapCHi h n m nX m2 k
  set aPLo := wrapPLo h n m nX m2 k
  set aPHi := wrapPHi h n m nX m2 k rcost
  -- Monotonic chain of the 17 regions (each proved by 1-line linear arithmetic)
  have c0 : outAddr + (2 + 2 * nX) ≤ h := by omega
  have c1 : h + (1 + nX) = aOrig := by dsimp only [aOrig, csrOrigAddr, wrapCsrWorkAddr]; omega
  have c2 : aOrig + nX = aOff := by dsimp only [aOrig, aOff, csrOrigAddr, csrOffAddr]
  have c3 : aOff + (nX + 1) ≤ aNb := by dsimp only [aOff, aNb, csrOffAddr, csrNbAddr]; omega
  have c4 : aNb + m2 ≤ aEdge := by dsimp only [aNb, aEdge, csrNbAddr, csrEdgeAddr]; omega
  have c5 : aEdge + m2 ≤ aPB := by
    dsimp only [aEdge, aPB, csrEdgeAddr, pairsBAddr, wrapPairsWorkAddr, localCsrSpace]; omega
  have c6 : aPB + nX = aAO := by dsimp only [aPB, aAO, pairsBAddr, pairsAOffAddr]
  have c7 : aAO + (k + 1) = aAL := by dsimp only [aAO, aAL, pairsAOffAddr, pairsALenAddr]; omega
  have c8 : aAL + k = aAD := by dsimp only [aAL, aAD, pairsALenAddr, pairsADataAddr]; omega
  have c9 : aAD + nX ≤ aAH := by
    dsimp only [aAD, aAH, pairsADataAddr, wrapAccHeadAddr, localPairsSpace]; omega
  have c10 : aAH + k = aAT := by dsimp only [aAH, aAT, wrapAccTailAddr]
  have c11 : aAT + k = aCfg := by dsimp only [aAT, aCfg, wrapCfgAddr]
  have c12 : aCfg + 32 = aWs := by dsimp only [aCfg, aWs, wrapWsAddr]
  have c13 : aWs + wsSz + 1 = aCLo := by dsimp only [aWs, wsSz, aCLo, wrapCLo]
  have c14 : aCLo + (2 * nX + 2) = aCHi := by dsimp only [aCLo, aCHi, wrapCHi]; omega
  have c15 : aCHi = aPLo := rfl
  have c16 : aPLo + (5 * rcost + 15 * nX) = aPHi := by dsimp only [aPLo, aPHi, wrapPHi]; omega
  have c17 : aPHi + 16 < 2 ^ w := by
    have hsp : aPHi ≤ h + routeOrCutPairsHeapSpace n m nX k rcost := by
      dsimp only [aPHi, wrapPHi, wrapPLo, wrapCHi, wrapCLo, wrapWsAddr, wrapCfgAddr,
        wrapAccTailAddr, wrapAccHeadAddr, wrapPairsWorkAddr, wrapCsrWorkAddr,
        routeOrCutPairsHeapSpace, batchScratchSize]
      omega
    omega
  have hd_eq : routeD Δ b L = 2 * (routeH Δ b * L) := by
    unfold routeD routePathLen routeH; ring
  have hR_ge : routeR Δ b L * (k * (routeD Δ b L + 3)) + routeR Δ b L =
      routeR Δ b L * (k * (routeD Δ b L + 3) + 1) := by ring
  have hR_k_le : routeR Δ b L * k ≤ routeR Δ b L * (k * (routeD Δ b L + 3)) :=
    Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
  have hR_dfs_le : routeR Δ b L * (k * (routeD Δ b L + 1)) ≤
      routeR Δ b L * (k * (routeD Δ b L + 3)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  have hHb_mul : nX * routeHBatch Δ b L + routeHBatch Δ b L =
      (nX + 1) * routeHBatch Δ b L := by ring
  have h16b_mul : 16 * b * m2 ≤ 16 * b * (2 * m + Δ + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h16b_le : 16 * b ≤ 16 * b * (2 * m + Δ + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hpar : routeR Δ b L * (k * (routeD Δ b L + 3) + 1) + (nX + 1) * routeHBatch Δ b L +
      routeD Δ b L + 16 * b * (2 * m + Δ + 1) + z + 32 < 2 ^ w := hw_par
  have h4nX : 4 * nX + 5 < 2 ^ w := by
    have : 15 * nX ≤ aPHi := by omega
    omega
  have hm2_w : m2 + 5 < 2 ^ w := by omega
  have hk_w : k + 5 < 2 ^ w := by omega
  change RouteLoopDisj w aCfg aPLo aPHi aCLo aCHi _
  dsimp only [mkWrapLoopCfg]
  constructor
  all_goals
    try dsimp only
    first | exact le_rfl | exact Or.inl (by omega) | exact Or.inr (by omega) | omega

/-! ## 3. Deterministic Word-RAM Statements and Relocatable Module -/

/-- Scan flat `MultiPairsAt` at `reg 2` (`k = reg 12` pairs) and populate pointer table
`PairsAt` at `reg 13` (`1 + 2*k` words). Uses scratch registers `14, 15, 16`. -/
def multiPairsToTableStmt : Stmt :=
  seqStmts
    [ .store (.reg 13) (.reg 12)
    , .assign 14 (.bin .add (.reg 2) (.const 1))
    , .assign 15 (.const 0)
    , .loop (.bin .lt (.reg 15) (.reg 12))
        (seqStmts
          [ .store (.bin .add (.bin .add (.reg 13) (.const 1)) (.bin .mul (.const 2) (.reg 15)))
              (.reg 14)
          , .assign 16 (.load (.reg 14))
          , .assign 14 (.bin .add (.bin .add (.reg 14) (.const 1)) (.reg 16))
          , .store (.bin .add (.bin .add (.reg 13) (.const 2)) (.bin .mul (.const 2) (.reg 15)))
              (.reg 14)
          , .assign 16 (.load (.reg 14))
          , .assign 14 (.bin .add (.bin .add (.reg 14) (.const 1)) (.reg 16))
          , .assign 15 (.bin .add (.reg 15) (.const 1)) ]) ]

/-- Write all 32 fields of `RouteLoopCfg` into `[reg 21, reg 21 + 32)`.
Inputs: `5=b, 6=z, 7=outAddr, 8=h, 10=m, 11=nX, 12=k, 14=csrW, 15=m2, 17=pairsW, 18=initDem,
19=accHead, 20=accTail, 21=cfgAddr, 22=ws, 23=cLo, 24=pLo, 26=hL, 27=d, 28=Hbatch, 29=R`. -/
def writeRouteLoopCfgStmt : Stmt :=
  seqStmts
    [ .store (.bin .add (.reg 21) (.const 0)) (.reg 11)
    , .store (.bin .add (.reg 21) (.const 1)) (.reg 12)
    , .store (.bin .add (.reg 21) (.const 2)) (.reg 27)
    , .store (.bin .add (.reg 21) (.const 3)) (.reg 5)
    , .store (.bin .add (.reg 21) (.const 4)) (.reg 28)
    , .store (.bin .add (.reg 21) (.const 5)) (.bin .add (.reg 14) (.reg 11))
    , .store (.bin .add (.reg 21) (.const 6))
        (.bin .add (.bin .add (.reg 14) (.bin .mul (.const 3) (.reg 11))) (.const 1))
    , .store (.bin .add (.reg 21) (.const 7))
        (.bin .add (.bin .add (.bin .add (.reg 14) (.bin .mul (.const 3) (.reg 11))) (.const 1))
          (.bin .mul (.const 2) (.reg 10)))
    , .store (.bin .add (.reg 21) (.const 8)) (.reg 17)
    , .store (.bin .add (.reg 21) (.const 9)) (.bin .add (.reg 17) (.reg 11))
    , .store (.bin .add (.reg 21) (.const 10))
        (.bin .add (.bin .add (.bin .add (.reg 17) (.reg 11)) (.reg 12)) (.const 1))
    , .store (.bin .add (.reg 21) (.const 11))
        (.bin .add (.bin .add (.bin .add (.reg 17) (.reg 11)) (.bin .mul (.const 2) (.reg 12)))
          (.const 1))
    , .store (.bin .add (.reg 21) (.const 12)) (.reg 19)
    , .store (.bin .add (.reg 21) (.const 13)) (.reg 20)
    , .store (.bin .add (.reg 21) (.const 14)) (.reg 22)
    , .store (.bin .add (.reg 21) (.const 15)) (.reg 15)
    , .store (.bin .add (.reg 21) (.const 16)) (.reg 18)
    , .store (.bin .add (.reg 21) (.const 17)) (.const 0)
    , .store (.bin .add (.reg 21) (.const 18)) (.const 0)
    , .store (.bin .add (.reg 21) (.const 19)) (.const 0)
    , .store (.bin .add (.reg 21) (.const 20)) (.const 0)
    , .store (.bin .add (.reg 21) (.const 21)) (.const 0)
    , .store (.bin .add (.reg 21) (.const 22)) (.reg 24)
    , .store (.bin .add (.reg 21) (.const 23)) (.reg 23)
    , .store (.bin .add (.reg 21) (.const 24)) (.const 0)
    , .store (.bin .add (.reg 21) (.const 25)) (.const 0)
    , .store (.bin .add (.reg 21) (.const 26)) (.reg 29)
    , .store (.bin .add (.reg 21) (.const 27)) (.reg 6)
    , .store (.bin .add (.reg 21) (.const 28)) (.reg 26)
    , .store (.bin .add (.reg 21) (.const 29)) (.reg 14)
    , .store (.bin .add (.reg 21) (.const 30)) (.reg 7)
    , .store (.bin .add (.reg 21) (.const 31)) (.reg 8) ]

/-- Top-level `routeOrCut` procedure on `RouteProgLayout` inputs (`GraphAt`, `VertSetAt`, `PairsAt`)
with 9 arguments `[gAddr, xAddr, pAddr, Δ, L, b, z, outAddr, h]`.
Writes `RouteOutAt` at `outAddr` (with any cut `U` sorted in strictly increasing vertex order
`U.sort (· ≤ ·)`) and, when matched, `WalksAt` at `h` with every walk in `[h, h')`, returning the
updated zero-heap cursor `h' = mem'[cfgAddr + 22] + 15 * nX`. -/
def routeOrCutPairsProc (bSort bCsr bPairs bLoop : ℕ) : Stmt :=
  seqStmts
    [ .assign 9 (.load (.reg 0))
    , .assign 10 (.load (.bin .add (.reg 0) (.const 1)))
    , .assign 11 (.load (.reg 1))
    , .assign 12 (.load (.reg 2))
    , .assign 14 (.bin .add (.bin .add (.reg 8) (.const 1)) (.reg 11))
    , .call 15 bCsr [.reg 0, .reg 1, .reg 14]
    , .assign 16 (.bin .add (.bin .add (.bin .add (.reg 14) (.bin .mul (.const 3) (.reg 11)))
        (.const 1)) (.bin .mul (.const 4) (.reg 10)))
    , .assign 17 (.bin .add (.reg 16) (.reg 9))
    , .call 18 bPairs [.reg 2, .reg 11, .reg 16, .reg 17, .reg 9]
    , .assign 19 (.bin .add (.bin .add (.bin .add (.reg 17) (.bin .mul (.const 3) (.reg 11)))
        (.bin .mul (.const 3) (.reg 12))) (.const 1))
    , .assign 20 (.bin .add (.reg 19) (.reg 12))
    , .assign 21 (.bin .add (.reg 20) (.reg 12))
    , .assign 22 (.bin .add (.reg 21) (.const 32))
    , .assign 23 (.bin .add (.bin .add (.bin .add (.bin .add (.bin .add (.reg 22) (.const 129))
        (.bin .mul (.const 27) (.reg 11))) (.reg 15)) (.bin .mul (.const 3) (.reg 12))) (.const 1))
    , .assign 24 (.bin .add (.bin .add (.reg 23) (.bin .mul (.const 2) (.reg 11))) (.const 2))
    , .assign 25 (.bin .mul (.bin .mul (.const 16) (.reg 3)) (.reg 5))
    , .assign 26 (.bin .mul (.reg 25) (.reg 4))
    , .assign 27 (.bin .mul (.const 2) (.reg 26))
    , .assign 28 (.bin .mul (.reg 25) (.bin .add (.reg 27) (.const 1)))
    , .assign 29 (.bin .mul (.reg 28) (.reg 4))
    , writeRouteLoopCfgStmt
    , .call 30 bLoop [.reg 21]
    , .cond (.reg 30)
        (.call 31 bSort [.bin .add (.reg 7) (.const 2), .load (.bin .add (.reg 7) (.const 1))])
        .nop
    , .ret (.bin .add (.load (.bin .add (.reg 21) (.const 22))) (.bin .mul (.const 15) (.reg 11))) ]

/-- Top-level `routeOrCut` procedure on flat `MultiPairsAt` inputs
`[gAddr, xAddr, pairsAddr, Δ, L, b, z, outAddr, h]`, matching `multiPairRouterContract` and
`routeOrCutContract`. Builds a `1 + 2 * k`-word `PairsAt` table at `h` and calls `bPairsEntry`
with heap cursor `h + 1 + 2 * k` (so `WalksAt` is written at `h + 1 + 2 * k` inside `[h, h')`). -/
def routeOrCutMultiProc (bPairsEntry : ℕ) : Stmt :=
  seqStmts
    [ .assign 12 (.load (.reg 2))
    , .assign 13 (.reg 8)
    , multiPairsToTableStmt
    , .assign 14 (.bin .add (.bin .add (.reg 8) (.const 1)) (.bin .mul (.const 2) (.reg 12)))
    , .call 15 bPairsEntry [.reg 0, .reg 1, .reg 13, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 14]
    , .ret (.reg 15) ]

theorem routeOrCutPairsProc_noRand (bSort bCsr bPairs bLoop : ℕ) :
    Stmt.NoRand (routeOrCutPairsProc bSort bCsr bPairs bLoop) := by
  unfold routeOrCutPairsProc writeRouteLoopCfgStmt
  repeat (first | apply seqStmts_noRand | constructor | simp)

theorem routeOrCutMultiProc_noRand (bPairsEntry : ℕ) :
    Stmt.NoRand (routeOrCutMultiProc bPairsEntry) := by
  unfold routeOrCutMultiProc multiPairsToTableStmt
  repeat (first | apply seqStmts_noRand | constructor | simp)

/-- Relocatable 14-procedure deterministic module implementing `RouteOrCut`.
* `base + 12` (`routerPairsEntryOff`): `RouteProgLayout` (`PairsAt`) entry, `WalksAt` at `h`.
* `base + 13` (`routerMultiEntryOff`): flat `MultiPairsAt` entry, `WalksAt` at `h + 1 + 2 * k`. -/
def routerPairsEntryOff : ℕ := 12
def routerMultiEntryOff : ℕ := 13

def routerProcs (base : ℕ) : List Stmt :=
  [ siftDownProc                                                 -- base + 0
  , heapSortProc base                                            -- base + 1
  , buildLocalCsrProc (base + 1)                                 -- base + 2
  , buildLocalPairsProc                                          -- base + 3
  , bfsLayersProc                                                -- base + 4
  , dfsBlockProc                                                 -- base + 5
  , shortPathBlockProc (base + 4) (base + 5)                     -- base + 6
  , buildResCsrProc                                              -- base + 7
  , buildCurBProc                                                -- base + 8
  , growBallProc (base + 4)                                      -- base + 9
  , runBatchProc (base + 6) (base + 7) (base + 8) (base + 9)     -- base + 10
  , routeOrCutCsrProc (base + 10)                                -- base + 11
  , routeOrCutPairsProc (base + 1) (base + 2) (base + 3) (base + 11) -- base + 12
  , routeOrCutMultiProc (base + 12) ]                            -- base + 13

theorem routerProcs_noRand (base : ℕ) : ∀ s ∈ routerProcs base, Stmt.NoRand s := by
  intro s hs
  simp only [routerProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact siftDownProc_noRand
  · exact heapSortProc_noRand base
  · exact buildLocalCsrProc_noRand (base + 1)
  · exact buildLocalPairsProc_noRand
  · exact bfsLayersProc_noRand
  · exact dfsBlockProc_noRand
  · exact shortPathBlockProc_noRand (base + 4) (base + 5)
  · exact buildResCsrProc_noRand
  · exact buildCurBProc_noRand
  · exact growBallProc_noRand (base + 4)
  · exact runBatchProc_noRand (base + 6) (base + 7) (base + 8) (base + 9)
  · exact routeOrCutCsrProc_noRand (base + 10)
  · exact routeOrCutPairsProc_noRand (base + 1) (base + 2) (base + 3) (base + 11)
  · exact routeOrCutMultiProc_noRand (base + 12)

/-- Standalone deterministic Word-RAM program containing `routerProcs 0`. -/
def routeOrCutProgram : Program := ⟨routerProcs 0⟩

theorem routeOrCutProgram_noRand : ∀ s ∈ routeOrCutProgram.procs, Stmt.NoRand s :=
  routerProcs_noRand 0

/-! ## 4. Verification of `multiPairsToTableStmt` -/

/-- Offset of pair `j` inside `MultiPairsAt mem pairsAddr pairLists`. -/
def multiPairOff (pairsAddr : ℕ) (pairLists : List (List ℕ × List ℕ)) (j : ℕ) : ℕ :=
  pairsAddr + 1 + ((pairLists.take j).flatMap encodePair).length

private lemma multiPairOff_zero (pairsAddr : ℕ) (pairLists : List (List ℕ × List ℕ)) :
    multiPairOff pairsAddr pairLists 0 = pairsAddr + 1 := by
  simp [multiPairOff]

private lemma multiPairOff_succ (pairsAddr : ℕ) (pairLists : List (List ℕ × List ℕ))
    {j : ℕ} (hj : j < pairLists.length) :
    multiPairOff pairsAddr pairLists (j + 1) =
      multiPairOff pairsAddr pairLists j + 2 + (pairLists[j]'hj).1.length +
        (pairLists[j]'hj).2.length := by
  unfold multiPairOff
  rw [List.take_succ_eq_append_getElem hj, List.flatMap_append, List.flatMap_singleton,
    List.length_append, encodePair_length]
  omega

private lemma multiPairOff_le_end (pairsAddr : ℕ) (pairLists : List (List ℕ × List ℕ))
    {j : ℕ} (_hj : j ≤ pairLists.length) :
    multiPairOff pairsAddr pairLists j ≤ pairsAddr + (encodePairs pairLists).length := by
  unfold multiPairOff encodePairs
  have htake : ((pairLists.take j).flatMap encodePair).length ≤ (pairLists.flatMap encodePair).length := by
    have h := List.take_append_drop j pairLists
    conv_rhs => rw [← h, List.flatMap_append, List.length_append]
    omega
  simp only [List.length_cons]; omega

private lemma multiPairsAt_getElem {mem : ℕ → ℕ} {pairsAddr : ℕ}
    {pairLists : List (List ℕ × List ℕ)} (hmp : MultiPairsAt mem pairsAddr pairLists)
    {j : ℕ} (hj : j < pairLists.length) :
    let off := multiPairOff pairsAddr pairLists j
    SeqAt mem off (pairLists[j]'hj).1 ∧
    SeqAt mem (off + 1 + (pairLists[j]'hj).1.length) (pairLists[j]'hj).2 := by
  unfold MultiPairsAt encodePairs at hmp
  rw [listAt_cons] at hmp
  have hsplit : pairLists = pairLists.take j ++ [pairLists[j]'hj] ++ pairLists.drop (j + 1) := by
    rw [← List.take_succ_eq_append_getElem hj, List.take_append_drop]
  have hflat : ListAt mem (pairsAddr + 1)
      ((pairLists.take j).flatMap encodePair ++
        (encodePair (pairLists[j]'hj) ++ (pairLists.drop (j + 1)).flatMap encodePair)) := by
    have h2 := hmp.2
    rw [hsplit, List.flatMap_append, List.flatMap_append, List.flatMap_singleton,
      List.append_assoc] at h2
    exact h2
  rw [listAt_append] at hflat
  have hrest := hflat.2
  rw [listAt_append] at hrest
  have hp := hrest.1
  change ListAt mem (multiPairOff pairsAddr pairLists j) (encodePair (pairLists[j]'hj)) at hp
  unfold encodePair at hp
  rw [List.cons_append, listAt_cons] at hp
  rcases hp with ⟨hA0, hp⟩
  rw [listAt_append] at hp
  rcases hp with ⟨hA1, hp⟩
  rw [listAt_cons] at hp
  rcases hp with ⟨hB0, hB1⟩
  refine ⟨⟨hA0, hA1⟩, ⟨hB0, ?_⟩⟩
  simpa only [Nat.add_assoc] using hB1

theorem multiPairsToTable_triple {w : ℕ} {p : Program}
    {pairsAddr pTableAddr : ℕ} {pairLists : List (List ℕ × List ℕ)} {st0 : State}
    (hmp : MultiPairsAt st0.mem pairsAddr pairLists)
    (hnd : ∀ pl ∈ pairLists, pl.1.Nodup ∧ pl.2.Nodup)
    (hdisj : pairsAddr + (encodePairs pairLists).length ≤ pTableAddr)
    (hw_pt : pTableAddr + 1 + 2 * pairLists.length + 5 < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    (hr2 : st0.regs 2 = pairsAddr) (hr12 : st0.regs 12 = pairLists.length)
    (hr13 : st0.regs 13 = pTableAddr) :
    Triple w p (fun st => st = st0) multiPairsToTableStmt
      (normalPost fun st' =>
        (∀ r ≤ 13, st'.regs r = st0.regs r) ∧
        PairsAt st'.mem pTableAddr (pairLists.map fun pl => (pl.1.toFinset, pl.2.toFinset)) ∧
        PairsBounded st'.mem pTableAddr (pairLists.map fun pl => (pl.1.toFinset, pl.2.toFinset))
          (pTableAddr + 1 + 2 * pairLists.length) ∧
        (∀ a, ¬ (pTableAddr ≤ a ∧ a < pTableAddr + 1 + 2 * pairLists.length) →
          st'.mem a = st0.mem a))
      (fun _ => 60 * pairLists.length + 30) := by
  set k := pairLists.length
  set pairs := pairLists.map fun pl => (pl.1.toFinset, pl.2.toFinset)
  have hk_def : k = pairLists.length := rfl
  wram_enter
  · subst st
    dsimp only [multiPairsToTableStmt, seqStmts]
    set mem1 := Function.update st0.mem pTableAddr k
    set st1 : State :=
      { mem := mem1
        regs := Function.update (Function.update st0.regs 14 (pairsAddr + 1)) 15 0
        pos := st0.pos }
    have hinit : ∃ c0,
        Runs w p ω
          (seqStmts
            [ .store (.reg 13) (.reg 12)
            , .assign 14 (.bin .add (.reg 2) (.const 1))
            , .assign 15 (.const 0) ])
          st0 .normal st1 c0 ∧ c0 ≤ 15 := by
      have h0 : ∃ o s c0,
          Runs w p ω
            (seqStmts
              [ .store (.reg 13) (.reg 12)
              , .assign 14 (.bin .add (.reg 2) (.const 1))
              , .assign 15 (.const 0) ])
            st0 o s c0 ∧ (o = .normal ∧ s = st1) ∧ 0 + c0 ≤ 15 := by
        dsimp only [seqStmts]
        refine runs_seq_store_le (x := pTableAddr) (v := k) (by eval_expr) (by eval_expr) ?_
        refine runs_seq_assign_le (v := pairsAddr + 1) (by eval_expr) ?_
        refine runs_assign_le (v := 0) (by eval_expr) ⟨rfl, rfl⟩ (by wram_cost)
      rcases h0 with ⟨_, _, c0, h, ⟨rfl, rfl⟩, hc0⟩; exact ⟨c0, h, by omega⟩
    rcases hinit with ⟨c0, hrun0, hc0⟩
    have hloop_ind : ∀ rem j (st : State),
        (hj_rem : j + rem = k) →
        (∀ r ≤ 13, st.regs r = st0.regs r) →
        st.regs 14 = multiPairOff pairsAddr pairLists j →
        st.regs 15 = j →
        st.mem pTableAddr = k →
        (∀ i (hi : i < j),
          let off := multiPairOff pairsAddr pairLists i
          st.mem (pTableAddr + 1 + 2 * i) = off ∧
          st.mem (pTableAddr + 2 + 2 * i) = off + 1 + (pairLists[i]'(by omega)).1.length) →
        (∀ a, ¬ (pTableAddr ≤ a ∧ a < pTableAddr + 1 + 2 * k) → st.mem a = st0.mem a) →
        ∃ stF cF,
          Runs w p ω
            (.loop (.bin .lt (.reg 15) (.reg 12))
              (seqStmts
                [ .store (.bin .add (.bin .add (.reg 13) (.const 1)) (.bin .mul (.const 2) (.reg 15)))
                    (.reg 14)
                , .assign 16 (.load (.reg 14))
                , .assign 14 (.bin .add (.bin .add (.reg 14) (.const 1)) (.reg 16))
                , .store (.bin .add (.bin .add (.reg 13) (.const 2)) (.bin .mul (.const 2) (.reg 15)))
                    (.reg 14)
                , .assign 16 (.load (.reg 14))
                , .assign 14 (.bin .add (.bin .add (.reg 14) (.const 1)) (.reg 16))
                , .assign 15 (.bin .add (.reg 15) (.const 1)) ]))
            st .normal stF cF ∧
          (∀ r ≤ 13, stF.regs r = st0.regs r) ∧
          stF.mem pTableAddr = k ∧
          (∀ i (hi : i < k),
            let off := multiPairOff pairsAddr pairLists i
            stF.mem (pTableAddr + 1 + 2 * i) = off ∧
            stF.mem (pTableAddr + 2 + 2 * i) = off + 1 + (pairLists[i]'(by omega)).1.length) ∧
          (∀ a, ¬ (pTableAddr ≤ a ∧ a < pTableAddr + 1 + 2 * k) → stF.mem a = st0.mem a) ∧
          cF ≤ 60 * rem + 8 := by
      intro rem
      induction rem with
      | zero =>
        intro j st hj hregs hr14 hr15 hmk htab hfr
        have hcond0 : (Expr.bin .lt (.reg 15) (.reg 12)).eval w st = some 0 := by
          have hr12' := (hregs 12 (by decide)).trans hr12
          simp [Expr.eval, BinOp.eval, hr15, hr12', show ¬ j < k by omega, show 0 < 2 ^ w by omega]
        refine ⟨st, _, batch_runs_loop_zero hcond0, hregs, hmk,
          fun i hi => htab i (by omega), hfr, by dsimp only [Expr.size]; omega⟩
      | succ rem ih =>
        intro j st hj hregs hr14 hr15 hmk htab hfr
        have hj_lt : j < pairLists.length := by omega
        have hr12' : st.regs 12 = k := (hregs 12 (by decide)).trans hr12
        have hr13' : st.regs 13 = pTableAddr := (hregs 13 (by decide)).trans hr13
        have hcond1 : (Expr.bin .lt (.reg 15) (.reg 12)).eval w st = some 1 := by
          simp [Expr.eval, BinOp.eval, hr15, hr12', show j < k by omega, show 1 < 2 ^ w by omega]
        have hseq := multiPairsAt_getElem hmp hj_lt
        set offA := multiPairOff pairsAddr pairLists j
        set lenA := (pairLists[j]'hj_lt).1.length
        set offB := offA + 1 + lenA
        set lenB := (pairLists[j]'hj_lt).2.length
        have hoff_next : offB + 1 + lenB = multiPairOff pairsAddr pairLists (j + 1) := by
          rw [multiPairOff_succ pairsAddr pairLists hj_lt]; dsimp only [offB, offA, lenA, lenB]; omega
        have hoff_ub : offB + 1 + lenB ≤ pTableAddr :=
          le_trans (hoff_next ▸ multiPairOff_le_end pairsAddr pairLists (by omega)) hdisj
        have hmA : st.mem offA = lenA := (hfr offA (by omega)).trans hseq.1.1
        have hmB : st.mem offB = lenB := (hfr offB (by omega)).trans hseq.2.1
        set memA := Function.update st.mem (pTableAddr + 1 + 2 * j) offA
        set memB := Function.update memA (pTableAddr + 2 + 2 * j) offB
        set regsB := Function.update (Function.update (Function.update st.regs 16 lenB)
          14 (offB + 1 + lenB)) 15 (j + 1)
        set stB : State := { mem := memB, regs := regsB, pos := st.pos }
        have hbody : ∃ cB,
            Runs w p ω
              (seqStmts
                [ .store (.bin .add (.bin .add (.reg 13) (.const 1)) (.bin .mul (.const 2) (.reg 15)))
                    (.reg 14)
                , .assign 16 (.load (.reg 14))
                , .assign 14 (.bin .add (.bin .add (.reg 14) (.const 1)) (.reg 16))
                , .store (.bin .add (.bin .add (.reg 13) (.const 2)) (.bin .mul (.const 2) (.reg 15)))
                    (.reg 14)
                , .assign 16 (.load (.reg 14))
                , .assign 14 (.bin .add (.bin .add (.reg 14) (.const 1)) (.reg 16))
                , .assign 15 (.bin .add (.reg 15) (.const 1)) ])
              st .normal stB cB ∧ cB ≤ 55 := by
          have hmA' : memA offA = lenA := by
            dsimp only [memA]; rw [Function.update_of_ne (by omega)]; exact hmA
          have hmB' : memB offB = lenB := by
            dsimp only [memB, memA]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hmB
          have h0 : ∃ o s cB,
              Runs w p ω
                (seqStmts
                  [ .store (.bin .add (.bin .add (.reg 13) (.const 1)) (.bin .mul (.const 2) (.reg 15)))
                      (.reg 14)
                  , .assign 16 (.load (.reg 14))
                  , .assign 14 (.bin .add (.bin .add (.reg 14) (.const 1)) (.reg 16))
                  , .store (.bin .add (.bin .add (.reg 13) (.const 2)) (.bin .mul (.const 2) (.reg 15)))
                      (.reg 14)
                  , .assign 16 (.load (.reg 14))
                  , .assign 14 (.bin .add (.bin .add (.reg 14) (.const 1)) (.reg 16))
                  , .assign 15 (.bin .add (.reg 15) (.const 1)) ])
                st o s cB ∧ (o = .normal ∧ s = stB) ∧ 0 + cB ≤ 55 := by
            dsimp only [seqStmts]
            refine runs_seq_store_le (x := pTableAddr + 1 + 2 * j) (v := offA) (by eval_expr) (by eval_expr) ?_
            refine runs_seq_assign_le (v := lenA) (by rw [← hmA']; eval_expr) ?_
            refine runs_seq_assign_le (v := offB) (by eval_expr) ?_
            refine runs_seq_store_le (x := pTableAddr + 2 + 2 * j) (v := offB) (by eval_expr) (by eval_expr) ?_
            refine runs_seq_assign_le (v := lenB) (by rw [← hmB']; eval_expr) ?_
            refine runs_seq_assign_le (v := offB + 1 + lenB) (by eval_expr) ?_
            refine runs_assign_le (v := j + 1) (by eval_expr) ?_ (by wram_cost)
            refine ⟨rfl, ?_⟩
            cases st; simp only [State.mk.injEq, stB, memB, memA, regsB]
            refine ⟨trivial, ?_, trivial⟩
            funext r
            by_cases h15 : r = 15
            · subst h15; simp
            · by_cases h14 : r = 14
              · subst h14; simp
              · by_cases h16 : r = 16
                · subst h16; simp
                · simp [h15, h14, h16]
          rcases h0 with ⟨_, _, cB, h, ⟨rfl, rfl⟩, hcB⟩; exact ⟨cB, h, by omega⟩
        rcases hbody with ⟨cB, hrunB, hcB⟩
        have hfrB : ∀ a, ¬ (pTableAddr ≤ a ∧ a < pTableAddr + 1 + 2 * k) → stB.mem a = st0.mem a := fun a ha => by
          dsimp only [stB, memB, memA]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hfr a ha
        obtain ⟨stF, cF, hrunF, hrF, hmkF, htabF, hfrF, hcF⟩ :=
          ih (j + 1) stB (by omega)
            (fun r hr => by dsimp only [stB, regsB]; rw [Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hregs r hr)
            (by dsimp only [stB, regsB]; rw [Function.update_of_ne (by decide), Function.update_self]; exact hoff_next)
            (by dsimp only [stB, regsB]; rw [Function.update_self])
            (by dsimp only [stB, memB, memA]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hmk)
            (fun i hi => by
              dsimp only [stB, memB, memA]
              by_cases hij : i = j
              · subst hij
                refine ⟨by rw [Function.update_of_ne (by omega), Function.update_self],
                  by rw [Function.update_self]⟩
              · have hi' := htab i (by omega)
                refine ⟨by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hi'.1,
                  by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hi'.2⟩)
            hfrB
        refine ⟨stF, _, batch_runs_loop_step hcond1 (by decide) hrunB hrunF, hrF, hmkF, htabF, hfrF, ?_⟩
        dsimp only [Expr.size]; omega
    obtain ⟨stF, cF, hrunF, hrF, hmkF, htabF, hfrF, hcF⟩ :=
      hloop_ind k 0 st1 (by omega)
        (fun r hr => by dsimp only [st1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
        (by dsimp only [st1]; rw [Function.update_of_ne (by decide), Function.update_self, multiPairOff_zero])
        (by dsimp only [st1]; rw [Function.update_self])
        (by dsimp only [st1, mem1]; rw [Function.update_self])
        (fun _ h => absurd h (Nat.not_lt_zero _))
        (fun a ha => by dsimp only [st1, mem1]; rw [Function.update_of_ne (by omega)])
    obtain ⟨cAll, hrunAll, hcAll⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrun0
      (show Runs w p ω (seqStmts [.loop _ _]) st1 .normal stF cF from hrunF)
    refine ⟨.normal, stF, cAll, hrunAll, ?_, ?_⟩
    · refine ⟨hrF, ⟨by simp [pairs, hmkF, hk_def], fun i hi => ?_⟩, ⟨by simp [pairs, k], fun i hi => ?_⟩, hfrF⟩
      · have hi' : i < pairLists.length := by simpa [pairs] using hi
        have ht := htabF i hi'
        have hseq := multiPairsAt_getElem hmp hi'
        have hndi := hnd (pairLists[i]'hi') (List.getElem_mem hi')
        have hub : multiPairOff pairsAddr pairLists (i + 1) ≤ pTableAddr :=
          le_trans (multiPairOff_le_end pairsAddr pairLists (by omega)) hdisj
        have hsucc := multiPairOff_succ pairsAddr pairLists hi'
        simp only [pairs, List.getElem_map]
        refine ⟨⟨(pairLists[i]'hi').1, hndi.1, rfl, ?_⟩, ⟨(pairLists[i]'hi').2, hndi.2, rfl, ?_⟩⟩
        · rw [ht.1]
          exact seqAt_congr hseq.1 (fun a ha1 ha2 => hfrF a (by omega))
        · rw [ht.2]
          exact seqAt_congr hseq.2 (fun a ha1 ha2 => hfrF a (by omega))
      · have hi' : i < pairLists.length := by simpa [pairs] using hi
        have ht := htabF i hi'
        have hndi := hnd (pairLists[i]'hi') (List.getElem_mem hi')
        have hub : multiPairOff pairsAddr pairLists (i + 1) ≤ pTableAddr :=
          le_trans (multiPairOff_le_end pairsAddr pairLists (by omega)) hdisj
        have hsucc := multiPairOff_succ pairsAddr pairLists hi'
        simp only [pairs, List.getElem_map, List.toFinset_card_of_nodup hndi.1,
          List.toFinset_card_of_nodup hndi.2]
        rw [ht.1, ht.2]; omega
    · simp only [List.length_cons, List.length_nil] at hcAll; omega

/-! ## 5. Verification of `writeRouteLoopCfgStmt` -/

theorem writeRouteLoopCfg_triple {w : ℕ} {p : Program}
    {h n m nX m2 k Δ L b z outAddr initDem rcost : ℕ} {st0 : State}
    (hm2_le : m2 ≤ 2 * m) (hnX_le : nX ≤ n) (hout_h : outAddr + 2 + 2 * n ≤ h)
    (hw_sp : h + routeOrCutPairsHeapSpace n m nX k rcost + 16 < 2 ^ w)
    (hw_par : routeOrCutParamBound m nX k Δ L b z < 2 ^ w)
    (hw16 : 16 < 2 ^ w)
    (hr5 : st0.regs 5 = b) (hr6 : st0.regs 6 = z) (hr7 : st0.regs 7 = outAddr)
    (hr8 : st0.regs 8 = h) (hr10 : st0.regs 10 = m) (hr11 : st0.regs 11 = nX)
    (hr12 : st0.regs 12 = k) (hr14 : st0.regs 14 = wrapCsrWorkAddr h nX)
    (hr15 : st0.regs 15 = m2) (hr17 : st0.regs 17 = wrapPairsWorkAddr h n m nX)
    (hr18 : st0.regs 18 = initDem) (hdem_le : initDem ≤ nX)
    (hr19 : st0.regs 19 = wrapAccHeadAddr h n m nX k)
    (hr20 : st0.regs 20 = wrapAccTailAddr h n m nX k)
    (hr21 : st0.regs 21 = wrapCfgAddr h n m nX k)
    (hr22 : st0.regs 22 = wrapWsAddr h n m nX k)
    (hr23 : st0.regs 23 = wrapCLo h n m nX m2 k)
    (hr24 : st0.regs 24 = wrapPLo h n m nX m2 k)
    (hr26 : st0.regs 26 = routeH Δ b * L)
    (hr27 : st0.regs 27 = routeD Δ b L)
    (hr28 : st0.regs 28 = routeHBatch Δ b L)
    (hr29 : st0.regs 29 = routeR Δ b L) :
    Triple w p (fun st => st = st0) writeRouteLoopCfgStmt
      (normalPost fun st' =>
        st'.regs = st0.regs ∧
        RouteLoopCfgAt st'.mem (wrapCfgAddr h n m nX k)
          (mkWrapLoopCfg h n m nX m2 k Δ L b z outAddr initDem) ∧
        (∀ a, ¬ (wrapCfgAddr h n m nX k ≤ a ∧ a < wrapCfgAddr h n m nX k + 32) →
          st'.mem a = st0.mem a))
      (fun _ => 260) := by
  set cfgAddr := wrapCfgAddr h n m nX k
  set csrW := wrapCsrWorkAddr h nX
  set pairsW := wrapPairsWorkAddr h n m nX
  have hdisj := mkWrapLoopDisj (w := w) (rcost := rcost) hm2_le hnX_le hdem_le hout_h hw_sp hw_par hw16
  have hw_cfg := hdisj.w_cfg
  have hw_off := hdisj.w_off; have hw_nb := hdisj.w_nb; have hw_edge := hdisj.w_edge
  have hw_pb := hdisj.w_pb; have hw_ao := hdisj.w_ao; have hw_al := hdisj.w_al
  have hw_ad := hdisj.w_ad; have hw_ah := hdisj.w_ah; have hw_at := hdisj.w_at
  have hw_ws := hdisj.w_ws; have hw_hp := hdisj.w_hp; have hw_ch := hdisj.w_ch
  have hw_orig := hdisj.w_orig; have hw_out := hdisj.w_out; have hw_walks := hdisj.w_walks
  have hw_d := hdisj.w_d; have hw_hL := hdisj.w_hL; have hw_Hbatch_s := hdisj.w_Hbatch_s
  have hw_R := hdisj.w_R; have hw_z := hdisj.w_z; have hw_b16 := hdisj.w_b16
  have hw_nX4 := hdisj.w_nX4; have hw_m2 := hdisj.w_m2; have hw_k := hdisj.w_k
  dsimp only [mkWrapLoopCfg] at hw_off hw_nb hw_edge hw_pb hw_ao hw_al hw_ad hw_ah hw_at hw_ws hw_orig hw_out hw_walks hw_d hw_hL hw_Hbatch_s hw_R hw_z hw_b16 hw_nX4 hw_m2 hw_k
  have hw_m : 2 * m < 2 ^ w := by
    unfold routeOrCutPairsHeapSpace localCsrSpace at hw_sp; omega
  have hpLo_lt : wrapPLo h n m nX m2 k < 2 ^ w := by
    unfold wrapPHi at hw_hp; omega
  have hcLo_lt : wrapCLo h n m nX m2 k < 2 ^ w := by
    unfold wrapCHi at hw_ch; omega
  have hw_csrw : csrW + 3 * nX + 1 + 2 * m < 2 ^ w := by
    dsimp only [csrEdgeAddr] at hw_edge; omega
  have hw_pw : pairsW + nX + 2 * k + 1 < 2 ^ w := by
    dsimp only [pairsADataAddr] at hw_ad; omega
  wram_enter
  · subst st
    dsimp only [writeRouteLoopCfgStmt, seqStmts]
    refine runs_seq_store_le (x := cfgAddr + 0) (v := nX) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 1) (v := k) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 2) (v := routeD Δ b L) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 3) (v := b) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 4) (v := routeHBatch Δ b L) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 5) (v := csrOffAddr csrW nX) (by eval_expr)
      (by unfold csrOffAddr; eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 6) (v := csrNbAddr csrW nX) (by eval_expr)
      (by unfold csrNbAddr; eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 7) (v := csrEdgeAddr csrW nX m) (by eval_expr)
      (by unfold csrEdgeAddr; eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 8) (v := pairsBAddr pairsW) (by eval_expr)
      (by unfold pairsBAddr; eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 9) (v := pairsAOffAddr pairsW nX) (by eval_expr)
      (by unfold pairsAOffAddr; eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 10) (v := pairsALenAddr pairsW nX k) (by eval_expr)
      (by unfold pairsALenAddr; eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 11) (v := pairsADataAddr pairsW nX k) (by eval_expr)
      (by unfold pairsADataAddr; eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 12) (v := wrapAccHeadAddr h n m nX k) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 13) (v := wrapAccTailAddr h n m nX k) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 14) (v := wrapWsAddr h n m nX k) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 15) (v := m2) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 16) (v := initDem) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 17) (v := 0) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 18) (v := 0) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 19) (v := 0) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 20) (v := 0) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 21) (v := 0) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 22) (v := wrapPLo h n m nX m2 k) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 23) (v := wrapCLo h n m nX m2 k) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 24) (v := 0) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 25) (v := 0) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 26) (v := routeR Δ b L) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 27) (v := z) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 28) (v := routeH Δ b * L) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 29) (v := csrOrigAddr csrW) (by eval_expr)
      (by unfold csrOrigAddr; eval_expr) ?_
    refine runs_seq_store_le (x := cfgAddr + 30) (v := outAddr) (by eval_expr) (by eval_expr) ?_
    refine runs_store_le (x := cfgAddr + 31) (v := h) (by eval_expr) (by eval_expr) ?_ (by wram_cost)
    refine ⟨rfl, ?_, ?_⟩
    · unfold RouteLoopCfgAt BatchCfgAt mkWrapLoopCfg
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals
        dsimp only
        repeat (first | rw [Function.update_self] | rw [Function.update_of_ne (by omega)])
    · intro a ha
      dsimp only
      repeat rw [Function.update_of_ne (by omega)]

end MinCostFlow.ExpanderDecomp
