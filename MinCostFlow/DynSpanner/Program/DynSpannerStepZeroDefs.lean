module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepOut
public import MinCostFlow.DynSpanner.Program.DynSpannerStepZeroAux
public import MinCostFlow.DynSpanner.Program.DynSpannerStepAuxProcs
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPrefix
public import MinCostFlow.DynSpanner.Program.DynSpannerClearBuckets
public import MinCostFlow.DynSpanner.Program.DynSpannerClearAbove
public import MinCostFlow.DynSpanner.Program.DynSpannerInitCore
public import MinCostFlow.DynSpanner.Program.DynSpannerStepHelpers
import WordRAM.Tactic
import Mathlib.Tactic.Ring

/-!
# Level-0 restart branch of Algorithm 6: program and contract (`DynSpannerStepZeroDefs`)

Defines the deterministic Word-RAM procedure `dsStepZeroStmt` for the `j = 0` branch of `step`
(Algorithm 6, Theorem 8.2, page 64), where `chooseLevel L q (t + 1) = 0` triggers a full rebuild
of level `0` on `G' = st.G.applyUpdate u` and clears all levels `i > 0` and all sets `S_i`.

Rather than allocating a second `dsFixedSize L vCap eCap` block for `dsInitAtStmt` (which would
require `ZeroFrom mem b` and add `Θ(L · (vCap + eCap))` copy time and space), `dsStepZeroStmt`
rebuilds in place at handle `b` using `dsInitCoreStmt` (`initProcs` at `initIdxCore`), achieving
the paper's `O(initCore + len + L + G'.n + |E(H)| + |E(H_new)|)` running time with zero
dependence on `vCap` or `eCap`.

Exports:
* `dsStepZeroPrepStmt`, `dsStepZeroClearBody`, `dsStepZeroEmitBody`, `dsStepZeroStmt`,
  `stepZeroProcs`, `stepZeroIdx`, `stepZeroProcs_noRand`.
* `StepZeroBases`, `HasStepZeroProcs`: bundled procedure-table bases and presence proofs.
* `dsStepZeroSpace`, `dsStepZeroCost`, `dsStepZeroContract` (postcondition `StepOutPost` plus
  heap-growth and generation-growth bounds for the batch loop).
* Pure layout arithmetic lemmas `stepZero_layout_eqs` and `stepZero_fixed_order`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## Word-RAM statement bodies -/

/-- Phase 0 of `dsStepZeroStmt`: load header scalars `(L, vCap, eCap)` from `b = r0` and compute
all fixed-block base pointers into `r3..r19`. -/
def dsStepZeroPrepStmt : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
  .assign 6 (.bin .add (.reg 3) (.const 1)) ;;
  .assign 7 (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 4)) (.bin .mul (.const 9) (.reg 5)))) ;;
  .assign 8 (.bin .add (.reg 0) (.const dsHdrSize)) ;;
  .assign 9 (.bin .add (.reg 8) (.reg 7)) ;;
  .assign 10 (.bin .add (.reg 9) (.reg 7)) ;;
  .assign 11 (.bin .add (.reg 10) (.reg 7)) ;;
  .assign 12 (.bin .add (.reg 11) (.reg 5)) ;;
  .assign 13 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 5))) ;;
  .assign 14 (.bin .add (.reg 13) (.reg 6)) ;;
  .assign 15 (.bin .add (.reg 14) (.reg 6)) ;;
  .assign 16 (.bin .add (.reg 15)
    (.bin .add (.reg 6)
      (.bin .add (.bin .mul (.const 2) (.bin .mul (.reg 6) (.reg 5)))
        (.bin .mul (.const 2) (.bin .mul (.reg 6) (.reg 4)))))) ;;
  .assign 17 (.bin .add (.reg 16)
    (.bin .add (.bin .add (.bin .mul (.const 2) (.reg 6)) (.bin .mul (.reg 6) (.reg 4)))
      (.bin .mul (.const 2) (.reg 4)))) ;;
  .assign 18 (.bin .add (.bin .add (.reg 9) (.const 4)) (.bin .mul (.const 7) (.reg 4))) ;;
  .assign 19 (.bin .add (.reg 18) (.reg 5))

/-- First half of Phase 1: measure `u`, apply `dsStepPrefix`, save `oldHEdges`, bump `gen`, and
stamp `eStamp` at `gOld`. -/
def dsStepZeroClearA (bAux bZAux bPref : ℕ) : Stmt :=
  .call 20 (bAux + stepAuxIdxUpdateLen) [.reg 1] ;;
  .assign 21 (.bin .add (.reg 2) (.const 5)) ;;
  .call 22 (bPref + stepPrefixIdx) [.reg 8, .reg 9, .reg 0, .reg 11, .reg 1, .reg 18, .reg 21] ;;
  .assign 23 (.load (.bin .add (.reg 9) (.const dgMOff))) ;;
  .assign 24 (.bin .add (.reg 21) (.reg 20)) ;;
  .call 25 (bAux + stepAuxIdxCopyWords) [.reg 19, .reg 24, .reg 23] ;;
  .assign 26 (.bin .add (.load (.bin .add (.reg 0) (.const dsGenOff))) (.const 1)) ;;
  .store (.bin .add (.reg 0) (.const dsGenOff)) (.reg 26) ;;
  .call 25 (bZAux + stepZeroAuxIdxStampList) [.reg 17, .reg 24, .reg 23, .reg 26]

/-- Second half of Phase 1: clear `H`, clear buckets `0..L` and `minH`, clear `domGen[1..L]` and
`sGen[0..L]`, increment `t`, and set `r27 := heapInit`. -/
def dsStepZeroClearB (bPhase bCB bClrA : ℕ) : Stmt :=
  .call 25 (bPhase + phaseIdxClearAux) [.reg 9] ;;
  .call 25 (bCB + clearBucketsIdx) [.reg 12, .reg 13, .reg 14, .const 0, .reg 6, .reg 11] ;;
  .call 25 (bClrA + clearAboveIdx) [.reg 15, .reg 16, .const 1, .const 0, .reg 6] ;;
  .store (.bin .add (.reg 0) (.const dsTOff))
    (.bin .add (.load (.bin .add (.reg 0) (.const dsTOff))) (.const 1)) ;;
  .assign 27 (.bin .add (.reg 24) (.reg 23))

/-- Phase 1 of `dsStepZeroStmt`: `dsStepZeroClearA ;; dsStepZeroClearB`. -/
def dsStepZeroClearBody (bAux bZAux bPref bPhase bCB bClrA : ℕ) : Stmt :=
  dsStepZeroClearA bAux bZAux bPref ;;
  dsStepZeroClearB bPhase bCB bClrA

/-- Phase 3 of `dsStepZeroStmt` (after `r28 := dsInitCore [b, heapInit]`): write `D` (`E(H₀)`)
at `dPtr = r28`, write `U_H = uhPref ++ uhDel' ++ uhIns'` at `uhPtr = dPtr + |D|`, store the
5-word step header `[uhPtr, |U_H|, uhWords, dPtr, |D|]` at `heapStep`, and return `retFinal`. -/
def dsStepZeroEmitBody (bAux bZAux : ℕ) : Stmt :=
  .assign 29 (.load (.bin .add (.reg 9) (.const dgMOff))) ;;
  .call 30 (bAux + stepAuxIdxCopyWords) [.reg 19, .reg 28, .reg 29] ;;
  .assign 31 (.bin .add (.reg 28) (.reg 29)) ;;
  .call 30 (bAux + stepAuxIdxCopyWords) [.reg 21, .reg 31, .reg 22] ;;
  .assign 32 (.bin .add (.reg 31) (.reg 22)) ;;
  .call 33 (bZAux + stepZeroAuxIdxListDelRecs) [.reg 24, .reg 23, .reg 18, .reg 32] ;;
  .assign 34 (.bin .add (.reg 32) (.bin .mul (.const 2) (.reg 33))) ;;
  .call 35 (bZAux + stepZeroAuxIdxStampInsRecs)
    [.reg 28, .reg 29, .reg 17, .reg 26, .reg 8, .reg 34] ;;
  .cond (.reg 22) (.assign 36 (.const 1)) (.assign 36 (.const 0)) ;;
  .assign 37 (.bin .add (.bin .add (.reg 36) (.reg 33)) (.reg 35)) ;;
  .assign 38 (.bin .add (.bin .add (.reg 22) (.bin .mul (.const 2) (.reg 33)))
    (.bin .mul (.const 4) (.reg 35))) ;;
  .assign 39 (.bin .add (.reg 31) (.reg 38)) ;;
  .store (.reg 2) (.reg 31) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.reg 37) ;;
  .store (.bin .add (.reg 2) (.const 2)) (.reg 38) ;;
  .store (.bin .add (.reg 2) (.const 3)) (.reg 28) ;;
  .store (.bin .add (.reg 2) (.const 4)) (.reg 29) ;;
  .ret (.reg 39)

/-- `args = [b, updPtr, heapStep]`: full level-0 restart step of Algorithm 6 (Theorem 8.2,
page 64), returning `retFinal` and establishing `StepOutPost`. -/
def dsStepZeroStmt (bAux bZAux bPref bPhase bCB bClrA bInit : ℕ) : Stmt :=
  dsStepZeroPrepStmt ;;
  dsStepZeroClearBody bAux bZAux bPref bPhase bCB bClrA ;;
  .call 28 (bInit + initIdxCore) [.reg 0, .reg 27] ;;
  dsStepZeroEmitBody bAux bZAux

/-- Level-0 step module (`1` deterministic procedure). -/
def stepZeroProcs (bAux bZAux bPref bPhase bCB bClrA bInit : ℕ) : List Stmt :=
  [dsStepZeroStmt bAux bZAux bPref bPhase bCB bClrA bInit]

def stepZeroIdx : ℕ := 0

lemma stepZeroProcs_length (bAux bZAux bPref bPhase bCB bClrA bInit : ℕ) :
    (stepZeroProcs bAux bZAux bPref bPhase bCB bClrA bInit).length = 1 := rfl

lemma stepZeroProcs_noRand (bAux bZAux bPref bPhase bCB bClrA bInit : ℕ) :
    ∀ s ∈ stepZeroProcs bAux bZAux bPref bPhase bCB bClrA bInit, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-! ## Bundled procedure-table bases -/

/-- Procedure-table bases needed by `dsStepZeroStmt` and all its callees. -/
structure StepZeroBases where
  bAux : ℕ
  bZAux : ℕ
  bSort : ℕ
  bOps : ℕ
  bEdge : ℕ
  bSplit : ℕ
  bBatch : ℕ
  bGT : ℕ
  bEmit : ℕ
  bFwd : ℕ
  bRevPrim : ℕ
  bRevCore : ℕ
  bRevDyn : ℕ
  bGuest : ℕ
  bSpDyn : ℕ
  bRev : ℕ
  bLW : ℕ
  bPhase : ℕ
  bInit : ℕ
  bF : ℕ
  bR : ℕ
  bD : ℕ
  bU : ℕ
  bPref : ℕ
  bCB : ℕ
  bZ : ℕ
  bClrA : ℕ
  bSZ : ℕ

/-- Proof that program `p` contains all procedures needed by `dsStepZeroStmt` at `bs`. -/
structure HasStepZeroProcs (impl : SparsifyImpl) (p : Program) (bs : StepZeroBases) : Prop where
  hpAux : p.HasAt bs.bAux stepAuxProcs
  hpZAux : p.HasAt bs.bZAux (stepZeroAuxProcs bs.bOps)
  hpSort : p.HasAt bs.bSort (sortProcs bs.bSort)
  hpOps : p.HasAt bs.bOps dgOpsProcs
  hpEdge : p.HasAt bs.bEdge (dgEdgeProcs bs.bOps)
  hpSplit : p.HasAt bs.bSplit (dgSplitProcs bs.bOps bs.bSplit)
  hpBatch : p.HasAt bs.bBatch (dgBatchProcs bs.bOps bs.bEdge bs.bSplit bs.bBatch)
  hpGT : p.HasAt bs.bGT (gtProcs bs.bSort bs.bOps)
  hpEmit : p.HasAt bs.bEmit (gtEmitProcs bs.bSort bs.bOps bs.bGT)
  hpFwd : p.HasAt bs.bFwd (gtForwardProcs bs.bOps bs.bGT bs.bEmit bs.bFwd)
  hpRevPrim : p.HasAt bs.bRevPrim gtRevPrimProcs
  hpRevCore : p.HasAt bs.bRevCore (gtRevCoreProcs bs.bBatch bs.bRevPrim)
  hpRevDyn : p.HasAt bs.bRevDyn (gtRevDynProcs bs.bOps bs.bGT bs.bRevCore)
  hpGuest : p.HasAt bs.bGuest (sparsifyGuestProcs impl bs.bGuest)
  hpSpDyn : p.HasAt bs.bSpDyn
    (sparsifyDynProcs impl.program.regBound impl.cw bs.bFwd bs.bRevDyn bs.bGuest)
  hpRev : p.HasAt bs.bRev (revProcs bs.bOps bs.bRev)
  hpLW : p.HasAt bs.bLW (levelWalkProcs bs.bOps bs.bRev)
  hpPhase : p.HasAt bs.bPhase (phaseProcs bs.bOps bs.bEdge)
  hpInit : p.HasAt bs.bInit (initProcs bs.bOps bs.bEdge bs.bBatch bs.bPhase bs.bLW bs.bSpDyn bs.bInit)
  hpF : p.HasAt bs.bF filterCopyProcs
  hpR : p.HasAt bs.bR (restrictRecProcs bs.bF)
  hpD : p.HasAt bs.bD (levelsDeleteProcs bs.bPhase)
  hpU : p.HasAt bs.bU (applyUProcs bs.bBatch bs.bD)
  hpPref : p.HasAt bs.bPref (stepPrefixProcs bs.bR bs.bU)
  hpCB : p.HasAt bs.bCB clearBucketsProcs
  hpZ : p.HasAt bs.bZ zeroRangeProcs
  hpClrA : p.HasAt bs.bClrA (clearAboveProcs bs.bZ)
  hpSZ : p.HasAt bs.bSZ (stepZeroProcs bs.bAux bs.bZAux bs.bPref bs.bPhase bs.bCB bs.bClrA bs.bInit)

/-! ## Heap space, cost, and contract -/

/-- Upper bound on the heap words allocated above `heapStep` by `dsStepZeroStmt`. -/
noncomputable def dsStepZeroSpace (impl : SparsifyImpl) (mMax vCap eCap : ℕ)
    (G' H_old H_new : MGraph) (len : ℕ) : ℕ :=
  5 + 2 * len + 3 * H_old.m + 5 * H_new.m + dsInitCoreSpaceBound impl mMax vCap eCap G'

/-- Explicit Word-RAM cost bound for `dsStepZeroStmt`. -/
noncomputable def dsStepZeroCost (impl : SparsifyImpl) (mMax L : ℕ)
    (G' H_old H_new : MGraph) (len : ℕ) : ℕ :=
  dsInitCoreCost impl mMax G' + 1350 * len + 675 * H_old.m + 250 * H_new.m +
    30 * G'.n + 90 * (L + 1) + 1500

/-- Contract for `dsStepZeroStmt` (`[b, updPtr, heapStep]`) on update `u = us[k]` when
`chooseLevel L q (k + 1) = 0`. Its postcondition is `StepOutPost` together with explicit upper
bounds on the returned heap pointer and the global generation counter. -/
noncomputable def dsStepZeroContract (G₀ : MGraph) (impl : SparsifyImpl)
    (mMax w L q vCap eCap b k : ℕ) (us : List Update) (u : Update) (len : ℕ)
    (x : DynSpannerMeta L) : Contract where
  pre args mem := ∃ updPtr heapStep,
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let G' := st.G.applyUpdate u
    let H₀ := (initCore G' (canonicalSparsify impl)).1
    args = [b, updPtr, heapStep] ∧
    16 ≤ 2 ^ w ∧ 1 ≤ L ∧ 1 ≤ q ∧
    G₀.IsValid ∧ G₀.m ≤ mMax ∧ G₀.BatchIsValid us ∧ (∀ u' ∈ us, isDelOrSplit u') ∧
    us[k]? = some u ∧
    chooseLevel L q (k + 1) = 0 ∧
    (∀ s ≤ k, SnapInv G₀ L q mMax (canonicalSparsifyParams impl mMax).absorbTime
      (canonicalSparsify impl) us s) ∧
    DynSpannerStateAt L vCap eCap b mem x st ∧
    b + dsFixedSize L vCap eCap ≤ heapStep ∧
    (∀ a, heapFoot x a → a < heapStep) ∧
    ZeroFrom mem heapStep ∧
    heapStep + dsStepZeroSpace impl mMax vCap eCap G' st.H H₀ len < 2 ^ w ∧
    mem (b + dsGenOff) + 2 + G'.m < 2 ^ w ∧
    k + 1 < 2 ^ w ∧
    (G'.E.Nonempty →
      wordSize impl.cw (canonSparsifyInput (activeSubgraph G') (activeSubgraph G') idEmb) ≤ w) ∧
    updPtr + len ≤ heapStep ∧
    (∀ i < len, ¬ metaFoot b x (updPtr + i)) ∧
    (∀ i < len, mem (updPtr + i) < 2 ^ w) ∧
    UpdateAt mem updPtr st.G u len ∧
    UpdateWithinCaps vCap eCap u
  post args mem ret mem' := ∃ updPtr heapStep,
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let G' := st.G.applyUpdate u
    let H₀ := (initCore G' (canonicalSparsify impl)).1
    args = [b, updPtr, heapStep] ∧
    StepOutPost G₀ L q vCap eCap b k impl us u mem x heapStep mem' ret ∧
    heapStep + 5 ≤ ret ∧
    ret ≤ heapStep + dsStepZeroSpace impl mMax vCap eCap G' st.H H₀ len ∧
    mem' (b + dsGenOff) ≤ mem (b + dsGenOff) + 2 + G'.m ∧
    mem' (heapStep + 2) ≤ len + 4 * (step st u (canonicalSparsify impl)).UH.length
  cost _ _ :=
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let G' := st.G.applyUpdate u
    let H₀ := (initCore G' (canonicalSparsify impl)).1
    dsStepZeroCost impl mMax L G' st.H H₀ len

/-! ## Pure layout arithmetic lemmas -/

/-- Exact address identities matching the register assignments in `dsStepZeroPrepStmt`. -/
lemma stepZero_layout_eqs (b L vCap eCap : ℕ) :
    let L1 := L + 1
    let dg := 4 + (7 * vCap + 9 * eCap)
    let gP := b + dsHdrSize
    let hP := gP + dg
    let auxP := hP + dg
    let minH := auxP + dg
    let hNext := minH + eCap
    let hHead := hNext + 2 * eCap
    let hDeg := hHead + L1
    let domG := hDeg + L1
    let sGen := domG + (L1 + (2 * (L1 * eCap) + 2 * (L1 * vCap)))
    let eSt := sGen + ((2 * L1 + L1 * vCap) + 2 * vCap)
    let hPres := (hP + 4) + 7 * vCap
    let hEList := hPres + eCap
    dg = dynGraphSize vCap eCap ∧
    gP = dsGPtr b ∧
    hP = dsHPtr b vCap eCap ∧
    auxP = dsAuxPtr b vCap eCap ∧
    minH = dsMinHBase b vCap eCap ∧
    hNext = dsHNextBase b vCap eCap ∧
    hHead = dsHHeadBase b vCap eCap ∧
    hDeg = dsHDegDummyBase b L vCap eCap ∧
    domG = dsDomGenBase b L vCap eCap ∧
    sGen = dsSGenBase b L vCap eCap ∧
    eSt = dsEStampBase b L vCap eCap ∧
    hPres = dgEPresBase (dsHPtr b vCap eCap) vCap ∧
    hEList = dgEListBase (dsHPtr b vCap eCap) vCap eCap := by
  dsimp only
  refine ⟨by simp [dynGraphSize]; omega, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [dsEStampBase, dsVStampBase, dsSBitBase, dsSHeadBase, dsVSGenBase, dsSGenBase,
    dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase,
    dsHHeadBase, dsHPrevBase, dsHNextBase, dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr, dynGraphSize,
    dgEPresBase, dgEListBase] <;>
  omega

/-- Monotonicity and block-boundary identities for the fixed block `[b, b + dsFixedSize)`. -/
lemma stepZero_fixed_order (b L vCap eCap : ℕ) :
    b + dsGenOff < dsGPtr b ∧
    dsGPtr b + dynGraphSize vCap eCap = dsHPtr b vCap eCap ∧
    dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap ∧
    dsAuxPtr b vCap eCap + dynGraphSize vCap eCap = dsMinHBase b vCap eCap ∧
    dsMinHBase b vCap eCap + eCap = dsHNextBase b vCap eCap ∧
    dsHNextBase b vCap eCap + eCap = dsHPrevBase b vCap eCap ∧
    dsHPrevBase b vCap eCap + eCap = dsHHeadBase b vCap eCap ∧
    dsHHeadBase b vCap eCap + (L + 1) = dsHDegDummyBase b L vCap eCap ∧
    dsHDegDummyBase b L vCap eCap + (L + 1) = dsDomGenBase b L vCap eCap ∧
    dsDomGenBase b L vCap eCap + (L + 1) = dsEdgeDomGenBase b L vCap eCap ∧
    dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap = dsPiPtrBase b L vCap eCap ∧
    dsPiPtrBase b L vCap eCap + (L + 1) * eCap = dsRevGenBase b L vCap eCap ∧
    dsRevGenBase b L vCap eCap + (L + 1) * vCap = dsRevHeadBase b L vCap eCap ∧
    dsRevHeadBase b L vCap eCap + (L + 1) * vCap = dsSGenBase b L vCap eCap ∧
    dsSGenBase b L vCap eCap + (L + 1) = dsVSGenBase b L vCap eCap ∧
    dsVSGenBase b L vCap eCap + (L + 1) * vCap = dsSHeadBase b L vCap eCap ∧
    dsSHeadBase b L vCap eCap + (L + 1) = dsSBitBase b L vCap eCap ∧
    dsSBitBase b L vCap eCap + vCap = dsVStampBase b L vCap eCap ∧
    dsVStampBase b L vCap eCap + vCap = dsEStampBase b L vCap eCap ∧
    dsEStampBase b L vCap eCap + eCap = dsKeptStampBase b L vCap eCap ∧
    dsKeptStampBase b L vCap eCap + eCap = dsMEmbTempBase b L vCap eCap ∧
    dsMEmbTempBase b L vCap eCap + eCap = b + dsFixedSize L vCap eCap :=
  ⟨by simp [dsGenOff, dsGPtr, dsHdrSize], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, dsFixedSize_add b L vCap eCap⟩

/-- Pure address-bounds helper for the fixed block of `DynSpannerStateAt`. -/
theorem stepZero_fixed_lt (b L vCap eCap : ℕ) :
    (∀ off < dsHdrSize, b ≤ b + off ∧ b + off < b + dsFixedSize L vCap eCap) ∧
    (b ≤ dsGPtr b ∧ dsGPtr b + dynGraphSize vCap eCap ≤ b + dsFixedSize L vCap eCap) ∧
    (b ≤ dsHPtr b vCap eCap ∧ dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ b + dsFixedSize L vCap eCap) ∧
    (b ≤ dsAuxPtr b vCap eCap ∧ dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ b + dsFixedSize L vCap eCap) ∧
    (∀ e < eCap, b ≤ dsMinHBase b vCap eCap + e ∧ dsMinHBase b vCap eCap + e < b + dsFixedSize L vCap eCap) ∧
    (∀ e < eCap, b ≤ dsHPrevBase b vCap eCap + e ∧ dsHPrevBase b vCap eCap + e < b + dsFixedSize L vCap eCap) ∧
    (∀ e < eCap, b ≤ dsHNextBase b vCap eCap + e ∧ dsHNextBase b vCap eCap + e < b + dsFixedSize L vCap eCap) ∧
    (∀ i < L + 1, b ≤ dsHHeadBase b vCap eCap + i ∧ dsHHeadBase b vCap eCap + i < b + dsFixedSize L vCap eCap) ∧
    (∀ i < L + 1, b ≤ dsHDegDummyBase b L vCap eCap + i ∧ dsHDegDummyBase b L vCap eCap + i < b + dsFixedSize L vCap eCap) ∧
    (∀ i < L + 1, b ≤ dsDomGenBase b L vCap eCap + i ∧ dsDomGenBase b L vCap eCap + i < b + dsFixedSize L vCap eCap) ∧
    (∀ i < L + 1, ∀ e < eCap, b ≤ dsEdgeDomGenBase b L vCap eCap + i * eCap + e ∧
      dsEdgeDomGenBase b L vCap eCap + i * eCap + e < b + dsFixedSize L vCap eCap) ∧
    (∀ i < L + 1, ∀ e < eCap, b ≤ dsPiPtrBase b L vCap eCap + i * eCap + e ∧
      dsPiPtrBase b L vCap eCap + i * eCap + e < b + dsFixedSize L vCap eCap) ∧
    (∀ i < L + 1, ∀ v < vCap, b ≤ dsRevGenBase b L vCap eCap + i * vCap + v ∧
      dsRevGenBase b L vCap eCap + i * vCap + v < b + dsFixedSize L vCap eCap) ∧
    (∀ i < L + 1, ∀ v < vCap, b ≤ dsRevHeadBase b L vCap eCap + i * vCap + v ∧
      dsRevHeadBase b L vCap eCap + i * vCap + v < b + dsFixedSize L vCap eCap) ∧
    (∀ i < L + 1, b ≤ dsSGenBase b L vCap eCap + i ∧ dsSGenBase b L vCap eCap + i < b + dsFixedSize L vCap eCap) ∧
    (∀ i < L + 1, ∀ v < vCap, b ≤ dsVSGenBase b L vCap eCap + i * vCap + v ∧
      dsVSGenBase b L vCap eCap + i * vCap + v < b + dsFixedSize L vCap eCap) ∧
    (∀ v < vCap, b ≤ dsSBitBase b L vCap eCap + v ∧ dsSBitBase b L vCap eCap + v < b + dsFixedSize L vCap eCap) ∧
    (∀ v < vCap, b ≤ dsVStampBase b L vCap eCap + v ∧ dsVStampBase b L vCap eCap + v < b + dsFixedSize L vCap eCap) ∧
    (∀ e < eCap, b ≤ dsEStampBase b L vCap eCap + e ∧ dsEStampBase b L vCap eCap + e < b + dsFixedSize L vCap eCap) ∧
    (∀ e < eCap, b ≤ dsKeptStampBase b L vCap eCap + e ∧ dsKeptStampBase b L vCap eCap + e < b + dsFixedSize L vCap eCap) := by
  have idx_lt : ∀ {a B c D : ℕ}, a < B → c < D → a * D + c < B * D := by
    intro a B c D ha hc
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hc _)
      (by simpa [Nat.succ_mul] using Nat.mul_le_mul_right D ha)
  obtain ⟨_, hgh, hha, ham, hmn, hnp, hph, hhd, hdd, hde, hep, hpr, hrr, hrs, hsv, hvs, hsh, hsb,
    hve, hek, hkm, hmf⟩ := stepZero_fixed_order b L vCap eCap
  have hb_g : b ≤ dsGPtr b := dsGPtr_ge b
  have h1 : dsGPtr b ≤ dsHPtr b vCap eCap := hgh ▸ Nat.le_add_right _ _
  have h2 : dsHPtr b vCap eCap ≤ dsAuxPtr b vCap eCap := hha ▸ Nat.le_add_right _ _
  have h3 : dsAuxPtr b vCap eCap ≤ dsMinHBase b vCap eCap := ham ▸ Nat.le_add_right _ _
  have h4 : dsMinHBase b vCap eCap ≤ dsHNextBase b vCap eCap := hmn ▸ Nat.le_add_right _ _
  have h5 : dsHNextBase b vCap eCap ≤ dsHPrevBase b vCap eCap := hnp ▸ Nat.le_add_right _ _
  have h6 : dsHPrevBase b vCap eCap ≤ dsHHeadBase b vCap eCap := hph ▸ Nat.le_add_right _ _
  have h7 : dsHHeadBase b vCap eCap ≤ dsHDegDummyBase b L vCap eCap := hhd ▸ Nat.le_add_right _ _
  have h8 : dsHDegDummyBase b L vCap eCap ≤ dsDomGenBase b L vCap eCap := hdd ▸ Nat.le_add_right _ _
  have h9 : dsDomGenBase b L vCap eCap ≤ dsEdgeDomGenBase b L vCap eCap := hde ▸ Nat.le_add_right _ _
  have h10 : dsEdgeDomGenBase b L vCap eCap ≤ dsPiPtrBase b L vCap eCap := hep ▸ Nat.le_add_right _ _
  have h11 : dsPiPtrBase b L vCap eCap ≤ dsRevGenBase b L vCap eCap := hpr ▸ Nat.le_add_right _ _
  have h12 : dsRevGenBase b L vCap eCap ≤ dsRevHeadBase b L vCap eCap := hrr ▸ Nat.le_add_right _ _
  have h13 : dsRevHeadBase b L vCap eCap ≤ dsSGenBase b L vCap eCap := hrs ▸ Nat.le_add_right _ _
  have h14 : dsSGenBase b L vCap eCap ≤ dsVSGenBase b L vCap eCap := hsv ▸ Nat.le_add_right _ _
  have h15 : dsVSGenBase b L vCap eCap ≤ dsSHeadBase b L vCap eCap := hvs ▸ Nat.le_add_right _ _
  have h16 : dsSHeadBase b L vCap eCap ≤ dsSBitBase b L vCap eCap := hsh ▸ Nat.le_add_right _ _
  have h17 : dsSBitBase b L vCap eCap ≤ dsVStampBase b L vCap eCap := hsb ▸ Nat.le_add_right _ _
  have h18 : dsVStampBase b L vCap eCap ≤ dsEStampBase b L vCap eCap := hve ▸ Nat.le_add_right _ _
  have h19 : dsEStampBase b L vCap eCap ≤ dsKeptStampBase b L vCap eCap := hek ▸ Nat.le_add_right _ _
  have h20 : dsKeptStampBase b L vCap eCap ≤ dsMEmbTempBase b L vCap eCap := hkm ▸ Nat.le_add_right _ _
  have h21 : dsMEmbTempBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := hmf ▸ Nat.le_add_right _ _
  have lt_top : ∀ {x y z : ℕ}, x < y → y ≤ z → x < z := lt_of_lt_of_le
  have le_top20 : dsKeptStampBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := h20.trans h21
  have le_top19 : dsEStampBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := h19.trans le_top20
  have le_top18 : dsVStampBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := h18.trans le_top19
  have le_top17 : dsSBitBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := h17.trans le_top18
  have le_top16 : dsSHeadBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := h16.trans le_top17
  have le_top15 : dsVSGenBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := h15.trans le_top16
  have le_top14 : dsSGenBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := h14.trans le_top15
  have le_top13 : dsRevHeadBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := h13.trans le_top14
  have le_top12 : dsRevGenBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := h12.trans le_top13
  have le_top11 : dsPiPtrBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := h11.trans le_top12
  have le_top10 : dsEdgeDomGenBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := h10.trans le_top11
  have le_top9 : dsDomGenBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := h9.trans le_top10
  have le_top8 : dsHDegDummyBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := h8.trans le_top9
  have le_top7 : dsHHeadBase b vCap eCap ≤ b + dsFixedSize L vCap eCap := h7.trans le_top8
  have le_top6 : dsHPrevBase b vCap eCap ≤ b + dsFixedSize L vCap eCap := h6.trans le_top7
  have le_top5 : dsHNextBase b vCap eCap ≤ b + dsFixedSize L vCap eCap := h5.trans le_top6
  have le_top4 : dsMinHBase b vCap eCap ≤ b + dsFixedSize L vCap eCap := h4.trans le_top5
  have le_top3 : dsAuxPtr b vCap eCap ≤ b + dsFixedSize L vCap eCap := h3.trans le_top4
  have le_top2 : dsHPtr b vCap eCap ≤ b + dsFixedSize L vCap eCap := h2.trans le_top3
  have le_top1 : dsGPtr b ≤ b + dsFixedSize L vCap eCap := h1.trans le_top2
  have ge_b1 : b ≤ dsHPtr b vCap eCap := hb_g.trans h1
  have ge_b2 : b ≤ dsAuxPtr b vCap eCap := ge_b1.trans h2
  have ge_b3 : b ≤ dsMinHBase b vCap eCap := ge_b2.trans h3
  have ge_b4 : b ≤ dsHNextBase b vCap eCap := ge_b3.trans h4
  have ge_b5 : b ≤ dsHPrevBase b vCap eCap := ge_b4.trans h5
  have ge_b6 : b ≤ dsHHeadBase b vCap eCap := ge_b5.trans h6
  have ge_b7 : b ≤ dsHDegDummyBase b L vCap eCap := ge_b6.trans h7
  have ge_b8 : b ≤ dsDomGenBase b L vCap eCap := ge_b7.trans h8
  have ge_b9 : b ≤ dsEdgeDomGenBase b L vCap eCap := ge_b8.trans h9
  have ge_b10 : b ≤ dsPiPtrBase b L vCap eCap := ge_b9.trans h10
  have ge_b11 : b ≤ dsRevGenBase b L vCap eCap := ge_b10.trans h11
  have ge_b12 : b ≤ dsRevHeadBase b L vCap eCap := ge_b11.trans h12
  have ge_b13 : b ≤ dsSGenBase b L vCap eCap := ge_b12.trans h13
  have ge_b14 : b ≤ dsVSGenBase b L vCap eCap := ge_b13.trans h14
  have ge_b16 : b ≤ dsSBitBase b L vCap eCap := (ge_b14.trans h15).trans h16
  have ge_b17 : b ≤ dsVStampBase b L vCap eCap := ge_b16.trans h17
  have ge_b18 : b ≤ dsEStampBase b L vCap eCap := ge_b17.trans h18
  have ge_b19 : b ≤ dsKeptStampBase b L vCap eCap := ge_b18.trans h19
  refine ⟨fun off ho => ⟨Nat.le_add_right _ _, lt_top (Nat.add_lt_add_left ho b) le_top1⟩,
    ⟨hb_g, hgh.symm ▸ le_top2⟩, ⟨ge_b1, hha.symm ▸ le_top3⟩, ⟨ge_b2, ham.symm ▸ le_top4⟩,
    fun e he => ⟨ge_b3.trans (Nat.le_add_right _ _), lt_top (hmn ▸ Nat.add_lt_add_left he _) le_top5⟩,
    fun e he => ⟨ge_b5.trans (Nat.le_add_right _ _), lt_top (hph ▸ Nat.add_lt_add_left he _) le_top7⟩,
    fun e he => ⟨ge_b4.trans (Nat.le_add_right _ _), lt_top (hnp ▸ Nat.add_lt_add_left he _) le_top6⟩,
    fun i hi => ⟨ge_b6.trans (Nat.le_add_right _ _), lt_top (hhd ▸ Nat.add_lt_add_left hi _) le_top8⟩,
    fun i hi => ⟨ge_b7.trans (Nat.le_add_right _ _), lt_top (hdd ▸ Nat.add_lt_add_left hi _) le_top9⟩,
    fun i hi => ⟨ge_b8.trans (Nat.le_add_right _ _), lt_top (hde ▸ Nat.add_lt_add_left hi _) le_top10⟩,
    fun i hi e he => ⟨(ge_b9.trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _),
      lt_top (by rw [Nat.add_assoc, ← hep]; exact Nat.add_lt_add_left (idx_lt hi he) _) le_top11⟩,
    fun i hi e he => ⟨(ge_b10.trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _),
      lt_top (by rw [Nat.add_assoc, ← hpr]; exact Nat.add_lt_add_left (idx_lt hi he) _) le_top12⟩,
    fun i hi v hv => ⟨(ge_b11.trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _),
      lt_top (by rw [Nat.add_assoc, ← hrr]; exact Nat.add_lt_add_left (idx_lt hi hv) _) le_top13⟩,
    fun i hi v hv => ⟨(ge_b12.trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _),
      lt_top (by rw [Nat.add_assoc, ← hrs]; exact Nat.add_lt_add_left (idx_lt hi hv) _) le_top14⟩,
    fun i hi => ⟨ge_b13.trans (Nat.le_add_right _ _), lt_top (hsv ▸ Nat.add_lt_add_left hi _) le_top15⟩,
    fun i hi v hv => ⟨(ge_b14.trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _),
      lt_top (by rw [Nat.add_assoc, ← hvs]; exact Nat.add_lt_add_left (idx_lt hi hv) _) le_top16⟩,
    fun v hv => ⟨ge_b16.trans (Nat.le_add_right _ _), lt_top (hsb ▸ Nat.add_lt_add_left hv _) le_top18⟩,
    fun v hv => ⟨ge_b17.trans (Nat.le_add_right _ _), lt_top (hve ▸ Nat.add_lt_add_left hv _) le_top19⟩,
    fun e he => ⟨ge_b18.trans (Nat.le_add_right _ _), lt_top (hek ▸ Nat.add_lt_add_left he _) le_top20⟩,
    fun e he => ⟨ge_b19.trans (Nat.le_add_right _ _), lt_top (hkm ▸ Nat.add_lt_add_left he _) h21⟩⟩

/-- Register invariant after Phase 0 (`dsStepZeroPrepStmt`): `r0..r19` hold the inputs and all
fixed-block base pointers. -/
def StepZeroPrepRegs (b updPtr heapStep L vCap eCap : ℕ) (regs : ℕ → ℕ) : Prop :=
  regs 0 = b ∧ regs 1 = updPtr ∧ regs 2 = heapStep ∧
  regs 3 = L ∧ regs 4 = vCap ∧ regs 5 = eCap ∧ regs 6 = L + 1 ∧
  regs 7 = dynGraphSize vCap eCap ∧
  regs 8 = dsGPtr b ∧ regs 9 = dsHPtr b vCap eCap ∧ regs 10 = dsAuxPtr b vCap eCap ∧
  regs 11 = dsMinHBase b vCap eCap ∧ regs 12 = dsHNextBase b vCap eCap ∧
  regs 13 = dsHHeadBase b vCap eCap ∧ regs 14 = dsHDegDummyBase b L vCap eCap ∧
  regs 15 = dsDomGenBase b L vCap eCap ∧ regs 16 = dsSGenBase b L vCap eCap ∧
  regs 17 = dsEStampBase b L vCap eCap ∧
  regs 18 = dgEPresBase (dsHPtr b vCap eCap) vCap ∧
  regs 19 = dgEListBase (dsHPtr b vCap eCap) vCap eCap

/-- Preserve `StepZeroPrepRegs` whenever registers `< 20` are untouched. -/
lemma stepZeroPrepRegs_of_agree {b updPtr heapStep L vCap eCap : ℕ} {r r' : ℕ → ℕ}
    (hR : StepZeroPrepRegs b updPtr heapStep L vCap eCap r) (hag : ∀ i < 20, r' i = r i) :
    StepZeroPrepRegs b updPtr heapStep L vCap eCap r' := by
  rcases hR with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19⟩
  exact ⟨(hag 0 (by decide)).trans h0, (hag 1 (by decide)).trans h1, (hag 2 (by decide)).trans h2,
    (hag 3 (by decide)).trans h3, (hag 4 (by decide)).trans h4, (hag 5 (by decide)).trans h5,
    (hag 6 (by decide)).trans h6, (hag 7 (by decide)).trans h7, (hag 8 (by decide)).trans h8,
    (hag 9 (by decide)).trans h9, (hag 10 (by decide)).trans h10, (hag 11 (by decide)).trans h11,
    (hag 12 (by decide)).trans h12, (hag 13 (by decide)).trans h13, (hag 14 (by decide)).trans h14,
    (hag 15 (by decide)).trans h15, (hag 16 (by decide)).trans h16, (hag 17 (by decide)).trans h17,
    (hag 18 (by decide)).trans h18, (hag 19 (by decide)).trans h19⟩

/-- Compact boundary inequalities for Phase 1 (`dsStepZeroClearBody`). -/
theorem stepZero_clear_bounds (b L vCap eCap : ℕ) :
    b + dsGenOff < dsGPtr b ∧
    dsGPtr b + dynGraphSize vCap eCap = dsHPtr b vCap eCap ∧
    dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap ∧
    dsAuxPtr b vCap eCap + dynGraphSize vCap eCap = dsMinHBase b vCap eCap ∧
    dsMinHBase b vCap eCap + eCap ≤ dsHNextBase b vCap eCap ∧
    dsHNextBase b vCap eCap ≤ dsHHeadBase b vCap eCap ∧
    dsHHeadBase b vCap eCap + (L + 1) = dsHDegDummyBase b L vCap eCap ∧
    dsHDegDummyBase b L vCap eCap + (L + 1) = dsDomGenBase b L vCap eCap ∧
    dsDomGenBase b L vCap eCap + (L + 1) = dsEdgeDomGenBase b L vCap eCap ∧
    dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap ≤ dsRevGenBase b L vCap eCap ∧
    dsRevGenBase b L vCap eCap + (L + 1) * vCap ≤ dsSGenBase b L vCap eCap ∧
    dsSGenBase b L vCap eCap + (L + 1) = dsVSGenBase b L vCap eCap ∧
    dsVSGenBase b L vCap eCap + (L + 1) * vCap ≤ dsSBitBase b L vCap eCap ∧
    dsSBitBase b L vCap eCap + vCap = dsVStampBase b L vCap eCap ∧
    dsVStampBase b L vCap eCap + vCap = dsEStampBase b L vCap eCap ∧
    dsEStampBase b L vCap eCap + eCap = dsKeptStampBase b L vCap eCap ∧
    dsKeptStampBase b L vCap eCap + eCap ≤ b + dsFixedSize L vCap eCap ∧
    dsHPtr b vCap eCap + dgMOff < dsAuxPtr b vCap eCap ∧
    dgEPresBase (dsHPtr b vCap eCap) vCap + eCap ≤ dsAuxPtr b vCap eCap ∧
    dgEListBase (dsHPtr b vCap eCap) vCap eCap + eCap ≤ dsAuxPtr b vCap eCap := by
  obtain ⟨hgo, hgh, hha, ham, hmn, hnp, hph, hhd, hdd, hde, hep, hpr, hrr, hrs, hsv, hvs, hsh, hsb,
    hve, hek, hkm, hmf⟩ := stepZero_fixed_order b L vCap eCap
  have h1 : dsHNextBase b vCap eCap ≤ dsHHeadBase b vCap eCap :=
    (hnp ▸ Nat.le_add_right _ _).trans (hph ▸ Nat.le_add_right _ _)
  have h2 : dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap ≤ dsRevGenBase b L vCap eCap :=
    hep.symm ▸ (hpr ▸ Nat.le_add_right _ _)
  have h3 : dsRevGenBase b L vCap eCap + (L + 1) * vCap ≤ dsSGenBase b L vCap eCap :=
    hrr.symm ▸ (hrs ▸ Nat.le_add_right _ _)
  have h4 : dsVSGenBase b L vCap eCap + (L + 1) * vCap ≤ dsSBitBase b L vCap eCap :=
    hvs.symm ▸ (hsh ▸ Nat.le_add_right _ _)
  have h5 : dsKeptStampBase b L vCap eCap + eCap ≤ b + dsFixedSize L vCap eCap :=
    hkm.symm ▸ (hmf ▸ Nat.le_add_right _ _)
  have h6 : dsHPtr b vCap eCap + dgMOff < dsAuxPtr b vCap eCap := by
    rw [← hha]; simp only [dgMOff, dynGraphSize]; omega
  have h7 : dgEPresBase (dsHPtr b vCap eCap) vCap + eCap ≤ dsAuxPtr b vCap eCap := by
    rw [← hha]; simp only [dgEPresBase, dynGraphSize]; omega
  have h8 : dgEListBase (dsHPtr b vCap eCap) vCap eCap + eCap ≤ dsAuxPtr b vCap eCap := by
    rw [← hha]; simp only [dgEListBase, dynGraphSize]; omega
  exact ⟨hgo, hgh, hha, ham, hmn ▸ le_rfl, h1, hhd, hdd, hde, h2, h3, hsv, h4, hsb, hve, hek, h5,
    h6, h7, h8⟩

end

private theorem stepZero_prep_bounds {w b L vCap eCap : ℕ}
    (hfix_w : b + dsFixedSize L vCap eCap < 2 ^ w) :
    L + 1 < 2 ^ w ∧ vCap < 2 ^ w ∧ eCap < 2 ^ w ∧
    7 * vCap < 2 ^ w ∧ 9 * eCap < 2 ^ w ∧ 7 * vCap + 9 * eCap < 2 ^ w ∧
    dynGraphSize vCap eCap < 2 ^ w ∧ 2 * eCap < 2 ^ w ∧
    (L + 1) * eCap < 2 ^ w ∧ 2 * ((L + 1) * eCap) < 2 ^ w ∧
    (L + 1) * vCap < 2 ^ w ∧ 2 * ((L + 1) * vCap) < 2 ^ w ∧
    2 * (L + 1) < 2 ^ w ∧ 2 * vCap < 2 ^ w ∧
    (L + 1) + (2 * ((L + 1) * eCap) + 2 * ((L + 1) * vCap)) < 2 ^ w ∧
    2 * ((L + 1) * eCap) + 2 * ((L + 1) * vCap) < 2 ^ w ∧
    2 * (L + 1) + (L + 1) * vCap < 2 ^ w ∧
    (2 * (L + 1) + (L + 1) * vCap) + 2 * vCap < 2 ^ w ∧
    dsHPtr b vCap eCap + 4 < 2 ^ w ∧
    dgEPresBase (dsHPtr b vCap eCap) vCap < 2 ^ w ∧
    dgEListBase (dsHPtr b vCap eCap) vCap eCap < 2 ^ w ∧
    dsGPtr b < 2 ^ w ∧ dsHPtr b vCap eCap < 2 ^ w ∧ dsAuxPtr b vCap eCap < 2 ^ w ∧
    dsMinHBase b vCap eCap < 2 ^ w ∧ dsHNextBase b vCap eCap < 2 ^ w ∧
    dsHHeadBase b vCap eCap < 2 ^ w ∧ dsHDegDummyBase b L vCap eCap < 2 ^ w ∧
    dsDomGenBase b L vCap eCap < 2 ^ w ∧ dsSGenBase b L vCap eCap < 2 ^ w ∧
    dsEStampBase b L vCap eCap < 2 ^ w ∧
    b + dsLOff < 2 ^ w ∧ b + dsVCapOff < 2 ^ w ∧ b + dsECapOff < 2 ^ w := by
  have hfs : dsFixedSize L vCap eCap =
      dsHdrSize + 3 * dynGraphSize vCap eCap + 3 * eCap + 2 * (L + 1) +
      (L + 1) + 2 * ((L + 1) * eCap) + 2 * ((L + 1) * vCap) +
      (L + 1) + (L + 1) * vCap + (L + 1) + 2 * vCap + 3 * eCap := by
    simp only [dsFixedSize, dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase,
      dsSBitBase, dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase,
      dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase,
      dsMinHBase, dsAuxPtr, dsHPtr, dsGPtr, dsHdrSize, dynGraphSize]
    ring
  have hdg : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hlt := stepZero_fixed_lt b L vCap eCap
  have h1 : dsGPtr b < 2 ^ w := lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hlt.2.1.2) hfix_w
  have h2 : dsHPtr b vCap eCap < 2 ^ w := lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hlt.2.2.1.2) hfix_w
  have h3 : dsAuxPtr b vCap eCap < 2 ^ w := lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hlt.2.2.2.1.2) hfix_w
  have h4 : dsHPtr b vCap eCap + dynGraphSize vCap eCap < 2 ^ w := lt_of_le_of_lt hlt.2.2.1.2 hfix_w
  have h5 : dsMinHBase b vCap eCap < 2 ^ w := by
    have : dsMinHBase b vCap eCap = dsAuxPtr b vCap eCap + dynGraphSize vCap eCap := rfl
    exact lt_of_le_of_lt (this ▸ hlt.2.2.2.1.2) hfix_w
  have h6 : dsHHeadBase b vCap eCap < 2 ^ w :=
    lt_of_lt_of_le (hlt.2.2.2.2.2.2.2.1 0 (Nat.zero_lt_succ L)).2 (le_of_lt hfix_w)
  have h7 : dsHDegDummyBase b L vCap eCap < 2 ^ w :=
    lt_of_lt_of_le (hlt.2.2.2.2.2.2.2.2.1 0 (Nat.zero_lt_succ L)).2 (le_of_lt hfix_w)
  have h8 : dsDomGenBase b L vCap eCap < 2 ^ w :=
    lt_of_lt_of_le (hlt.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_lt_succ L)).2 (le_of_lt hfix_w)
  have h9 : dsSGenBase b L vCap eCap < 2 ^ w :=
    lt_of_lt_of_le (hlt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_lt_succ L)).2 (le_of_lt hfix_w)
  have h10 : dsEStampBase b L vCap eCap < 2 ^ w := by
    have := (stepZero_fixed_order b L vCap eCap).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hle : dsEStampBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap :=
      (this.1 ▸ Nat.le_add_right _ _).trans
        ((this.2.1 ▸ Nat.le_add_right _ _).trans (this.2.2 ▸ Nat.le_add_right _ _))
    exact lt_of_le_of_lt hle hfix_w
  have h11 : dsHNextBase b vCap eCap < 2 ^ w := by
    have := (stepZero_fixed_order b L vCap eCap).2.2.2.2.2
    have hle : dsHNextBase b vCap eCap ≤ dsHHeadBase b vCap eCap :=
      (this.1 ▸ Nat.le_add_right _ _).trans (this.2.1 ▸ Nat.le_add_right _ _)
    exact lt_of_le_of_lt hle h6
  have hL_off : b + dsLOff < 2 ^ w := lt_of_lt_of_le (hlt.1 dsLOff (by decide)).2 (le_of_lt hfix_w)
  have hV_off : b + dsVCapOff < 2 ^ w := lt_of_lt_of_le (hlt.1 dsVCapOff (by decide)).2 (le_of_lt hfix_w)
  have hE_off : b + dsECapOff < 2 ^ w := lt_of_lt_of_le (hlt.1 dsECapOff (by decide)).2 (le_of_lt hfix_w)
  have hdg_lt : dynGraphSize vCap eCap < 2 ^ w := by omega
  have hp1 : dgEPresBase (dsHPtr b vCap eCap) vCap < 2 ^ w := by
    simp only [dgEPresBase]; omega
  have hp2 : dgEListBase (dsHPtr b vCap eCap) vCap eCap < 2 ^ w := by
    simp only [dgEListBase]; omega
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, hdg_lt, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, hp1, hp2, h1, h2, h3, h5, h11, h6, h7, h8, h9, h10, hL_off, hV_off, hE_off⟩

public section

/-- Execute `dsStepZeroPrepStmt` in at most `140` steps, leaving memory unchanged and populating
`StepZeroPrepRegs`. -/
theorem stepZero_prep_triple {w b updPtr heapStep L vCap eCap : ℕ} {mem0 : ℕ → ℕ} {p : Program}
    (hw16 : 16 ≤ 2 ^ w) (hfix_w : b + dsFixedSize L vCap eCap < 2 ^ w)
    (hmL : mem0 (b + dsLOff) = L) (hmV : mem0 (b + dsVCapOff) = vCap)
    (hmE : mem0 (b + dsECapOff) = eCap) :
    Triple w p
      (fun st => st.mem = mem0 ∧ st.regs 0 = b ∧ st.regs 1 = updPtr ∧ st.regs 2 = heapStep)
      dsStepZeroPrepStmt
      (normalPost fun st => st.mem = mem0 ∧ StepZeroPrepRegs b updPtr heapStep L vCap eCap st.regs)
      (fun _ => 140) := by
  intro st ω ⟨hm, hr0, hr1, hr2⟩
  subst hm
  have hle := stepZero_layout_eqs b L vCap eCap
  dsimp only at hle
  rcases hle with ⟨hdg, _, hhP, haP, hmH, hnH, hhH, hdH, hdm, hsG, heS, hpH, heL⟩
  obtain ⟨hL_w, hv_w, he_w, h7v, h9e, h79, hdg_w, h2e, hLe, h2Le, hLv, h2Lv, h2L1, h2v,
    hdom_diff, h2Le_2Lv, hs_diff1, hs_diff, hhP4, hhPres_w, hhEList_w,
    hgP_w, hhP_w, haP_w, hmH_w, hnH_w, hhH_w, hdH_w, hdm_w, hsG_w, heS_w, hLo_w, hVo_w, hEo_w⟩ :=
    stepZero_prep_bounds hfix_w
  have hgp_eq : dsGPtr b = b + dsHdrSize := rfl
  have hHdr : dsHdrSize = 6 := rfl
  have hLoff : dsLOff = 2 := rfl
  have hVoff : dsVCapOff = 3 := rfl
  have hEoff : dsECapOff = 4 := rfl
  dsimp only [dsStepZeroPrepStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := L)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr0)
      (Expr.eval_const (by rw [hLoff]; omega)) hLo_w) hmL) ?_
  refine runs_seq_assign_le (v := vCap)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr0]))
      (Expr.eval_const (by rw [hVoff]; omega)) hVo_w) hmV) ?_
  refine runs_seq_assign_le (v := eCap)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr0]))
      (Expr.eval_const (by rw [hEoff]; omega)) hEo_w) hmE) ?_
  refine runs_seq_assign_le (v := L + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) hL_w) ?_
  refine runs_seq_assign_le (v := dynGraphSize vCap eCap)
    (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_const (by omega))
        (Expr.eval_add
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) h7v)
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) h9e) h79)
        (by rw [hdg]; exact hdg_w)) hdg) ?_
  refine runs_seq_assign_le (v := dsGPtr b)
    (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr0]))
        (Expr.eval_const (by rw [hHdr]; omega)) (hgp_eq ▸ hgP_w))
      hgp_eq.symm) ?_
  refine runs_seq_assign_le (v := dsHPtr b vCap eCap)
    (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp))
        (by change dsHPtr b vCap eCap < 2 ^ w; exact hhP_w)) rfl) ?_
  refine runs_seq_assign_le (v := dsAuxPtr b vCap eCap)
    (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp))
        (by change dsAuxPtr b vCap eCap < 2 ^ w; exact haP_w)) rfl) ?_
  refine runs_seq_assign_le (v := dsMinHBase b vCap eCap)
    (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp))
        (by change dsMinHBase b vCap eCap < 2 ^ w; exact hmH_w)) rfl) ?_
  refine runs_seq_assign_le (v := dsHNextBase b vCap eCap)
    (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp))
        (by change dsHNextBase b vCap eCap < 2 ^ w; exact hnH_w)) rfl) ?_
  have hhh_eq : dsHNextBase b vCap eCap + 2 * eCap = dsHHeadBase b vCap eCap := by
    simp only [dsHHeadBase, dsHPrevBase, dsHNextBase]; omega
  refine runs_seq_assign_le (v := dsHHeadBase b vCap eCap)
    (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) h2e)
        (hhh_eq.symm ▸ hhH_w)) hhh_eq) ?_
  refine runs_seq_assign_le (v := dsHDegDummyBase b L vCap eCap)
    (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp))
        (by change dsHDegDummyBase b L vCap eCap < 2 ^ w; exact hdH_w)) rfl) ?_
  refine runs_seq_assign_le (v := dsDomGenBase b L vCap eCap)
    (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp))
        (by change dsDomGenBase b L vCap eCap < 2 ^ w; exact hdm_w)) rfl) ?_
  have hsg_eq : dsDomGenBase b L vCap eCap +
      ((L + 1) + (2 * ((L + 1) * eCap) + 2 * ((L + 1) * vCap))) = dsSGenBase b L vCap eCap := by
    simp only [dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase]; omega
  refine runs_seq_assign_le (v := dsSGenBase b L vCap eCap)
    (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
          (Expr.eval_add
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_mul (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) hLe) h2Le)
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_mul (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) hLv) h2Lv)
            h2Le_2Lv) hdom_diff) (hsg_eq.symm ▸ hsG_w)) hsg_eq) ?_
  have hes_eq : dsSGenBase b L vCap eCap + ((2 * (L + 1) + (L + 1) * vCap) + 2 * vCap) =
      dsEStampBase b L vCap eCap := by
    simp only [dsEStampBase, dsVStampBase, dsSBitBase, dsSHeadBase, dsVSGenBase]; omega
  refine runs_seq_assign_le (v := dsEStampBase b L vCap eCap)
    (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_add
          (Expr.eval_add
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) h2L1)
            (Expr.eval_mul (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) hLv)
            hs_diff1)
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) h2v)
          hs_diff) (hes_eq.symm ▸ heS_w)) hes_eq) ?_
  refine runs_seq_assign_le (v := dgEPresBase (dsHPtr b vCap eCap) vCap)
    (Expr.eval_eq_of_eq
      (Expr.eval_add
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) hhP4)
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) h7v)
        (by simp only [dgEPresBase] at hhPres_w ⊢; exact hhPres_w))
      (by simp only [dgEPresBase])) ?_
  refine runs_assign_le (v := dgEListBase (dsHPtr b vCap eCap) vCap eCap)
    (Expr.eval_eq_of_eq
      (Expr.eval_add (x := dgEPresBase (dsHPtr b vCap eCap) vCap) (y := eCap)
        (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp))
        hhEList_w) rfl) ?_ ?_
  · refine ⟨rfl, ⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp⟩⟩
  · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega

end

end MinCostFlow.DynSpanner.Program
