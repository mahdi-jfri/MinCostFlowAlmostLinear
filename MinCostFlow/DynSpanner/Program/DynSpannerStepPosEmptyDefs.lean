module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosNEGlueA
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosNEGlueB
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosNonEmptyDefs

/-!
# Empty affected-set branch of a `0 < j` step (`DynSpannerStepPosEmpty`)

Implements and verifies `dsStepPosEmptyStmt`, the `E_aff = ∅` branch of Algorithm 6 for `0 < j`.
When `E_aff = ∅`, no sparsification, re-embedding, or `D`-collection is needed: `J = emptyMGraph`,
`H_j = emptyGraphOn G'`, `inDom' j = ∅`, and `res.D = ∅`. The procedure uses the zero-filled
region `[retAff, retAff + eCap)` as both the empty presence bitmask and empty embedding table,
invokes `dsStepFinishStmt` with `jtEList = []` and `eAff = []`, writes `[uhTailHdr, dPtr, 0]`
at `outInfoPtr`, and returns `dPtr`, establishing `StepPosMidPost`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## Procedure body -/

/-- `args = [b, j, eAffPtr, retAff, oldBucketsSum, outInfoPtr]`.
Handles the `E_aff = ∅` branch of a `0 < j` step by calling `dsStepFinishStmt` with empty
`jtEList` and `eAff`, storing `[uhTailHdr, dPtr, 0]` at `outInfoPtr`, and returning `dPtr`. -/
def dsStepPosEmptyStmt (bFin : ℕ) : Stmt :=
  .assign 6 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
  .assign 9 (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 7)) (.bin .mul (.const 9) (.reg 8)))) ;;
  .assign 10 (.bin .add (.reg 0) (.const dsHdrSize)) ;;           -- gPtr
  .assign 11 (.bin .add (.reg 10) (.reg 9)) ;;                    -- hPtr
  .assign 12 (.bin .add (.reg 11) (.reg 9)) ;;                    -- auxPtr
  .assign 13 (.bin .add (.reg 12) (.reg 9)) ;;                    -- minH
  .assign 14 (.bin .add (.reg 13) (.reg 8)) ;;                    -- hNext
  .assign 15 (.bin .add (.reg 14) (.bin .mul (.const 2) (.reg 8))) ;; -- hHead
  .assign 20 (.bin .add (.reg 6) (.const 1)) ;;                   -- L + 1
  .assign 16 (.bin .add (.reg 15) (.reg 20)) ;;                   -- hDeg
  .assign 17 (.bin .add (.reg 16) (.reg 20)) ;;                   -- domGen
  .assign 18 (.bin .add (.reg 17)
    (.bin .add (.reg 20)
      (.bin .add (.bin .mul (.const 2) (.bin .mul (.reg 20) (.reg 8)))
        (.bin .mul (.const 2) (.bin .mul (.reg 20) (.reg 7)))))) ;; -- sGen
  .assign 19 (.bin .add (.bin .add (.reg 11) (.const 4)) (.bin .mul (.const 7) (.reg 7))) ;; -- hPres
  .assign 21 (.bin .add (.reg 3) (.reg 8)) ;;                     -- uhTailHdr = retAff + eCap
  .call 22 (bFin + stepFinishIdx)
    [.reg 14, .reg 15, .reg 16, .reg 1, .reg 20, .reg 3, .bin .add (.reg 21) (.const 1),
     .reg 3, .const 0, .reg 19, .reg 10, .reg 11, .reg 21,
     .reg 14, .reg 15, .reg 16, .reg 1, .reg 20, .reg 13, .reg 0, .reg 3, .const 0,
     .reg 17, .reg 18, .bin .add (.reg 1) (.const 1), .reg 1, .reg 20,
     .reg 0, .reg 1, .reg 2, .const 0, .reg 3, .reg 21] ;;
  .assign 23 (.bin .add (.bin .add (.reg 21) (.const 1)) (.bin .mul (.const 2) (.reg 4))) ;;
  .store (.reg 5) (.reg 21) ;;
  .store (.bin .add (.reg 5) (.const 1)) (.reg 23) ;;
  .store (.bin .add (.reg 5) (.const 2)) (.const 0) ;;
  .ret (.reg 23)

def stepPosEmptyProcs (bFin : ℕ) : List Stmt := [dsStepPosEmptyStmt bFin]

def stepPosEmptyIdx : ℕ := 0

lemma stepPosEmptyProcs_noRand (bFin : ℕ) : ∀ s ∈ stepPosEmptyProcs bFin, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-! ## Input context and contract for the `E_aff = ∅` branch -/

/-- All data and invariants holding right after `dsAffStage` and `dsSumRange` in a `0 < j` step
when `E_aff = ∅`. -/
structure StepPosEmptyCtx where
  G₀ : MGraph
  w : ℕ
  L : ℕ
  q : ℕ
  mMax : ℕ
  vCap : ℕ
  eCap : ℕ
  b : ℕ
  k : ℕ
  impl : SparsifyImpl
  us : List Update
  u : Update
  mem0 : ℕ → ℕ
  mem2 : ℕ → ℕ
  memAff : ℕ → ℕ
  x : DynSpannerMeta L
  headHeap : ℕ
  r₁ : ℕ
  heapStep : ℕ
  heapAff : ℕ
  retAff : ℕ
  sPrevList : List ℕ
  cand : List ℕ
  prefWords : ℕ
  oldBucketsSum : ℕ
  hw16 : 16 ≤ 2 ^ w
  hVG₀ : G₀.IsValid
  hq : 1 ≤ q
  hGm₀ : G₀.m ≤ mMax
  hBV : G₀.BatchIsValid us
  hds : ∀ u' ∈ us, isDelOrSplit u'
  hu_some : us[k]? = some u
  hPref : ∀ s ≤ k, SnapInv G₀ L q mMax (canonicalSparsifyParams impl mMax).absorbTime
    (canonicalSparsify impl) us s
  hj_pos : 0 < chooseLevel L q (k + 1)
  hState : DynSpannerStateAt L vCap eCap b mem0 x
    (runState (L := L) G₀ q (canonicalSparsify impl) us k)
  hGV'_cap : ∀ v ∈ ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u).V,
    v < vCap
  hfix_step : b + dsFixedSize L vCap eCap ≤ heapStep
  hhead_in : heapStep + 5 + prefWords ≤ headHeap ∧ headHeap ≤ r₁ ∧ r₁ ≤ heapAff
  hret_ge : heapAff + 2 + sPrevList.length + cand.length ≤ retAff
  hEnd_ltw : retAff + eCap + 1 + 2 * oldBucketsSum < 2 ^ w
  hGen_ltw : memAff (b + dsGenOff) + 2 < 2 ^ w
  hZeroAff : ZeroFrom memAff retAff
  hOldSum : oldBucketsSum =
    (bucketsCat (fun i => delErase u (if hi : i < L + 1 then x.hBuckets ⟨i, hi⟩ else []))
      (chooseLevel L q (k + 1)) (L + 1 - chooseLevel L q (k + 1))).length
  -- Facts from `dsStepHead` (on `mem2`)
  hG'_graph : DynGraphAt mem2 (dsGPtr b) vCap eCap
    ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u)
  hHmid_graph : DynGraphAt mem2 (dsHPtr b vCap eCap) vCap eCap
    ((runState (L := L) G₀ q (canonicalSparsify impl) us k).H.applyBatch
      (restrictUpdate u (runState (L := L) G₀ q (canonicalSparsify impl) us k).H))
  hBk_mem2 : BucketsAt mem2 L vCap eCap b
    (fun i => delErase u (if hi : i < L + 1 then x.hBuckets ⟨i, hi⟩ else []))
  hmin2 : ∀ e < eCap, mem2 (dsMinHBase b vCap eCap + e) =
    minHAfter u (mem0 (dsMinHBase b vCap eCap + e)) e
  hgen_02 : mem0 (b + dsGenOff) ≤ mem2 (b + dsGenOff)
  hS2_ge : ∀ i : Fin (L + 1), chooseLevel L q (k + 1) ≤ i.1 →
    ∀ v < vCap, mem2 (dsVSGenBase b L vCap eCap + i.1 * vCap + v) ≤ mem2 (b + dsGenOff)
  hHdr_02 : ∀ addr, b ≤ addr → addr < dsGPtr b → addr ≠ b + dsGenOff → mem2 addr = mem0 addr
  hDom_02 : ∀ addr, dsDomGenBase b L vCap eCap ≤ addr → addr < dsSGenBase b L vCap eCap →
    mem2 addr = mem0 addr
  hVSt_02 : ∀ v < vCap, mem2 (dsVStampBase b L vCap eCap + v) ≤ mem2 (b + dsGenOff)
  hKept_02 : ∀ e < eCap, mem2 (dsKeptStampBase b L vCap eCap + e) =
    mem0 (dsKeptStampBase b L vCap eCap + e)
  hFoot_02 : ∀ a, heapFoot x a → mem2 a = mem0 a
  hfoot_lt : ∀ a, heapFoot x a → a < heapStep
  hFrame_02 : ∀ a < heapStep, ¬ metaFoot b x a → mem2 a = mem0 a
  -- Facts from `dsAffStage` (on `memAff`) with `E_aff = ∅`
  hAff_empty :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let j := chooseLevel L q (k + 1)
    let G' := st.G.applyUpdate u
    let H_mid : Fin (L + 1) → MGraph := fun i =>
      (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
    let inDom_mid : Fin (L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
    let S_prev := st.S_level ⟨j - 1, by have := chooseLevel_le L q (k + 1); omega⟩ ∪
      touchedVertices st.G u
    let H_lt := unionGraphLt G' H_mid j
    let piLt_mid := piLtFrom st.Pi_level inDom_mid j
    affectedEdges G' H_lt piLt_mid S_prev = ∅
  hAff_sPrev : ListAt memAff (heapAff + 2) sPrevList
  hAff_aux :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let j := chooseLevel L q (k + 1)
    let G' := st.G.applyUpdate u
    let H_mid : Fin (L + 1) → MGraph := fun i =>
      (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
    let inDom_mid : Fin (L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
    let S_prev := st.S_level ⟨j - 1, by have := chooseLevel_le L q (k + 1); omega⟩ ∪
      touchedVertices st.G u
    let H_lt := unionGraphLt G' H_mid j
    let piLt_mid := piLtFrom st.Pi_level inDom_mid j
    let E_aff := affectedEdges G' H_lt piLt_mid S_prev
    DynGraphAt memAff (dsAuxPtr b vCap eCap) vCap eCap
      (buildProjGraph G' H_lt piLt_mid S_prev E_aff)
  hAff_sBit :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let j := chooseLevel L q (k + 1)
    let S_prev := st.S_level ⟨j - 1, by have := chooseLevel_le L q (k + 1); omega⟩ ∪
      touchedVertices st.G u
    ∀ v < vCap, memAff (dsSBitBase b L vCap eCap + v) = if v ∈ S_prev then 1 else 0
  hAff_gen : memAff (b + dsGenOff) = mem2 (b + dsGenOff) + 1
  hAff_eStamp : ∀ e < eCap, memAff (dsEStampBase b L vCap eCap + e) ≤ memAff (b + dsGenOff)
  hAff_frame : ∀ addr, addr < heapAff → addr ≠ b + dsGenOff →
    (addr < dsAuxPtr b vCap eCap ∨ dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr) →
    (addr < dsSBitBase b L vCap eCap ∨ dsSBitBase b L vCap eCap + vCap ≤ addr) →
    (addr < dsEStampBase b L vCap eCap ∨ dsEStampBase b L vCap eCap + eCap ≤ addr) →
    (addr < dsMEmbTempBase b L vCap eCap ∨ dsMEmbTempBase b L vCap eCap + eCap ≤ addr) →
    memAff addr = mem2 addr

namespace StepPosEmptyCtx

noncomputable abbrev st (ctx : StepPosEmptyCtx) : DynSpannerState ctx.L :=
  runState (L := ctx.L) ctx.G₀ ctx.q (canonicalSparsify ctx.impl) ctx.us ctx.k

noncomputable abbrev res (ctx : StepPosEmptyCtx) : StepOut ctx.L :=
  step ctx.st ctx.u (canonicalSparsify ctx.impl)

abbrev j (ctx : StepPosEmptyCtx) : ℕ := chooseLevel ctx.L ctx.q (ctx.k + 1)

noncomputable abbrev G' (ctx : StepPosEmptyCtx) : MGraph := ctx.st.G.applyUpdate ctx.u

abbrev eAffPtr (ctx : StepPosEmptyCtx) : ℕ :=
  ctx.heapAff + 2 + ctx.sPrevList.length + ctx.cand.length

abbrev uhTailHdr (ctx : StepPosEmptyCtx) : ℕ := ctx.retAff + ctx.eCap

abbrev dPtr (ctx : StepPosEmptyCtx) : ℕ := ctx.uhTailHdr + 1 + 2 * ctx.oldBucketsSum

end StepPosEmptyCtx

/-- Cost bound for `dsStepPosEmptyStmt`. -/
def dsStepPosEmptyCost (L j oldBucketsSum : ℕ) : ℕ :=
  1440 * oldBucketsSum + 150 * (L + 1 - j) + 2100

/-- Contract for `dsStepPosEmptyStmt`. -/
noncomputable def dsStepPosEmptyContract (ctx : StepPosEmptyCtx) : Contract where
  pre args mem :=
    args = [ctx.b, ctx.j, ctx.eAffPtr, ctx.retAff, ctx.oldBucketsSum, ctx.heapStep] ∧
    mem = ctx.memAff
  post _ _ ret mem' :=
    StepPosMidPost ctx.G₀ ctx.L ctx.q ctx.vCap ctx.eCap ctx.b ctx.k ctx.impl ctx.us ctx.u
      ctx.mem0 ctx.mem2 ctx.x ctx.headHeap ctx.r₁ ctx.heapStep ctx.heapAff ctx.sPrevList
      ctx.prefWords mem' ret ∧
    ret = ctx.dPtr
  cost _ _ := dsStepPosEmptyCost ctx.L ctx.j ctx.oldBucketsSum

/-- Bundled procedure bases for `dsStepPosEmptyStmt`. -/
structure HasStepPosEmptyProcs (p : Program) (bs : StepPosNEBases) (bEm : ℕ) : Prop where
  hpOps : p.HasAt bs.bOps dgOpsProcs
  hpEdge : p.HasAt bs.bEdge (dgEdgeProcs bs.bOps)
  hpSplit : p.HasAt bs.bSplit (dgSplitProcs bs.bOps bs.bSplit)
  hpBatch : p.HasAt bs.bBatch (dgBatchProcs bs.bOps bs.bEdge bs.bSplit bs.bBatch)
  hpDR : p.HasAt bs.bDR delRecordsProcs
  hpDA : p.HasAt bs.bDA (delAllProcs bs.bDR)
  hpIR : p.HasAt bs.bIR (insRecordsProcs bs.bOps)
  hpUT : p.HasAt bs.bUT (uhTailProcs bs.bDA bs.bIR)
  hpAU : p.HasAt bs.bAU (applyUHProcs bs.bBatch)
  hpUE : p.HasAt bs.bUE (uhEndProcs bs.bUT bs.bAU)
  hpCB : p.HasAt bs.bCB clearBucketsProcs
  hpPhase : p.HasAt bs.bPhase (phaseProcs bs.bOps bs.bEdge)
  hpFL : p.HasAt bs.bFL (fillLevelProcs bs.bPhase)
  hpRB : p.HasAt bs.bRB (rebuildBucketsProcs bs.bCB bs.bFL)
  hpSE : p.HasAt bs.bSE (stepEndProcs bs.bUE bs.bRB)
  hpZ : p.HasAt bs.bZ zeroRangeProcs
  hpClrA : p.HasAt bs.bClrA (clearAboveProcs bs.bZ)
  hpST : p.HasAt bs.bST (stepTailProcs bs.bSE bs.bClrA)
  hpRev : p.HasAt bs.bRev (revProcs bs.bOps bs.bRev)
  hpLW : p.HasAt bs.bLW (levelWalkProcs bs.bOps bs.bRev)
  hpFin : p.HasAt bs.bFin (stepFinishProcs bs.bST bs.bLW)
  hpEm : p.HasAt bEm (stepPosEmptyProcs bs.bFin)

end

end MinCostFlow.DynSpanner.Program
