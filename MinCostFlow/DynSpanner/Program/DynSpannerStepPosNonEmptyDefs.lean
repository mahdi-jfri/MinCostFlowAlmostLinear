module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepAuxProcs
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosJoinA
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosJoinB
public import MinCostFlow.DynSpanner.Program.DynSpannerSparsifyStage
public import MinCostFlow.DynSpanner.Program.DynSpannerReembStage
public import MinCostFlow.DynSpanner.Program.DynSpannerStepFinish
public import MinCostFlow.DynSpanner.Program.DynSpannerCollectD
import WordRAM.Tactic

/-!
# Nonempty affected-set branch of a `0 < j` step: definitions and glue

Defines `dsStepPosNonEmptyStmt` (the `E_aff ≠ ∅` branch of Algorithm 6 for `0 < j`), the unified
post-branch invariant `StepPosMidPost` shared by both the `E_aff ≠ ∅` and `E_aff = ∅` branches,
and the pure glue lemmas that construct `RSCtx` (for `dsReembStage`) and `DCtx` (for `dsCollectD`)
and assemble `StepPosMidPost` from the five stage postconditions.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## The procedure for the `E_aff ≠ ∅` branch -/

/-- `args = [b, j, eAffPtr, eAffLen, wpPtr, candLen, oldBucketsSum, outInfoPtr]`.
Runs `dsSumWalkLens`, `dsSparsifyStage`, `dsReembStage`, `dsStepFinish`, increments `gen`,
runs `dsCollectD`, stores `[uhTailHdr, dPtr, dLen]` at `outInfoPtr`, and returns
`dPtr + 2 * lenSum + eAffLen` (a `ZeroFrom` upper bound after `dsCollectD`). -/
def dsStepPosNonEmptyStmt (bAux bSS bRS bFin bCD : ℕ) : Stmt :=
  -- Layout constants from header at `b = r0`
  .assign 8 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
  .assign 11 (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 9)) (.bin .mul (.const 9) (.reg 10)))) ;;
  .assign 12 (.bin .add (.reg 0) (.const dsHdrSize)) ;;        -- gPtr
  .assign 13 (.bin .add (.reg 12) (.reg 11)) ;;                  -- hPtr
  .assign 14 (.bin .add (.reg 13) (.reg 11)) ;;                  -- auxPtr
  .assign 15 (.bin .add (.reg 14) (.reg 11)) ;;                  -- minH
  .assign 16 (.bin .add (.reg 15) (.reg 10)) ;;                  -- hNext
  .assign 17 (.bin .add (.reg 16) (.bin .mul (.const 2) (.reg 10))) ;; -- hHead
  .assign 40 (.bin .add (.reg 8) (.const 1)) ;;                  -- L + 1
  .assign 18 (.bin .add (.reg 17) (.reg 40)) ;;                  -- hDeg
  .assign 19 (.bin .add (.reg 18) (.reg 40)) ;;                  -- domGen
  .assign 20 (.bin .add (.reg 19)
    (.bin .add (.reg 40)
      (.bin .add (.bin .mul (.const 2) (.bin .mul (.reg 40) (.reg 10)))
        (.bin .mul (.const 2) (.bin .mul (.reg 40) (.reg 9)))))) ;; -- sGen
  .assign 21 (.bin .add (.reg 20)
    (.bin .add (.bin .mul (.const 2) (.reg 40)) (.bin .mul (.reg 40) (.reg 9)))) ;; -- sBit
  .assign 22 (.bin .add (.reg 21) (.bin .mul (.const 2) (.reg 9))) ;; -- eStamp
  .assign 23 (.bin .add (.reg 22) (.bin .mul (.const 2) (.reg 10))) ;; -- mEmbTemp
  -- 1. `lenSum := dsSumWalkLens [wpPtr, eAffLen]`
  .call 24 (bAux + stepAuxIdxSumWalkLens) [.reg 4, .reg 3] ;;
  -- 2. `scratchPtr`, `jN`, `guestBase`
  .assign 25 (.bin .add (.bin .add (.reg 4) (.reg 3))
    (.bin .add (.bin .mul (.const 14) (.reg 24))
      (.bin .add (.bin .mul (.const 15) (.reg 3)) (.reg 5)))) ;;
  .assign 26 (.load (.bin .add (.reg 14) (.const dgNOff))) ;;
  .assign 27 (.bin .add (.reg 25)
    (.bin .add (.const 8)
      (.bin .add (.bin .mul (.const 3) (.reg 26))
        (.bin .add (.bin .mul (.const 11) (.reg 3)) (.bin .mul (.const 10) (.reg 24)))))) ;;
  -- 3. `dsSparsifyStage`
  .call 28 (bSS + sparsifyStageIdx)
    [.reg 12, .reg 14, .reg 23, .reg 9, .reg 10, .reg 25, .reg 27, .reg 0, .reg 2, .reg 3] ;;
  .assign 29 (.load (.reg 25)) ;;                                -- jtPtr
  .assign 30 (.load (.bin .add (.reg 25) (.const 1))) ;;         -- qTab
  -- 4. `dsReembStage`
  .assign 31 (.bin .add (.reg 28) (.reg 10)) ;;                  -- heapReemb = piTab + eCap
  .call 32 (bRS + reembStageIdx)
    [.reg 12, .reg 21, .reg 23, .reg 28, .reg 2, .reg 3, .reg 4, .reg 30, .reg 31] ;;
  -- 5. `heapFin`, `uhTailHdr`, `jtM`, `jtPres`, `jtEList`, `hPres`
  .assign 33 (.bin .sub (.reg 32) (.reg 31)) ;;                  -- reembDelta
  .assign 34 (.bin .add (.reg 31)
    (.bin .add (.bin .mul (.const 16) (.reg 3))
      (.bin .add (.bin .mul (.const 14) (.reg 24)) (.bin .mul (.const 3) (.reg 33))))) ;;
  .assign 35 (.bin .add (.reg 34) (.bin .mul (.const 2) (.reg 33))) ;; -- uhTailHdr
  .assign 36 (.load (.bin .add (.reg 29) (.const dgMOff))) ;;    -- jtM
  .assign 37 (.bin .add (.bin .add (.reg 29) (.const 4)) (.bin .mul (.const 7) (.reg 9))) ;;
  .assign 38 (.bin .add (.reg 37) (.reg 10)) ;;                  -- jtEList
  .assign 39 (.bin .add (.bin .add (.reg 13) (.const 4)) (.bin .mul (.const 7) (.reg 9))) ;;
  -- 6. `dsStepFinish` (33 args)
  .call 41 (bFin + stepFinishIdx)
    [.reg 16, .reg 17, .reg 18, .reg 1, .reg 40, .reg 37, .bin .add (.reg 35) (.const 1),
     .reg 38, .reg 36, .reg 39, .reg 12, .reg 13, .reg 35,
     .reg 16, .reg 17, .reg 18, .reg 1, .reg 40, .reg 15, .reg 0, .reg 38, .reg 36,
     .reg 19, .reg 20, .bin .add (.reg 1) (.const 1), .reg 1, .reg 40,
     .reg 0, .reg 1, .reg 2, .reg 3, .reg 28, .reg 34] ;;
  -- 7. `dPtr`, bump `gen`, `dsCollectD`
  .assign 42 (.bin .add (.bin .add (.reg 35) (.const 1))
    (.bin .add (.bin .mul (.const 2) (.reg 6)) (.bin .mul (.const 4) (.reg 36)))) ;;
  .assign 43 (.bin .add (.load (.bin .add (.reg 0) (.const dsGenOff))) (.const 1)) ;;
  .store (.bin .add (.reg 0) (.const dsGenOff)) (.reg 43) ;;
  .call 44 (bCD + collectDIdx) [.reg 38, .reg 36, .reg 23, .reg 22, .reg 43, .reg 42] ;;
  -- 8. Store `[uhTailHdr, dPtr, dLen]` at `outInfoPtr = r7` and return `dPtr + 2 * lenSum + eAffLen`
  .store (.reg 7) (.reg 35) ;;
  .store (.bin .add (.reg 7) (.const 1)) (.reg 42) ;;
  .store (.bin .add (.reg 7) (.const 2)) (.reg 44) ;;
  .ret (.bin .add (.reg 42) (.bin .add (.bin .mul (.const 2) (.reg 24)) (.reg 3)))

def stepPosNonEmptyProcs (bAux bSS bRS bFin bCD : ℕ) : List Stmt :=
  [dsStepPosNonEmptyStmt bAux bSS bRS bFin bCD]

def stepPosNonEmptyIdx : ℕ := 0

lemma stepPosNonEmptyProcs_noRand (bAux bSS bRS bFin bCD : ℕ) :
    ∀ s ∈ stepPosNonEmptyProcs bAux bSS bRS bFin bCD, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-! ## Unified post-branch invariant `StepPosMidPost` -/

/-- The facts of `StepPosMidPost` for given witnesses: the header pointer `uhTailHdr` of the
records of `U_H`, the pointer `dPtr` of the list `dL` of `D`, the context `c` of the records, the
context `r` of the bucket rebuild, and the reverse lists `revJ` of level `j`. Among them is an
upper bound on the generation word: `mem gen ≤ mem2 gen + 3 + |E_aff|`, where `mem2` is the
memory after `dsStepHead`. -/
abbrev StepPosMidBody (G₀ : MGraph) (L q vCap eCap b k : ℕ) (impl : SparsifyImpl)
    (us : List Update) (u : Update) (mem0 mem2 : ℕ → ℕ) (x : DynSpannerMeta L)
    (headHeap r₁ heapStep heapAff : ℕ)
    (sPrevList : List ℕ) (prefWords : ℕ) (mem : ℕ → ℕ) (nextHeap : ℕ)
    (uhTailHdr dPtr : ℕ) (c : UTCtx) (r : RBCtx) (revJ : ℕ → List ℕ) (dL : List ℕ) : Prop :=
  let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
  let res := step st u (canonicalSparsify impl)
  let j := chooseLevel L q (k + 1)
  let jF : Fin (L + 1) := ⟨j, by have := chooseLevel_le L q (k + 1); omega⟩
  let G' := st.G.applyUpdate u
  let H_mid : Fin (L + 1) → MGraph := fun i => (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
  let inDom_mid : Fin (L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
  let S_prev := st.S_level ⟨j - 1, by have := chooseLevel_le L q (k + 1); omega⟩ ∪ touchedVertices st.G u
  let H_lt := unionGraphLt G' H_mid j
  let piLt_mid := piLtFrom st.Pi_level inDom_mid j
  let E_aff := affectedEdges G' H_lt piLt_mid S_prev
  let J := buildProjGraph G' H_lt piLt_mid S_prev E_aff
  mem heapStep = uhTailHdr ∧ mem (heapStep + 1) = dPtr ∧ mem (heapStep + 2) = dL.length ∧
  heapAff + 2 + sPrevList.length ≤ uhTailHdr ∧ uhTailHdr + 1 + c.size ≤ dPtr ∧ dPtr + dL.length ≤ nextHeap ∧
  ZeroFrom mem nextHeap ∧
  mem uhTailHdr = c.recs.length ∧
  (∀ K : MGraph, BatchBodyAt mem (uhTailHdr + 1) K c.recs c.words) ∧
  (restrictUpdate u st.H ++ c.recs).Perm res.UH ∧
  (∀ u' ∈ c.recs, isDelOrIns u') ∧
  dL.Nodup ∧ dL.toFinset = res.D ∧ ListAt mem dPtr dL ∧
  r.L = L ∧ r.vCap = vCap ∧ r.eCap = eCap ∧ r.b = b ∧ r.j = j ∧
  mem (b + dsQOff) = st.q ∧ mem (b + dsTOff) = st.t ∧
  mem (b + dsLOff) = L ∧ mem (b + dsVCapOff) = vCap ∧ mem (b + dsECapOff) = eCap ∧
  1 ≤ mem (b + dsGenOff) ∧ mem2 (b + dsGenOff) ≤ mem (b + dsGenOff) ∧
  mem (b + dsGenOff) ≤ mem2 (b + dsGenOff) + 3 + E_aff.card ∧
  DynGraphAt mem (dsGPtr b) vCap eCap res.state.G ∧
  DynGraphAt mem (dsHPtr b vCap eCap) vCap eCap res.state.H ∧
  DynGraphAt mem (dsAuxPtr b vCap eCap) vCap eCap J ∧
  BucketsAt mem L vCap eCap b r.newB ∧
  (∀ e < eCap,
    (mem (dsMinHBase b vCap eCap + e) = 0 ↔ e ∉ res.state.H.E) ∧
    (e ∈ res.state.H.E → ∃ i : Fin (L + 1),
      mem (dsMinHBase b vCap eCap + e) = i.1 + 1 ∧
      e ∈ (res.state.H_level i).E ∧
      ∀ k' : Fin (L + 1), k'.1 < i.1 → e ∉ (res.state.H_level k').E)) ∧
  (∀ i : Fin (L + 1), ∀ e, e ∈ r.newB i.1 ↔
    e ∈ res.state.H.E ∧ mem (dsMinHBase b vCap eCap + e) = i.1 + 1) ∧
  (∀ i : Fin (L + 1), i.1 < j →
    mem (dsDomGenBase b L vCap eCap + i.1) = mem0 (dsDomGenBase b L vCap eCap + i.1) ∧
    (∀ e < eCap,
      mem (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) =
        mem0 (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) ∧
      mem (dsPiPtrBase b L vCap eCap + i.1 * eCap + e) =
        mem0 (dsPiPtrBase b L vCap eCap + i.1 * eCap + e)) ∧
    (∀ v < vCap,
      mem (dsRevGenBase b L vCap eCap + i.1 * vCap + v) =
        mem0 (dsRevGenBase b L vCap eCap + i.1 * vCap + v) ∧
      mem (dsRevHeadBase b L vCap eCap + i.1 * vCap + v) =
        mem0 (dsRevHeadBase b L vCap eCap + i.1 * vCap + v))) ∧
  (∀ a, heapFoot x a → mem a = mem0 a) ∧
  (0 < mem (dsDomGenBase b L vCap eCap + j) ∧
    mem (dsDomGenBase b L vCap eCap + j) ≤ mem (b + dsGenOff) ∧
    (∀ e < eCap,
      mem (dsEdgeDomGenBase b L vCap eCap + j * eCap + e) ≤ mem (b + dsGenOff) ∧
      ((0 < mem (dsDomGenBase b L vCap eCap + j) ∧
        mem (dsEdgeDomGenBase b L vCap eCap + j * eCap + e) =
          mem (dsDomGenBase b L vCap eCap + j)) ↔ e ∈ res.state.inDom jF)) ∧
    (∀ e ∈ res.state.inDom jF,
      let ptr := mem (dsPiPtrBase b L vCap eCap + j * eCap + e)
      MWalkAt mem ptr (res.state.Pi_level jF e) ∧
      heapStep + 5 ≤ ptr ∧ ptr + (mWalkEncode (res.state.Pi_level jF e)).length ≤ nextHeap) ∧
    (∀ v < vCap,
      mem (dsRevGenBase b L vCap eCap + j * vCap + v) ≤ mem (b + dsGenOff) ∧
      (revJ v).Nodup ∧
      (∀ e, e ∈ revJ v ↔ e ∈ res.state.inDom jF ∧
        v ∈ res.state.H.walkVertices (res.state.G.tail e) (res.state.Pi_level jF e)) ∧
      (if 0 < mem (dsDomGenBase b L vCap eCap + j) ∧
          mem (dsRevGenBase b L vCap eCap + j * vCap + v) =
            mem (dsDomGenBase b L vCap eCap + j)
       then LinkedListIn (fun a => heapStep + 5 ≤ a ∧ a < nextHeap) mem
              (mem (dsRevHeadBase b L vCap eCap + j * vCap + v)) (revJ v)
       else revJ v = []))) ∧
  (∀ i : Fin (L + 1), j < i.1 →
    mem (dsDomGenBase b L vCap eCap + i.1) = 0 ∧
    (∀ e < eCap, mem (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) =
      mem0 (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e)) ∧
    (∀ v < vCap, mem (dsRevGenBase b L vCap eCap + i.1 * vCap + v) =
      mem0 (dsRevGenBase b L vCap eCap + i.1 * vCap + v))) ∧
  (∀ i : Fin (L + 1),
    if i.1 < j then
      mem (dsSGenBase b L vCap eCap + i.1) = mem2 (dsSGenBase b L vCap eCap + i.1) ∧
      mem (dsSHeadBase b L vCap eCap + i.1) = mem2 (dsSHeadBase b L vCap eCap + i.1) ∧
      (∀ v < vCap, mem (dsVSGenBase b L vCap eCap + i.1 * vCap + v) =
        mem2 (dsVSGenBase b L vCap eCap + i.1 * vCap + v)) ∧
      (∀ a, headHeap ≤ a → a < r₁ → mem a = mem2 a)
    else
      mem (dsSGenBase b L vCap eCap + i.1) = 0 ∧
      mem (dsSHeadBase b L vCap eCap + i.1) = mem2 (dsSHeadBase b L vCap eCap + i.1) ∧
      (∀ v < vCap, mem (dsVSGenBase b L vCap eCap + i.1 * vCap + v) =
        mem2 (dsVSGenBase b L vCap eCap + i.1 * vCap + v))) ∧
  (∀ v < vCap,
    mem (dsSBitBase b L vCap eCap + v) = (if v ∈ S_prev then 1 else 0) ∧
    mem (dsVStampBase b L vCap eCap + v) ≤ mem (b + dsGenOff)) ∧
  (∀ e < eCap,
    mem (dsEStampBase b L vCap eCap + e) ≤ mem (b + dsGenOff) ∧
    mem (dsKeptStampBase b L vCap eCap + e) = mem0 (dsKeptStampBase b L vCap eCap + e)) ∧
  (∀ a, heapStep + 5 ≤ a → a < heapStep + 5 + prefWords → mem a = mem2 a) ∧
  ListAt mem (heapAff + 2) sPrevList ∧
  (∀ a < heapStep, ¬ metaFoot b x a → mem a = mem0 a)

/-- Unified postcondition produced by both the `E_aff ≠ ∅` and `E_aff = ∅` branches of a `0 < j`
step, right before the common epilogue (`dsClearSBit`, `clearAuxGraph`, `t++`, `U_H` pack, header). -/
def StepPosMidPost (G₀ : MGraph) (L q vCap eCap b k : ℕ) (impl : SparsifyImpl)
    (us : List Update) (u : Update) (mem0 mem2 : ℕ → ℕ) (x : DynSpannerMeta L)
    (headHeap r₁ heapStep heapAff : ℕ)
    (sPrevList : List ℕ) (prefWords : ℕ) (mem : ℕ → ℕ) (nextHeap : ℕ) : Prop :=
  ∃ (uhTailHdr dPtr : ℕ) (c : UTCtx) (r : RBCtx) (revJ : ℕ → List ℕ) (dL : List ℕ),
    StepPosMidBody G₀ L q vCap eCap b k impl us u mem0 mem2 x headHeap r₁ heapStep heapAff
      sPrevList prefWords mem nextHeap uhTailHdr dPtr c r revJ dL

/-! ## Heap upper bound and cost of `dsStepPosNonEmptyStmt` -/

/-- Upper bound on the final heap pointer returned by `dsStepPosNonEmptyStmt`. -/
noncomputable def dsStepPosNonEmptyEnd (impl : SparsifyImpl) (mMax vCap eCap : ℕ)
    (G' J : MGraph) (piLt_mid embJH : Embedding) (eAff : List ℕ)
    (wpPtr candLen oldBucketsSum : ℕ) : ℕ :=
  let lenSum := (eAff.map fun e => (piLt_mid e).length).sum
  let eLen := eAff.length
  let out := canonicalSparsify impl G' J embJH
  let outEmb : Embedding := fun e => shortcutWalk out.Jtilde (J.tail e) (out.emb e)
  let scratchPtr := wpPtr + eLen + 14 * lenSum + 15 * eLen + candLen
  let guestBase := scratchPtr + 8 + 3 * J.n + 11 * eLen + 10 * lenSum
  let spEnd := spOutBound impl mMax vCap eCap guestBase G' J embJH +
    dsShortcutHeapSpace eAff out.emb
  let reembN := reembStageNeed piLt_mid embJH outEmb eAff
  spEnd + eCap + 16 * eLen + 14 * lenSum + 5 * reembN + 1 + 2 * oldBucketsSum +
    4 * out.Jtilde.m + 2 * lenSum + eLen

/-- Explicit cost bound of `dsStepPosNonEmptyStmt`. -/
noncomputable def dsStepPosNonEmptyCost (impl : SparsifyImpl) (mMax L vCap eCap j : ℕ)
    (G' J : MGraph) (piLt_mid embJH : Embedding) (S_prev : Finset ℕ) (eAff : List ℕ)
    (oldBucketsSum : ℕ) : ℕ :=
  let out := canonicalSparsify impl G' J embJH
  let outEmb : Embedding := fun e => shortcutWalk out.Jtilde (J.tail e) (out.emb e)
  let embMid := Embedding.comp embJH outEmb
  let lenSum := (eAff.map fun e => (piLt_mid e).length).sum
  let spCost := (dsSparsifyStageContract impl mMax 0 vCap eCap vCap eCap vCap eCap L vCap eCap 0
    G' J embJH eAff).cost [] 0
  let reembCost := compAllCost embJH outEmb eAff + reembedAllCost piLt_mid embMid eAff + 40
  let finCost := 100 * oldBucketsSum + 150 * (L + 1 - j) + 420 * out.Jtilde.m +
    670 * (2 * oldBucketsSum + 4 * out.Jtilde.m) +
    400 * (eAff.map fun e => (reembedWalk G' G' piLt_mid embMid S_prev e).length).sum +
    620 * eAff.length + 1800
  let dCost := 50 * (2 * lenSum + eAff.length) + 50 * out.Jtilde.m + 20
  35 * eAff.length + 25 + spCost + reembCost + finCost + dCost + 600

/-! ## Bundled procedure-table bases for the nonempty branch -/

/-- Procedure-table bases needed by `dsStepPosNonEmptyStmt` and its callees. -/
structure StepPosNEBases where
  bAux : ℕ
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
  bSS : ℕ
  bEmb : ℕ
  bC : ℕ
  bCA : ℕ
  bRe : ℕ
  bRA : ℕ
  bRS : ℕ
  bDR : ℕ
  bDA : ℕ
  bIR : ℕ
  bUT : ℕ
  bAU : ℕ
  bUE : ℕ
  bCB : ℕ
  bPhase : ℕ
  bFL : ℕ
  bRB : ℕ
  bSE : ℕ
  bZ : ℕ
  bClrA : ℕ
  bST : ℕ
  bFin : ℕ
  bCD : ℕ
  bNE : ℕ

/-- Proof that program `p` contains all procedures needed by `dsStepPosNonEmptyStmt` at `bs`. -/
structure HasStepPosNEProcs (impl : SparsifyImpl) (p : Program) (bs : StepPosNEBases) : Prop where
  hpAux : p.HasAt bs.bAux stepAuxProcs
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
  hpSS : p.HasAt bs.bSS (sparsifyStageProcs bs.bSpDyn bs.bLW)
  hpEmb : p.HasAt bs.bEmb (embOpsProcs bs.bOps)
  hpC : p.HasAt bs.bC (compProcs bs.bEmb)
  hpCA : p.HasAt bs.bCA (compAllProcs bs.bC)
  hpRe : p.HasAt bs.bRe (reembedProcs bs.bEmb)
  hpRA : p.HasAt bs.bRA (reembedAllProcs bs.bOps bs.bRe)
  hpRS : p.HasAt bs.bRS (reembStageProcs bs.bCA bs.bRA)
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
  hpFin : p.HasAt bs.bFin (stepFinishProcs bs.bST bs.bLW)
  hpCD : p.HasAt bs.bCD collectDProcs
  hpNE : p.HasAt bs.bNE (stepPosNonEmptyProcs bs.bAux bs.bSS bs.bRS bs.bFin bs.bCD)

/-! ## Pure arithmetic & glue lemmas for the nonempty branch -/

/-- Sum of `projWalk` lengths over a list is at most `2 * sum (|piLt_mid e|) + es.length`. -/
lemma sum_projWalk_le (G' : MGraph) (piLt_mid : Embedding) (S_prev : Finset ℕ) (es : List ℕ) :
    (es.map fun e => (projWalk G' G' piLt_mid S_prev e).length).sum ≤
      2 * (es.map fun e => (piLt_mid e).length).sum + es.length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := projWalk_length_le G' piLt_mid S_prev e
    omega

/-- `collectRawEsFun (vertsOf J.E) embJH` has length at most `2 * lenSum + eAff.length`. -/
lemma rawEsLen_le_two_lenSum {G' : MGraph} {piLt_mid : Embedding} {S_prev : Finset ℕ}
    {eAff : List ℕ} (hnd : eAff.Nodup) {J : MGraph} (hJE : J.E = eAff.toFinset) :
    (collectRawEsFun (vertsOf J.E) (projWalk G' G' piLt_mid S_prev)).length ≤
      2 * (eAff.map fun e => (piLt_mid e).length).sum + eAff.length := by
  have hlen : (collectRawEsFun (vertsOf J.E) (projWalk G' G' piLt_mid S_prev)).length =
      ∑ e ∈ J.E, (projWalk G' G' piLt_mid S_prev e).length := by
    simp only [collectRawEsFun, List.length_flatMap, List.length_map]
    have hndV : (vertsOf J.E).Nodup := J.E.sort_nodup (· ≤ ·)
    rw [← List.sum_toFinset _ hndV]
    congr 1
    ext e; simp [vertsOf]
  rw [hlen, hJE, List.sum_toFinset _ hnd]
  exact sum_projWalk_le G' piLt_mid S_prev eAff

/-- `sLen ≤ 8 + 3 * J.n + 11 * eAff.length + 10 * lenSum`. -/
lemma sLen_le_bound {G' : MGraph} {piLt_mid : Embedding} {S_prev : Finset ℕ}
    {eAff : List ℕ} (hnd : eAff.Nodup) {J : MGraph} (hJE : J.E = eAff.toFinset) :
    let rawEsLen := (collectRawEsFun (vertsOf J.E) (projWalk G' G' piLt_mid S_prev)).length
    max (gtFwdDynScratchLen J.n J.m rawEsLen) (gtRevDynScratchLen J.n J.m) ≤
      8 + 3 * J.n + 11 * eAff.length + 10 * (eAff.map fun e => (piLt_mid e).length).sum := by
  have hraw := rawEsLen_le_two_lenSum (G' := G') (piLt_mid := piLt_mid) (S_prev := S_prev) hnd hJE
  have hJm : J.m = eAff.length := by
    show J.E.card = eAff.length
    rw [hJE, List.toFinset_card_of_nodup hnd]
  simp only [gtFwdDynScratchLen, gtRevDynScratchLen, hJm]
  omega

/-- `dTotal embJH jtEList ≤ 2 * lenSum + eAff.length` whenever `jtEList` is nodup and `⊆ eAff`. -/
lemma dTotal_jt_le {G' : MGraph} {piLt_mid : Embedding} {S_prev : Finset ℕ}
    {eAff jtEList : List ℕ} (hndE : eAff.Nodup) (hndJ : jtEList.Nodup)
    (hsub : ∀ e ∈ jtEList, e ∈ eAff) :
    dTotal (projWalk G' G' piLt_mid S_prev) jtEList ≤
      2 * (eAff.map fun e => (piLt_mid e).length).sum + eAff.length := by
  unfold dTotal
  rw [← List.sum_toFinset _ hndJ]
  have hsubF : jtEList.toFinset ⊆ eAff.toFinset := by
    intro e he; exact List.mem_toFinset.mpr (hsub e (List.mem_toFinset.mp he))
  calc ∑ e ∈ jtEList.toFinset, (projWalk G' G' piLt_mid S_prev e).length
      ≤ ∑ e ∈ eAff.toFinset, (projWalk G' G' piLt_mid S_prev e).length :=
        Finset.sum_le_sum_of_subset hsubF
    _ = (eAff.map fun e => (projWalk G' G' piLt_mid S_prev e).length).sum :=
        List.sum_toFinset _ hndE
    _ ≤ 2 * (eAff.map fun e => (piLt_mid e).length).sum + eAff.length :=
        sum_projWalk_le G' piLt_mid S_prev eAff

/-- `projHeapNeed piLt_mid eAff ≤ 14 * lenSum + 15 * eAff.length`. -/
lemma projHeapNeed_le_linear (piLt_mid : Embedding) (eAff : List ℕ) :
    projHeapNeed piLt_mid eAff ≤
      14 * (eAff.map fun e => (piLt_mid e).length).sum + 15 * eAff.length := by
  induction eAff with
  | nil => simp [projHeapNeed]
  | cons e es ih =>
    simp only [projHeapNeed, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

/-- `2 ^ (w' + 1) < 2 ^ w` implies `w' ≤ w`. -/
lemma le_of_two_pow_succ_lt {w' w : ℕ} (h : 2 ^ (w' + 1) < 2 ^ w) : w' ≤ w := by
  by_contra hgt
  have hle : w ≤ w' + 1 := by omega
  have := Nat.pow_le_pow_right (by omega : 0 < 2) hle
  omega

/-- `reembedWalk G' G' piLt_mid embMid S_prev e` equals `reembedWalk G' H_lt piLt_mid embMid S_prev e`
when `H_lt.tail = G'.tail ∧ H_lt.head = G'.head`. -/
lemma reembedWalk_congr_host {G' H_lt : MGraph} (ht : H_lt.tail = G'.tail) (hh : H_lt.head = G'.head)
    (piLt_mid embMid : Embedding) (S_prev : Finset ℕ) (e : ℕ) :
    reembedWalk G' G' piLt_mid embMid S_prev e =
      reembedWalk G' H_lt piLt_mid embMid S_prev e := by
  simp only [reembedWalk, prefixWalk_congr_ends ht hh]

/-- `projWalk G' G' piLt_mid S_prev e = projWalk G' H_lt piLt_mid S_prev e` when endpoints agree. -/
lemma projWalk_congr_host {G' H_lt : MGraph} (ht : H_lt.tail = G'.tail) (hh : H_lt.head = G'.head)
    (piLt_mid : Embedding) (S_prev : Finset ℕ) (e : ℕ) :
    projWalk G' G' piLt_mid S_prev e = projWalk G' H_lt piLt_mid S_prev e := by
  simp only [projWalk, prefixWalk_congr_ends ht hh]

/-- `buildProjGraph G' G' ... = buildProjGraph G' H_lt ...` when endpoints agree. -/
lemma buildProjGraph_congr_host {G' H_lt : MGraph} (ht : H_lt.tail = G'.tail) (hh : H_lt.head = G'.head)
    (piLt_mid : Embedding) (S_prev E_aff : Finset ℕ) :
    buildProjGraph G' G' piLt_mid S_prev E_aff =
      buildProjGraph G' H_lt piLt_mid S_prev E_aff := by
  simp only [buildProjGraph, proj, prefixWalk_congr_ends ht hh]

/-- Layout inequalities used by `dsStepPosNonEmptyStmt` to prove register address values match
`StateLayout` functions. -/
lemma stepPosNE_layout_eqs (b L vCap eCap : ℕ) :
    let dg := 4 + 7 * vCap + 9 * eCap
    let gP := b + dsHdrSize
    let hP := gP + dg
    let auxP := hP + dg
    let minH := auxP + dg
    let hNext := minH + eCap
    let hHead := hNext + 2 * eCap
    let L1 := L + 1
    let hDeg := hHead + L1
    let domG := hDeg + L1
    let sGen := domG + (L1 + (2 * (L1 * eCap) + 2 * (L1 * vCap)))
    let sBit := sGen + (2 * L1 + L1 * vCap)
    let eSt := sBit + 2 * vCap
    let mEmb := eSt + 2 * eCap
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
    sBit = dsSBitBase b L vCap eCap ∧
    eSt = dsEStampBase b L vCap eCap ∧
    mEmb = dsMEmbTempBase b L vCap eCap := by
  dsimp only
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase, dsSHeadBase,
    dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase,
    dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase, dsHNextBase, dsMinHBase,
    dsAuxPtr, dsHPtr, dsGPtr, dynGraphSize] <;>
  omega

end

end MinCostFlow.DynSpanner.Program
