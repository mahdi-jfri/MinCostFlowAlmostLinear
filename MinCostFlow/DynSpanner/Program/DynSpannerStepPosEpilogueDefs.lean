module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosNonEmptyDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosNEGlueA
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosJoinB
public import MinCostFlow.DynSpanner.Program.DynSpannerPhase
public import MinCostFlow.DynSpanner.Program.DynSpannerStepOut

/-!
# Common epilogue of a `0 < j` step: the procedure and its contract

Implements and verifies `dsStepPosEpilogueStmt`, the shared final phase of Algorithm 6 for
`0 < j` executed after either `dsStepPosNonEmptyStmt` (`E_aff ≠ ∅`) or `dsStepPosEmptyStmt`
(`E_aff = ∅`). Starting from `StepPosMidPost`, it:
1. Clears `sBit[v]` for every `v ∈ sPrevList` via `dsClearSBitStmt`.
2. Clears the auxiliary graph `J` at `dsAuxPtr` back to `emptyMGraph` via `clearAuxGraphStmt`.
3. Increments the step counter `t` at `b + dsTOff`.
4. Copies the prefix `restrictUpdate u st.H` (`prefWords` words at `heapStep + 5`) and the
   delete/insert tail `c.recs` (at `uhTailHdr + 1`) contiguously to `nextHeap`, using
   `dsCopyWordsStmt` and `dsCopyDelInsStmt`.
5. Stores the 5-word step output header `[uhContigPtr, uhCount, uhWords, dPtr, dLen]` at
   `heapStep..heapStep + 4` and returns `uhContigPtr + uhWords`.
6. Applies `rebuildStatePos` to reconstruct `DynSpannerStateAt` and `RevHistoryInv` at `k + 1`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## Procedure body -/

/-- `args = [b, j, prefWords, heapStep, heapAff, sPrevLen, nextHeap]`.
Runs `dsClearSBit`, `clearAuxGraph`, `t++`, packs `U_H` contiguously at `nextHeap`, stores the
5-word output header at `heapStep..heapStep+4`, and returns `nextHeap + uhWords`. -/
def dsStepPosEpilogueStmt (bAux bPhase : ℕ) : Stmt :=
  -- Compute `auxPtr` (r11) and `sBitPtr` (r18) from header at `b = r0`
  .assign 7 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
  .assign 10 (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 8)) (.bin .mul (.const 9) (.reg 9)))) ;;
  .assign 11 (.bin .add (.bin .add (.reg 0) (.const dsHdrSize))
    (.bin .mul (.const 2) (.reg 10))) ;;                         -- auxPtr
  .assign 12 (.bin .add (.reg 11) (.reg 10)) ;;                  -- minH
  .assign 13 (.bin .add (.reg 7) (.const 1)) ;;                  -- L + 1
  .assign 14 (.bin .add (.bin .add (.reg 12) (.bin .mul (.const 3) (.reg 9)))
    (.bin .mul (.const 2) (.reg 13))) ;;                         -- domGen
  .assign 15 (.bin .add (.reg 14)
    (.bin .add (.reg 13)
      (.bin .add (.bin .mul (.const 2) (.bin .mul (.reg 13) (.reg 9)))
        (.bin .mul (.const 2) (.bin .mul (.reg 13) (.reg 8)))))) ;; -- sGen
  .assign 16 (.bin .add (.reg 15)
    (.bin .add (.bin .mul (.const 2) (.reg 13)) (.bin .mul (.reg 13) (.reg 8)))) ;; -- sBit
  -- 1. Clear `sBit` for `sPrevList` at `heapAff + 2`
  .call 17 (bAux + stepAuxIdxClearSBit) [.reg 16, .bin .add (.reg 4) (.const 2), .reg 5] ;;
  -- 2. Clear `auxPtr` back to `emptyMGraph`
  .call 17 (bPhase + phaseIdxClearAux) [.reg 11] ;;
  -- 3. Increment `t` at `b + dsTOff`
  .assign 18 (.bin .add (.load (.bin .add (.reg 0) (.const dsTOff))) (.const 1)) ;;
  .store (.bin .add (.reg 0) (.const dsTOff)) (.reg 18) ;;
  -- 4. Load `[uhTailHdr, dPtr, dLen]` from `heapStep..heapStep+2` and `tailCount := mem[uhTailHdr]`
  .assign 19 (.load (.reg 3)) ;;                                 -- uhTailHdr
  .assign 20 (.load (.bin .add (.reg 3) (.const 1))) ;;          -- dPtr
  .assign 21 (.load (.bin .add (.reg 3) (.const 2))) ;;          -- dLen
  .assign 22 (.load (.reg 19)) ;;                                -- tailCount
  .assign 23 (.bin .lt (.const 0) (.reg 2)) ;;                   -- prefCount = (0 < prefWords)
  -- 5. Copy prefix `U_H` and tail `U_H` contiguously to `nextHeap = r6`
  .call 24 (bAux + stepAuxIdxCopyWords) [.bin .add (.reg 3) (.const 5), .reg 6, .reg 2] ;;
  .call 25 (bAux + stepAuxIdxCopyDelIns)
    [.bin .add (.reg 19) (.const 1), .bin .add (.reg 6) (.reg 2), .reg 22] ;;
  -- 6. Write 5-word output header at `heapStep..heapStep+4` and return `nextHeap + uhWords`
  .assign 26 (.bin .add (.reg 23) (.reg 22)) ;;                  -- uhCount
  .assign 27 (.bin .add (.reg 2) (.reg 25)) ;;                   -- uhWords
  .store (.reg 3) (.reg 6) ;;
  .store (.bin .add (.reg 3) (.const 1)) (.reg 26) ;;
  .store (.bin .add (.reg 3) (.const 2)) (.reg 27) ;;
  .store (.bin .add (.reg 3) (.const 3)) (.reg 20) ;;
  .store (.bin .add (.reg 3) (.const 4)) (.reg 21) ;;
  .ret (.bin .add (.reg 6) (.reg 27))

def stepPosEpilogueProcs (bAux bPhase : ℕ) : List Stmt :=
  [dsStepPosEpilogueStmt bAux bPhase]

def stepPosEpilogueIdx : ℕ := 0

lemma stepPosEpilogueProcs_noRand (bAux bPhase : ℕ) :
    ∀ s ∈ stepPosEpilogueProcs bAux bPhase, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-! ## Input context and contract for `dsStepPosEpilogueStmt` -/

/-- Context right before `dsStepPosEpilogueStmt`, combining `StepPosMidPost` with the
head-stage facts needed by `rebuildStatePos`. -/
structure StepPosEpCtx where
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
  memMid : ℕ → ℕ
  x : DynSpannerMeta L
  sLists' : Fin (L + 1) → List ℕ
  headHeap : ℕ
  r₁ : ℕ
  heapStep : ℕ
  heapAff : ℕ
  sPrevList : List ℕ
  prefWords : ℕ
  nextHeap : ℕ
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
  hRev : RevHistoryInv G₀ q (canonicalSparsify impl) us k x
  hGV'_cap : ∀ v ∈ ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u).V,
    v < vCap
  hfix_step : b + dsFixedSize L vCap eCap ≤ heapStep
  hhead_in : heapStep + 5 + prefWords ≤ headHeap ∧ headHeap ≤ r₁ ∧ r₁ ≤ heapAff
  hgen_02 : mem0 (b + dsGenOff) ≤ mem2 (b + dsGenOff)
  hPrefBody : BatchBodyAt mem2 (heapStep + 5)
    (runState (L := L) G₀ q (canonicalSparsify impl) us k).H
    (restrictUpdate u (runState (L := L) G₀ q (canonicalSparsify impl) us k).H) prefWords
  hSL2 : ∀ i : Fin (L + 1),
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let j := chooseLevel L q (k + 1)
    let S' : Finset ℕ := if i.1 < j then st.S_level i ∪ touchedVertices st.G u else ∅
    mem2 (dsSGenBase b L vCap eCap + i.1) ≤ mem2 (b + dsGenOff) ∧
    (j ≤ i.1 → mem2 (dsSGenBase b L vCap eCap + i.1) = 0) ∧
    (∀ v ∈ S', v < vCap) ∧
    (∀ v < vCap,
      mem2 (dsVSGenBase b L vCap eCap + i.1 * vCap + v) ≤ mem2 (b + dsGenOff) ∧
      ((0 < mem2 (dsSGenBase b L vCap eCap + i.1) ∧
        mem2 (dsVSGenBase b L vCap eCap + i.1 * vCap + v) =
          mem2 (dsSGenBase b L vCap eCap + i.1)) ↔ v ∈ S')) ∧
    (sLists' i).Nodup ∧ (∀ v, v ∈ sLists' i ↔ v ∈ S') ∧
    (if 0 < mem2 (dsSGenBase b L vCap eCap + i.1)
     then LinkedListIn (fun p => heapFoot x p ∨ (headHeap ≤ p ∧ p < r₁)) mem2
            (mem2 (dsSHeadBase b L vCap eCap + i.1)) (sLists' i)
     else sLists' i = [])
  hsPrev_eq : sPrevList = sLists' ⟨chooseLevel L q (k + 1) - 1,
    by have := chooseLevel_le L q (k + 1); omega⟩
  hFoot_02 : ∀ a, heapFoot x a → mem2 a = mem0 a
  hfoot_lt : ∀ a, heapFoot x a → a < heapStep
  hKept_le : ∀ e < eCap, mem0 (dsKeptStampBase b L vCap eCap + e) ≤ mem0 (b + dsGenOff)
  hMidPost : StepPosMidPost G₀ L q vCap eCap b k impl us u mem0 mem2 x headHeap r₁
    heapStep heapAff sPrevList prefWords memMid nextHeap
  ht_ltw : k + 1 < 2 ^ w
  hEnd_ltw :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let res := step st u (canonicalSparsify impl)
    nextHeap + prefWords + 4 * res.UH.length < 2 ^ w

namespace StepPosEpCtx

noncomputable abbrev st (ctx : StepPosEpCtx) : DynSpannerState ctx.L :=
  runState (L := ctx.L) ctx.G₀ ctx.q (canonicalSparsify ctx.impl) ctx.us ctx.k

noncomputable abbrev res (ctx : StepPosEpCtx) : StepOut ctx.L :=
  step ctx.st ctx.u (canonicalSparsify ctx.impl)

abbrev j (ctx : StepPosEpCtx) : ℕ := chooseLevel ctx.L ctx.q (ctx.k + 1)

noncomputable abbrev J (ctx : StepPosEpCtx) : MGraph :=
  let G' := ctx.st.G.applyUpdate ctx.u
  let H_mid : Fin (ctx.L + 1) → MGraph :=
    fun i => (ctx.st.H_level i).applyBatch (restrictUpdate ctx.u (ctx.st.H_level i))
  let inDom_mid : Fin (ctx.L + 1) → Finset ℕ := fun i => ctx.st.inDom i ∩ G'.E
  let S_prev := ctx.st.S_level ⟨chooseLevel ctx.L ctx.q (ctx.k + 1) - 1,
    by have := chooseLevel_le ctx.L ctx.q (ctx.k + 1); omega⟩ ∪
    touchedVertices ctx.st.G ctx.u
  let H_lt := unionGraphLt G' H_mid ctx.j
  let piLt_mid := piLtFrom ctx.st.Pi_level inDom_mid ctx.j
  buildProjGraph G' H_lt piLt_mid S_prev (affectedEdges G' H_lt piLt_mid S_prev)

end StepPosEpCtx

/-- Explicit cost bound of `dsStepPosEpilogueStmt`. -/
def dsStepPosEpilogueCost (sPrevLen jM jN prefWords uhLen : ℕ) : ℕ :=
  35 * sPrevLen + 500 * jM + 30 * jN + 30 * prefWords + 95 * uhLen + 450

/-- Contract for `dsStepPosEpilogueStmt`. The post also bounds the generation word:
`mem' gen ≤ mem2 gen + 3 + |E_aff|` (`J.m = |E(J)| = |E_aff|`, `mem2` is the memory after
`dsStepHead`). -/
noncomputable def dsStepPosEpilogueContract (ctx : StepPosEpCtx) : Contract where
  pre args mem :=
    args = [ctx.b, ctx.j, ctx.prefWords, ctx.heapStep, ctx.heapAff, ctx.sPrevList.length,
      ctx.nextHeap] ∧
    mem = ctx.memMid
  post _ _ ret mem' :=
    StepOutPost ctx.G₀ ctx.L ctx.q ctx.vCap ctx.eCap ctx.b ctx.k ctx.impl ctx.us ctx.u
      ctx.mem0 ctx.x ctx.heapStep mem' ret ∧
    ret ≤ ctx.nextHeap + ctx.prefWords + 4 * ctx.res.UH.length ∧
    mem' (ctx.b + dsGenOff) ≤ ctx.mem2 (ctx.b + dsGenOff) + 3 + ctx.J.m ∧
    mem' (ctx.heapStep + 2) ≤ ctx.prefWords + 4 * ctx.res.UH.length ∧
    (∀ a, ctx.heapStep + 5 ≤ a → a < ctx.nextHeap → mem' a = ctx.memMid a) ∧
    ctx.nextHeap ≤ ret
  cost _ _ :=
    dsStepPosEpilogueCost ctx.sPrevList.length ctx.J.m ctx.J.n ctx.prefWords ctx.res.UH.length

end

end MinCostFlow.DynSpanner.Program
