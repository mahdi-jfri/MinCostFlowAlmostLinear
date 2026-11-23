module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosEmptyDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosEpilogueDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosNERegs

/-!
# The step of Algorithm 6 for `0 < j` after the affected edges are known

One update of Algorithm 6 (Theorem 8.2, page 64) at a level `j > 0` first applies the update to
`G` and to the levels (`dsStepHead`), then computes the affected edges `E_aff` and the graph `J`
(`dsAffStage`). What remains depends on whether `E_aff` is empty. If it is not, the step
sparsifies `J`, re-embeds the affected edges, rebuilds level `j` and collects `D`
(`dsStepPosNonEmptyStmt`). If it is, level `j` becomes empty and `D = ∅`
(`dsStepPosEmptyStmt`). Both branches end in `StepPosMidPost`, and a common epilogue
(`dsStepPosEpilogueStmt`) turns this into the post `StepOutPost` of a step.

This file defines the procedure `dsStepPosStmt` that makes this choice and runs the epilogue,
its context `StepPosCtx`, and its contract. The context holds the facts after `dsAffStage` that
both branches and the epilogue need. The proof is `dsStepPos_meetsContract`
(`DynSpannerStepPos.lean`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

@[expose] public section

/-- All data and invariants right after `dsAffStage` in a step of Algorithm 6 with `0 < j`, for
either case of `E_aff`, together with the facts from `dsStepHead` that the epilogue needs. The
fields are those of `StepPosNECtx`, without the condition `0 < eAff.length`, with one bound
`hEnd_ltw` that covers the heap of both branches and of the epilogue, and with the epilogue's
own facts (`StepPosEpCtx`). In the empty case the zero-filled table of the empty branch starts
at `eAffPtr + cand.length`, where `hZeroAff` says memory is zero. -/
structure StepPosCtx where
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
  sPrevList : List ℕ
  cand : List ℕ
  eAff : List ℕ
  prefWords : ℕ
  oldBucketsSum : ℕ
  hw16 : 16 ≤ 2 ^ w
  hVG₀ : G₀.IsValid
  hq : 1 ≤ q
  hGm₀ : G₀.m ≤ mMax
  hE₀_cap : ∀ e ∈ G₀.E, e < eCap
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
  hfoot_lt : ∀ a, heapFoot x a → a < heapStep
  hEnd_ltw :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let res := step st u (canonicalSparsify impl)
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
    let J := buildProjGraph G' H_lt piLt_mid S_prev E_aff
    let embJH := projWalk G' H_lt piLt_mid S_prev
    let eAffPtr := heapAff + 2 + sPrevList.length + cand.length
    (if 0 < eAff.length then
      dsStepPosNonEmptyEnd impl mMax vCap eCap G' J piLt_mid embJH eAff
        (eAffPtr + eAff.length) cand.length oldBucketsSum
     else eAffPtr + cand.length + eCap + 1 + 2 * oldBucketsSum) +
      prefWords + 4 * res.UH.length < 2 ^ w
  hGen_ltw : memAff (b + dsGenOff) + 3 + eAff.length < 2 ^ w
  hZeroAff :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let j := chooseLevel L q (k + 1)
    let G' := st.G.applyUpdate u
    let inDom_mid : Fin (L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
    let piLt_mid := piLtFrom st.Pi_level inDom_mid j
    let wpPtr := heapAff + 2 + sPrevList.length + cand.length + eAff.length
    ZeroFrom memAff (wpPtr + eAff.length + 14 * (eAff.map fun e => (piLt_mid e).length).sum +
      15 * eAff.length + cand.length)
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
  hmin_after :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let H_mid : Fin (L + 1) → MGraph := fun i =>
      (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
    (∀ e' < eCap,
      (mem2 (dsMinHBase b vCap eCap + e') = 0 ↔ e' ∉ delSet u st.H.E) ∧
      (e' ∈ delSet u st.H.E → ∃ i : Fin (L + 1),
        mem2 (dsMinHBase b vCap eCap + e') = i.1 + 1 ∧
        e' ∈ (H_mid i).E ∧ ∀ k' : Fin (L + 1), k'.1 < i.1 → e' ∉ (H_mid k').E)) ∧
    (∀ i : Fin (L + 1), ∀ e' < eCap,
      e' ∈ delErase u (if hi : i.1 < L + 1 then x.hBuckets ⟨i.1, hi⟩ else []) ↔
        e' ∈ delSet u st.H.E ∧ mem2 (dsMinHBase b vCap eCap + e') = i.1 + 1)
  hgen_02 : mem0 (b + dsGenOff) ≤ mem2 (b + dsGenOff)
  hS2_lt : ∀ i : Fin (L + 1), i.1 < chooseLevel L q (k + 1) →
    mem2 (dsSGenBase b L vCap eCap + i.1) ≤ mem2 (b + dsGenOff) ∧
    (∀ v < vCap, mem2 (dsVSGenBase b L vCap eCap + i.1 * vCap + v) ≤ mem2 (b + dsGenOff))
  hS2_ge : ∀ i : Fin (L + 1), chooseLevel L q (k + 1) ≤ i.1 →
    ∀ v < vCap, mem2 (dsVSGenBase b L vCap eCap + i.1 * vCap + v) ≤ mem2 (b + dsGenOff)
  hHdr_02 : ∀ addr, b ≤ addr → addr < dsGPtr b → addr ≠ b + dsGenOff → mem2 addr = mem0 addr
  hDom_02 : ∀ addr, dsDomGenBase b L vCap eCap ≤ addr → addr < dsSGenBase b L vCap eCap →
    mem2 addr = mem0 addr
  hVSt_02 : ∀ v < vCap, mem2 (dsVStampBase b L vCap eCap + v) ≤ mem2 (b + dsGenOff)
  hKept_02 : ∀ e < eCap, mem2 (dsKeptStampBase b L vCap eCap + e) =
    mem0 (dsKeptStampBase b L vCap eCap + e)
  hFoot_02 : ∀ a, heapFoot x a → mem2 a = mem0 a
  hFrame_02 : ∀ a < heapStep, ¬ metaFoot b x a → mem2 a = mem0 a
  -- Facts from `dsAffStage` (on `memAff`)
  hAff_eNd : eAff.Nodup
  hAff_iff :
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
    ∀ e, e ∈ eAff ↔ e ∈ affectedEdges G' H_lt piLt_mid S_prev
  hAff_at : ListAt memAff (heapAff + 2 + sPrevList.length + cand.length) eAff
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
  hAff_wp :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let j := chooseLevel L q (k + 1)
    let G' := st.G.applyUpdate u
    let inDom_mid : Fin (L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
    let piLt_mid := piLtFrom st.Pi_level inDom_mid j
    let wpPtr := heapAff + 2 + sPrevList.length + cand.length + eAff.length
    ∀ k' (hk' : k' < eAff.length),
      b + dsFixedSize L vCap eCap ≤ memAff (wpPtr + k') ∧
      memAff (wpPtr + k') + (mWalkEncode (piLt_mid eAff[k'])).length ≤ heapStep ∧
      MWalkAt memAff (memAff (wpPtr + k')) (piLt_mid eAff[k'])
  hAff_emb :
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
    let embJH := projWalk G' H_lt piLt_mid S_prev
    let wpPtr := heapAff + 2 + sPrevList.length + cand.length + eAff.length
    ∀ e ∈ eAff,
      wpPtr + eAff.length ≤ memAff (dsMEmbTempBase b L vCap eCap + e) ∧
      memAff (dsMEmbTempBase b L vCap eCap + e) + (2 * (embJH e).length + 1) ≤
        wpPtr + eAff.length + projHeapNeed piLt_mid eAff ∧
      MWalkAt memAff (memAff (dsMEmbTempBase b L vCap eCap + e)) (embJH e)
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
  -- Facts used only by the epilogue
  sLists' : Fin (L + 1) → List ℕ
  hRev : RevHistoryInv G₀ q (canonicalSparsify impl) us k x
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
  hKept_le : ∀ e < eCap, mem0 (dsKeptStampBase b L vCap eCap + e) ≤ mem0 (b + dsGenOff)
  ht_ltw : k + 1 < 2 ^ w

namespace StepPosCtx

noncomputable abbrev st (ctx : StepPosCtx) : DynSpannerState ctx.L :=
  runState (L := ctx.L) ctx.G₀ ctx.q (canonicalSparsify ctx.impl) ctx.us ctx.k

noncomputable abbrev res (ctx : StepPosCtx) : StepOut ctx.L :=
  step ctx.st ctx.u (canonicalSparsify ctx.impl)

abbrev j (ctx : StepPosCtx) : ℕ := chooseLevel ctx.L ctx.q (ctx.k + 1)

noncomputable abbrev G' (ctx : StepPosCtx) : MGraph := ctx.st.G.applyUpdate ctx.u

noncomputable abbrev H_mid (ctx : StepPosCtx) : Fin (ctx.L + 1) → MGraph :=
  fun i => (ctx.st.H_level i).applyBatch (restrictUpdate ctx.u (ctx.st.H_level i))

noncomputable abbrev inDom_mid (ctx : StepPosCtx) : Fin (ctx.L + 1) → Finset ℕ :=
  fun i => ctx.st.inDom i ∩ ctx.G'.E

noncomputable abbrev S_prev (ctx : StepPosCtx) : Finset ℕ :=
  ctx.st.S_level ⟨ctx.j - 1, by
      have : ctx.j ≤ ctx.L := chooseLevel_le ctx.L ctx.q (ctx.k + 1)
      omega⟩ ∪
    touchedVertices ctx.st.G ctx.u

noncomputable abbrev H_lt (ctx : StepPosCtx) : MGraph := unionGraphLt ctx.G' ctx.H_mid ctx.j

noncomputable abbrev piLt_mid (ctx : StepPosCtx) : Embedding :=
  piLtFrom ctx.st.Pi_level ctx.inDom_mid ctx.j

noncomputable abbrev E_aff (ctx : StepPosCtx) : Finset ℕ :=
  affectedEdges ctx.G' ctx.H_lt ctx.piLt_mid ctx.S_prev

noncomputable abbrev J (ctx : StepPosCtx) : MGraph :=
  buildProjGraph ctx.G' ctx.H_lt ctx.piLt_mid ctx.S_prev ctx.E_aff

noncomputable abbrev embJH (ctx : StepPosCtx) : Embedding :=
  projWalk ctx.G' ctx.H_lt ctx.piLt_mid ctx.S_prev

abbrev eAffPtr (ctx : StepPosCtx) : ℕ :=
  ctx.heapAff + 2 + ctx.sPrevList.length + ctx.cand.length

abbrev wpPtr (ctx : StepPosCtx) : ℕ := ctx.eAffPtr + ctx.eAff.length

/-- The start of the zero-filled table that the empty branch uses. -/
abbrev retAffE (ctx : StepPosCtx) : ℕ := ctx.eAffPtr + ctx.cand.length

/-- A bound on the next free word after either branch: `dsStepPosNonEmptyEnd` if `E_aff` is
not empty, and the pointer `dPtr` of the empty branch otherwise. -/
noncomputable abbrev midEnd (ctx : StepPosCtx) : ℕ :=
  if 0 < ctx.eAff.length then
    dsStepPosNonEmptyEnd ctx.impl ctx.mMax ctx.vCap ctx.eCap ctx.G' ctx.J ctx.piLt_mid
      ctx.embJH ctx.eAff ctx.wpPtr ctx.cand.length ctx.oldBucketsSum
  else ctx.retAffE + ctx.eCap + 1 + 2 * ctx.oldBucketsSum

end StepPosCtx

/-! ## The procedure -/

/-- `args = [b, j, eAffPtr, eAffLen, candLen, oldBucketsSum, heapStep, prefWords, heapAff,
sPrevLen]`. If `eAffLen ≠ 0` it runs `dsStepPosNonEmptyStmt`, otherwise `dsStepPosEmptyStmt`
with its zero table at `eAffPtr + candLen`. Then it runs `dsStepPosEpilogueStmt` from the
pointer that the branch returned, and returns what the epilogue returns. -/
def dsStepPosStmt (bNE bEm bEp : ℕ) : Stmt :=
  .cond (.reg 3)
    (.call 20 (bNE + stepPosNonEmptyIdx)
      [.reg 0, .reg 1, .reg 2, .reg 3, .bin .add (.reg 2) (.reg 3), .reg 4, .reg 5, .reg 6])
    (.call 20 (bEm + stepPosEmptyIdx)
      [.reg 0, .reg 1, .reg 2, .bin .add (.reg 2) (.reg 4), .reg 5, .reg 6]) ;;
  .call 21 (bEp + stepPosEpilogueIdx)
    [.reg 0, .reg 1, .reg 7, .reg 6, .reg 8, .reg 9, .reg 20] ;;
  .ret (.reg 21)

def stepPosProcs (bNE bEm bEp : ℕ) : List Stmt := [dsStepPosStmt bNE bEm bEp]

def stepPosIdx : ℕ := 0

lemma stepPosProcs_noRand (bNE bEm bEp : ℕ) : ∀ s ∈ stepPosProcs bNE bEm bEp, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact ⟨⟨trivial, trivial⟩, trivial, trivial⟩
  cases hs

/-- The cost bound of `dsStepPosStmt`: the cost of the branch that runs, plus the cost of the
epilogue, plus the calls themselves. -/
noncomputable def dsStepPosCost (impl : SparsifyImpl) (mMax L vCap eCap j : ℕ)
    (G' J : MGraph) (piLt_mid embJH : Embedding) (S_prev : Finset ℕ) (eAff : List ℕ)
    (oldBucketsSum sPrevLen prefWords uhLen : ℕ) : ℕ :=
  (if 0 < eAff.length then
    dsStepPosNonEmptyCost impl mMax L vCap eCap j G' J piLt_mid embJH S_prev eAff oldBucketsSum
   else dsStepPosEmptyCost L j oldBucketsSum) +
  dsStepPosEpilogueCost sPrevLen J.m J.n prefWords uhLen + 40

/-- Contract of `dsStepPosStmt`: from the memory after `dsAffStage`, it ends in the post
`StepOutPost` of a step, returns a pointer below the bound of `hEnd_ltw`, and leaves the
generation word at most `mem2 gen + 3 + |E_aff|` (`J.m = |E_aff|`, `mem2` is the memory after
`dsStepHead`). -/
noncomputable def dsStepPosContract (ctx : StepPosCtx) : Contract where
  pre args mem :=
    args = [ctx.b, ctx.j, ctx.eAffPtr, ctx.eAff.length, ctx.cand.length, ctx.oldBucketsSum,
      ctx.heapStep, ctx.prefWords, ctx.heapAff, ctx.sPrevList.length] ∧
    mem = ctx.memAff
  post _ _ ret mem' :=
    StepOutPost ctx.G₀ ctx.L ctx.q ctx.vCap ctx.eCap ctx.b ctx.k ctx.impl ctx.us ctx.u
      ctx.mem0 ctx.x ctx.heapStep mem' ret ∧
    ret ≤ ctx.midEnd + ctx.prefWords + 4 * ctx.res.UH.length ∧
    mem' (ctx.b + dsGenOff) ≤ ctx.mem2 (ctx.b + dsGenOff) + 3 + ctx.J.m ∧
    mem' (ctx.heapStep + 2) ≤ ctx.prefWords + 4 * ctx.res.UH.length ∧
    ListAt mem' ctx.eAffPtr ctx.eAff ∧
    ctx.eAffPtr + ctx.eAff.length ≤ ret
  cost _ _ :=
    dsStepPosCost ctx.impl ctx.mMax ctx.L ctx.vCap ctx.eCap ctx.j ctx.G' ctx.J ctx.piLt_mid
      ctx.embJH ctx.S_prev ctx.eAff ctx.oldBucketsSum ctx.sPrevList.length ctx.prefWords
      ctx.res.UH.length

/-- The procedures that `dsStepPosStmt` calls, directly or not. -/
structure HasStepPosProcs (impl : SparsifyImpl) (p : Program) (bs : StepPosNEBases)
    (bEm bEp bPos : ℕ) : Prop where
  hNE : HasStepPosNEProcs impl p bs
  hEm : p.HasAt bEm (stepPosEmptyProcs bs.bFin)
  hEp : p.HasAt bEp (stepPosEpilogueProcs bs.bAux bs.bPhase)
  hPos : p.HasAt bPos (stepPosProcs bs.bNE bEm bEp)

end

end MinCostFlow.DynSpanner.Program
