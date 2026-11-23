module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosNonEmptyDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerShortcutBridge
import WordRAM.Tactic

/-!
# Nonempty affected-set branch of a `0 < j` step: glue part A

Defines `StepPosNECtx` (the state right after `dsAffStage` when `E_aff ≠ ∅`) and the first two
context-building glue theorems:
1. `stepPosNE_spPre`: derives `dsSparsifyStageContract.pre` and sparsifier facts.
2. `stepPosNE_reembCtx`: constructs `RSCtx` on `memSp` after `dsSparsifyStage`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## Input context for `dsStepPosNonEmptyStmt` -/

/-- All data and invariants holding right after `dsAffStage` and `dsSumRange` in a `0 < j` step
when `E_aff ≠ ∅`. -/
structure StepPosNECtx where
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
  heAff_pos : 0 < eAff.length
  hEnd_ltw :
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
    let J := buildProjGraph G' H_lt piLt_mid S_prev E_aff
    let embJH := projWalk G' H_lt piLt_mid S_prev
    let wpPtr := heapAff + 2 + sPrevList.length + cand.length + eAff.length
    dsStepPosNonEmptyEnd impl mMax vCap eCap G' J piLt_mid embJH eAff wpPtr cand.length
      oldBucketsSum < 2 ^ w
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

/-! ## Projections on `StepPosNECtx` -/

noncomputable abbrev StepPosNECtx.st (ctx : StepPosNECtx) : DynSpannerState ctx.L :=
  runState (L := ctx.L) ctx.G₀ ctx.q (canonicalSparsify ctx.impl) ctx.us ctx.k

noncomputable abbrev StepPosNECtx.res (ctx : StepPosNECtx) : StepOut ctx.L :=
  step ctx.st ctx.u (canonicalSparsify ctx.impl)

abbrev StepPosNECtx.j (ctx : StepPosNECtx) : ℕ := chooseLevel ctx.L ctx.q (ctx.k + 1)

noncomputable abbrev StepPosNECtx.G' (ctx : StepPosNECtx) : MGraph := ctx.st.G.applyUpdate ctx.u

noncomputable abbrev StepPosNECtx.H_mid (ctx : StepPosNECtx) : Fin (ctx.L + 1) → MGraph :=
  fun i => (ctx.st.H_level i).applyBatch (restrictUpdate ctx.u (ctx.st.H_level i))

noncomputable abbrev StepPosNECtx.inDom_mid (ctx : StepPosNECtx) : Fin (ctx.L + 1) → Finset ℕ :=
  fun i => ctx.st.inDom i ∩ ctx.G'.E

noncomputable abbrev StepPosNECtx.S_prev (ctx : StepPosNECtx) : Finset ℕ :=
  ctx.st.S_level ⟨ctx.j - 1, by
      have : ctx.j ≤ ctx.L := chooseLevel_le ctx.L ctx.q (ctx.k + 1)
      omega⟩ ∪
    touchedVertices ctx.st.G ctx.u

noncomputable abbrev StepPosNECtx.H_lt (ctx : StepPosNECtx) : MGraph :=
  unionGraphLt ctx.G' ctx.H_mid ctx.j

noncomputable abbrev StepPosNECtx.piLt_mid (ctx : StepPosNECtx) : Embedding :=
  piLtFrom ctx.st.Pi_level ctx.inDom_mid ctx.j

noncomputable abbrev StepPosNECtx.E_aff (ctx : StepPosNECtx) : Finset ℕ :=
  affectedEdges ctx.G' ctx.H_lt ctx.piLt_mid ctx.S_prev

noncomputable abbrev StepPosNECtx.J (ctx : StepPosNECtx) : MGraph :=
  buildProjGraph ctx.G' ctx.H_lt ctx.piLt_mid ctx.S_prev ctx.E_aff

noncomputable abbrev StepPosNECtx.H_aux (ctx : StepPosNECtx) : MGraph :=
  buildAuxHost ctx.G' ctx.H_lt ctx.E_aff

noncomputable abbrev StepPosNECtx.embJH (ctx : StepPosNECtx) : Embedding :=
  projWalk ctx.G' ctx.H_lt ctx.piLt_mid ctx.S_prev

noncomputable abbrev StepPosNECtx.out (ctx : StepPosNECtx) : SparsifyOut :=
  canonicalSparsify ctx.impl ctx.G' ctx.J ctx.embJH

noncomputable abbrev StepPosNECtx.outEmb (ctx : StepPosNECtx) : Embedding :=
  fun e => shortcutWalk ctx.out.Jtilde (ctx.J.tail e) (ctx.out.emb e)

noncomputable abbrev StepPosNECtx.embMid (ctx : StepPosNECtx) : Embedding :=
  Embedding.comp ctx.embJH ctx.outEmb

abbrev StepPosNECtx.eAffPtr (ctx : StepPosNECtx) : ℕ :=
  ctx.heapAff + 2 + ctx.sPrevList.length + ctx.cand.length

abbrev StepPosNECtx.wpPtr (ctx : StepPosNECtx) : ℕ :=
  ctx.eAffPtr + ctx.eAff.length

noncomputable abbrev StepPosNECtx.lenSum (ctx : StepPosNECtx) : ℕ :=
  (ctx.eAff.map fun e => (ctx.piLt_mid e).length).sum

noncomputable abbrev StepPosNECtx.scratchPtr (ctx : StepPosNECtx) : ℕ :=
  ctx.wpPtr + ctx.eAff.length + 14 * ctx.lenSum + 15 * ctx.eAff.length + ctx.cand.length

noncomputable abbrev StepPosNECtx.guestBase (ctx : StepPosNECtx) : ℕ :=
  ctx.scratchPtr + 8 + 3 * ctx.J.n + 11 * ctx.eAff.length + 10 * ctx.lenSum

lemma StepPosNECtx.addr_chain (ctx : StepPosNECtx) :
    ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ ctx.heapStep ∧
    ctx.heapStep + 5 + ctx.prefWords ≤ ctx.headHeap ∧
    ctx.headHeap ≤ ctx.r₁ ∧ ctx.r₁ ≤ ctx.heapAff ∧
    ctx.heapAff + 2 + ctx.sPrevList.length + ctx.cand.length = ctx.eAffPtr ∧
    ctx.eAffPtr + ctx.eAff.length = ctx.wpPtr ∧
    ctx.wpPtr + ctx.eAff.length + 14 * ctx.lenSum + 15 * ctx.eAff.length + ctx.cand.length =
      ctx.scratchPtr ∧
    ctx.scratchPtr + 8 + 3 * ctx.J.n + 11 * ctx.eAff.length + 10 * ctx.lenSum = ctx.guestBase :=
  ⟨ctx.hfix_step, ctx.hhead_in.1, ctx.hhead_in.2.1, ctx.hhead_in.2.2, rfl, rfl, rfl, rfl⟩

/-! ## Layout and bound helpers -/

lemma fixed_layout_order (b L vCap eCap : ℕ) :
    b + dsHdrSize = dsGPtr b ∧
    dsGPtr b + dynGraphSize vCap eCap = dsHPtr b vCap eCap ∧
    dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap ∧
    dsAuxPtr b vCap eCap + dynGraphSize vCap eCap = dsMinHBase b vCap eCap ∧
    dsMinHBase b vCap eCap + 3 * eCap + 2 * (L + 1) = dsDomGenBase b L vCap eCap ∧
    dsDomGenBase b L vCap eCap + (L + 1) = dsEdgeDomGenBase b L vCap eCap ∧
    dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap = dsPiPtrBase b L vCap eCap ∧
    dsPiPtrBase b L vCap eCap + (L + 1) * eCap = dsRevGenBase b L vCap eCap ∧
    dsRevGenBase b L vCap eCap + (L + 1) * vCap = dsRevHeadBase b L vCap eCap ∧
    dsRevHeadBase b L vCap eCap + (L + 1) * vCap = dsSGenBase b L vCap eCap ∧
    dsSGenBase b L vCap eCap + 2 * (L + 1) + (L + 1) * vCap = dsSBitBase b L vCap eCap ∧
    dsSBitBase b L vCap eCap + vCap = dsVStampBase b L vCap eCap ∧
    dsVStampBase b L vCap eCap + vCap = dsEStampBase b L vCap eCap ∧
    dsEStampBase b L vCap eCap + eCap = dsKeptStampBase b L vCap eCap ∧
    dsKeptStampBase b L vCap eCap + eCap = dsMEmbTempBase b L vCap eCap ∧
    dsMEmbTempBase b L vCap eCap + eCap = b + dsFixedSize L vCap eCap := by
  have hfa := dsFixedSize_add b L vCap eCap
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, hfa⟩ <;>
  simp only [dsSBitBase, dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase,
    dsPiPtrBase, dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase,
    dsHNextBase, dsMinHBase] <;>
  ring

lemma spEnd_add_reemb_lt_of_end {impl : SparsifyImpl} {mMax vCap eCap : ℕ}
    {G' J : MGraph} {piLt_mid embJH : Embedding} {eAff : List ℕ}
    {wpPtr candLen oldBucketsSum w : ℕ}
    (hEnd : dsStepPosNonEmptyEnd impl mMax vCap eCap G' J piLt_mid embJH eAff
      wpPtr candLen oldBucketsSum < 2 ^ w) :
    let lenSum := (eAff.map fun e => (piLt_mid e).length).sum
    let out := canonicalSparsify impl G' J embJH
    let outEmb : Embedding := fun e => shortcutWalk out.Jtilde (J.tail e) (out.emb e)
    let scratchPtr := wpPtr + eAff.length + 14 * lenSum + 15 * eAff.length + candLen
    let guestBase := scratchPtr + 8 + 3 * J.n + 11 * eAff.length + 10 * lenSum
    let spEnd := spOutBound impl mMax vCap eCap guestBase G' J embJH +
      dsShortcutHeapSpace eAff out.emb
    spEnd + eCap + reembStageNeed piLt_mid embJH outEmb eAff < 2 ^ w := by
  dsimp only [dsStepPosNonEmptyEnd] at hEnd ⊢
  omega

lemma spOutBound_lt_of_end {impl : SparsifyImpl} {mMax vCap eCap : ℕ}
    {G' J : MGraph} {piLt_mid embJH : Embedding} {eAff : List ℕ}
    {wpPtr candLen oldBucketsSum w : ℕ}
    (hEnd : dsStepPosNonEmptyEnd impl mMax vCap eCap G' J piLt_mid embJH eAff
      wpPtr candLen oldBucketsSum < 2 ^ w) :
    let lenSum := (eAff.map fun e => (piLt_mid e).length).sum
    let out := canonicalSparsify impl G' J embJH
    let scratchPtr := wpPtr + eAff.length + 14 * lenSum + 15 * eAff.length + candLen
    let guestBase := scratchPtr + 8 + 3 * J.n + 11 * eAff.length + 10 * lenSum
    spOutBound impl mMax vCap eCap guestBase G' J embJH +
      dsShortcutHeapSpace eAff out.emb < 2 ^ w ∧
    guestBase + 2 ^ (wordSize impl.cw (canonSparsifyInput G' J embJH) + 1) + 2 +
      3 * J.m + dynGraphSize vCap eCap + eCap + J.m * (1 + 2 * Nat.ceil (impl.γ_ℓ mMax)) < 2 ^ w ∧
    guestBase < 2 ^ w ∧
    wordSize impl.cw (canonSparsifyInput G' J embJH) ≤ w := by
  have h1 : ∀ (gb pw jm dg ec cl sh rn jtm ls el ob w' w : ℕ),
      pw = 2 ^ (w' + 1) →
      gb + pw + 2 + 3 * jm + dg + ec + cl + sh + ec + 16 * el + 14 * ls + 5 * rn + 1 +
        2 * ob + 4 * jtm + 2 * ls + el < 2 ^ w →
      (gb + pw + 2 + 3 * jm + dg + ec + cl + sh < 2 ^ w) ∧
      (gb + pw + 2 + 3 * jm + dg + ec + cl < 2 ^ w) ∧
      (gb < 2 ^ w) ∧
      (w' ≤ w) := by
    intro gb pw jm dg ec cl sh rn jtm ls el ob w' w hpw h
    refine ⟨by omega, by omega, by omega, le_of_two_pow_succ_lt (by rw [← hpw]; omega)⟩
  exact h1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl hEnd

end

/-! ## Glue 1: Precondition of `dsSparsifyStage` -/

public section

/-- Derive `dsSparsifyStageContract.pre` and key sparsifier facts from `StepPosNECtx`. -/
theorem stepPosNE_spPre (ctx : StepPosNECtx) :
    ctx.E_aff.Nonempty ∧
    ctx.J.E = ctx.eAff.toFinset ∧
    ctx.out = canonicalSparsify ctx.impl ctx.H_aux ctx.J ctx.embJH ∧
    ctx.out.Jtilde.tail = ctx.J.tail ∧ ctx.out.Jtilde.head = ctx.J.head ∧
    ctx.out.Jtilde.E ⊆ ctx.E_aff ∧
    (∀ e ∈ ctx.J.E, ctx.out.Jtilde.IsWalk (ctx.J.tail e) (ctx.J.head e) (ctx.out.emb e)) ∧
    (∀ e ∈ ctx.E_aff, ∀ x ∈ ctx.embJH e, x.1 < ctx.eCap) ∧
    (dsSparsifyStageContract ctx.impl ctx.mMax ctx.w ctx.vCap ctx.eCap ctx.vCap ctx.eCap
      ctx.vCap ctx.eCap ctx.L ctx.vCap ctx.eCap ctx.b ctx.G' ctx.J ctx.embJH ctx.eAff).pre
      [dsGPtr ctx.b, dsAuxPtr ctx.b ctx.vCap ctx.eCap, dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap,
       ctx.vCap, ctx.eCap, ctx.scratchPtr, ctx.guestBase, ctx.b, ctx.eAffPtr, ctx.eAff.length]
      ctx.memAff := by
  have hfl := fixed_layout_order ctx.b ctx.L ctx.vCap ctx.eCap
  have hch := ctx.addr_chain
  have hne : ctx.E_aff.Nonempty := by
    have h0 : 0 < ctx.eAff.length := ctx.heAff_pos
    exact ⟨ctx.eAff[0], (ctx.hAff_iff _).mp (List.getElem_mem h0)⟩
  have hJE_eq : ctx.J.E = ctx.eAff.toFinset := by
    ext e; simp [StepPosNECtx.J, buildProjGraph, ctx.hAff_iff]
  have hdu := (batchIsValid_take ctx.us ctx.G₀ ctx.k ctx.hBV ctx.hds).2.2 ctx.u ctx.hu_some
  have hGE'_cap : ∀ e ∈ ctx.G'.E, e < ctx.eCap := fun e he =>
    ctx.hState.2.2.2.2.2.2.2.2.2.2.1 e (E_applyUpdate_subset hdu.2 he)
  have hspf := projGraph_sparsify_facts ctx.hVG₀ ctx.hq ctx.hGm₀ ctx.hE₀_cap ctx.hBV ctx.hds
    ctx.hu_some ctx.hPref ctx.hj_pos ctx.hGV'_cap hGE'_cap hne
  rcases hspf with ⟨hJn1, hJval, hJm_le, hJV_cap, hJE_cap, hemb, hLen1, hcanon, hJwalk, hembCap⟩
  have hVG' : ctx.G'.IsValid :=
    isValid_applyUpdate_of_delOrSplit ctx.hState.2.2.2.2.1
      ((ctx.hPref ctx.k (le_refl _)).G_eq ▸ hdu.1) hdu.2
  have hSpecG := canonicalSparsify_spec_absorb ctx.impl ctx.mMax ctx.G' ctx.J ctx.embJH
    hVG' hJval hJm_le (fun _ => hLen1) hemb
  have hJt_sub : ctx.J.IsSubgraph ctx.out.Jtilde := hSpecG.1
  have hJt_ends := canonicalSparsify_ends ctx.impl ctx.G' ctx.J ctx.embJH
  have hJt_E : ctx.out.Jtilde.E ⊆ ctx.E_aff := hJt_sub.2.1
  have hJt_w : ∀ e ∈ ctx.J.E, ctx.out.Jtilde.IsWalk (ctx.J.tail e) (ctx.J.head e) (ctx.out.emb e) :=
    fun e he => hSpecG.2.1.2 e he
  have hb1 : 1 ≤ ctx.b := ctx.hState.2.2.2.1
  have hL_w : ctx.memAff (ctx.b + dsLOff) = ctx.L :=
    (ctx.hAff_frame _ (by simp [dsLOff, dsHdrSize] at hfl ⊢; omega) (by simp [dsLOff, dsGenOff])
      (Or.inl (by simp [dsLOff, dsHdrSize] at hfl ⊢; omega))
      (Or.inl (by simp [dsLOff, dsHdrSize] at hfl ⊢; omega))
      (Or.inl (by simp [dsLOff, dsHdrSize] at hfl ⊢; omega))
      (Or.inl (by simp [dsLOff, dsHdrSize] at hfl ⊢; omega))).trans
      ((ctx.hHdr_02 _ (by simp [dsLOff]) (by simp [dsLOff, dsGPtr, dsHdrSize])
        (by simp [dsLOff, dsGenOff])).trans ctx.hState.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  have hV_w : ctx.memAff (ctx.b + dsVCapOff) = ctx.vCap :=
    (ctx.hAff_frame _ (by simp [dsVCapOff, dsHdrSize] at hfl ⊢; omega) (by simp [dsVCapOff, dsGenOff])
      (Or.inl (by simp [dsVCapOff, dsHdrSize] at hfl ⊢; omega))
      (Or.inl (by simp [dsVCapOff, dsHdrSize] at hfl ⊢; omega))
      (Or.inl (by simp [dsVCapOff, dsHdrSize] at hfl ⊢; omega))
      (Or.inl (by simp [dsVCapOff, dsHdrSize] at hfl ⊢; omega))).trans
      ((ctx.hHdr_02 _ (by simp [dsVCapOff]) (by simp [dsVCapOff, dsGPtr, dsHdrSize])
        (by simp [dsVCapOff, dsGenOff])).trans ctx.hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  have hE_w : ctx.memAff (ctx.b + dsECapOff) = ctx.eCap :=
    (ctx.hAff_frame _ (by simp [dsECapOff, dsHdrSize] at hfl ⊢; omega) (by simp [dsECapOff, dsGenOff])
      (Or.inl (by simp [dsECapOff, dsHdrSize] at hfl ⊢; omega))
      (Or.inl (by simp [dsECapOff, dsHdrSize] at hfl ⊢; omega))
      (Or.inl (by simp [dsECapOff, dsHdrSize] at hfl ⊢; omega))
      (Or.inl (by simp [dsECapOff, dsHdrSize] at hfl ⊢; omega))).trans
      ((ctx.hHdr_02 _ (by simp [dsECapOff]) (by simp [dsECapOff, dsGPtr, dsHdrSize])
        (by simp [dsECapOff, dsGenOff])).trans ctx.hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
  have hDG' : DynGraphAt ctx.memAff (dsGPtr ctx.b) ctx.vCap ctx.eCap ctx.G' :=
    dynGraphAt_of_agree ctx.hG'_graph fun a ha1 ha2 =>
      ctx.hAff_frame a (by omega) (by simp [dsGPtr, dsHdrSize, dsGenOff] at ha1 ⊢; omega)
        (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
  have hVSt_aff : ∀ v < ctx.vCap,
      ctx.memAff (dsVStampBase ctx.b ctx.L ctx.vCap ctx.eCap + v) ≤ ctx.memAff (ctx.b + dsGenOff) := by
    intro v hv
    have hag : ctx.memAff (dsVStampBase ctx.b ctx.L ctx.vCap ctx.eCap + v) =
        ctx.mem2 (dsVStampBase ctx.b ctx.L ctx.vCap ctx.eCap + v) :=
      ctx.hAff_frame _ (by omega) (by simp [dsGenOff, dsHdrSize] at hfl ⊢; omega)
        (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    rw [hag, ctx.hAff_gen]
    exact le_trans (ctx.hVSt_02 v hv) (Nat.le_succ _)
  have hMEmb : MEmbAt ctx.memAff (dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap)
      ctx.J.E ctx.eCap ctx.embJH :=
    fun e he => ⟨hJE_cap e he, (ctx.hAff_emb e ((ctx.hAff_iff e).mpr he)).2.2⟩
  obtain ⟨hSpBnd, hGbBnd, hGb_lt_w, hw'_le⟩ := spOutBound_lt_of_end ctx.hEnd_ltw
  have hGb_lt_w' : ctx.guestBase < 2 ^ ctx.w := hGb_lt_w
  clear hGb_lt_w
  have hsLen := sLen_le_bound (G' := ctx.G') (piLt_mid := ctx.piLt_mid)
    (S_prev := ctx.S_prev) ctx.hAff_eNd hJE_eq
  have hprojH : projHeapNeed ctx.piLt_mid ctx.eAff ≤ 14 * ctx.lenSum + 15 * ctx.eAff.length :=
    projHeapNeed_le_linear ctx.piLt_mid ctx.eAff
  have hwp_le_scr : ctx.wpPtr + ctx.eAff.length + projHeapNeed ctx.piLt_mid ctx.eAff ≤
      ctx.scratchPtr := by omega
  clear hVG' hSpecG hJt_sub hdu
  have hproj_eq : projWalk ctx.G' ctx.G' ctx.piLt_mid ctx.S_prev = ctx.embJH := by
    funext e
    exact projWalk_congr_host (G' := ctx.G') (H_lt := ctx.H_lt)
      (by rfl : (unionGraphLt ctx.G' ctx.H_mid ctx.j).tail = ctx.G'.tail)
      (by rfl : (unionGraphLt ctx.G' ctx.H_mid ctx.j).head = ctx.G'.head) _ _ _
  have hsLen' : max (gtFwdDynScratchLen ctx.J.n ctx.J.m
      (collectRawEsFun (vertsOf ctx.J.E) ctx.embJH).length)
      (gtRevDynScratchLen ctx.J.n ctx.J.m) ≤
      8 + 3 * ctx.J.n + 11 * ctx.eAff.length + 10 * ctx.lenSum := by
    change max (gtFwdDynScratchLen ctx.J.n ctx.J.m
      (collectRawEsFun (vertsOf ctx.J.E) (projWalk ctx.G' ctx.G' ctx.piLt_mid ctx.S_prev)).length)
      (gtRevDynScratchLen ctx.J.n ctx.J.m) ≤
      8 + 3 * ctx.J.n + 11 * ctx.eAff.length + 10 * ctx.lenSum at hsLen
    rw [hproj_eq] at hsLen
    exact hsLen
  refine ⟨hne, hJE_eq, hcanon.symm, hJt_ends.1, hJt_ends.2, hJt_E, hJt_w, hembCap,
    dsGPtr ctx.b, dsAuxPtr ctx.b ctx.vCap ctx.eCap,
    dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap, ctx.scratchPtr, ctx.guestBase, ctx.eAffPtr,
    rfl, ?_, hb1, by omega, by omega, hSpBnd, hL_w, hV_w, hE_w, by have := ctx.hGen_ltw; omega,
    hVSt_aff, Or.inl (by omega), Or.inr (by omega), ctx.hAff_eNd, ctx.hAff_iff, ctx.hAff_at,
    hJval, hJV_cap, hJwalk⟩
  -- `sparsifyDynContract.pre`
  have hScr_lt_gb : ctx.scratchPtr + max (gtFwdDynScratchLen ctx.J.n ctx.J.m
      (collectRawEsFun (vertsOf ctx.J.E) ctx.embJH).length)
      (gtRevDynScratchLen ctx.J.n ctx.J.m) ≤ ctx.guestBase := by omega
  have hEmb_le_scr : ∀ e ∈ ctx.J.E,
      ctx.memAff (dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap + e) +
        (2 * (ctx.embJH e).length + 1) ≤ ctx.scratchPtr := by
    intro e he
    have h1 : ctx.memAff (dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap + e) +
        (2 * (ctx.embJH e).length + 1) ≤ ctx.wpPtr + ctx.eAff.length +
        projHeapNeed ctx.piLt_mid ctx.eAff :=
      (ctx.hAff_emb e ((ctx.hAff_iff e).mpr he)).2.1
    omega
  have hFix_lt_scr : ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ ctx.scratchPtr := by omega
  have hScr_lt_gb' : ctx.scratchPtr < ctx.guestBase := by omega
  refine ⟨dsGPtr ctx.b, dsAuxPtr ctx.b ctx.vCap ctx.eCap,
    dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap, ctx.scratchPtr, ctx.guestBase,
    rfl, ctx.hw16, hJn1, by omega, by omega, by omega, hw'_le, hGbBnd,
    by omega, by omega, by omega, hScr_lt_gb,
    fun i hi => Or.inl (by omega), fun i hi => Or.inl (by omega),
    fun e he => Or.inl (by have := hJE_cap e he; omega),
    fun e he k' hk' => Or.inl (by
      have h1 := hEmb_le_scr e he
      rw [mWalkEncode_length] at hk'; omega),
    (ctx.hZeroAff : ZeroFrom ctx.memAff ctx.scratchPtr).mono (le_of_lt hScr_lt_gb'),
    hDG', ctx.hAff_aux, hemb, hMEmb, hJm_le, fun _ => hLen1, hJV_cap, hJE_cap, fun e he => ?_⟩
  have h1 := hEmb_le_scr e he
  rw [mWalkEncode_length]; omega

/-! ## Glue 2: `RSCtx` for `dsReembStage` -/

/-- Build `RSCtx` on `memSp` after `dsSparsifyStage`. -/
theorem stepPosNE_reembCtx (ctx : StepPosNECtx) {memSp : ℕ → ℕ} {retSp : ℕ}
    (hSp : (dsSparsifyStageContract ctx.impl ctx.mMax ctx.w ctx.vCap ctx.eCap ctx.vCap ctx.eCap
      ctx.vCap ctx.eCap ctx.L ctx.vCap ctx.eCap ctx.b ctx.G' ctx.J ctx.embJH ctx.eAff).post
      [dsGPtr ctx.b, dsAuxPtr ctx.b ctx.vCap ctx.eCap, dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap,
       ctx.vCap, ctx.eCap, ctx.scratchPtr, ctx.guestBase, ctx.b, ctx.eAffPtr, ctx.eAff.length]
      ctx.memAff retSp memSp) :
    let jtPtr := memSp ctx.scratchPtr
    let qTab := memSp (ctx.scratchPtr + 1)
    let heapReemb := retSp + ctx.eCap
    ∃ rc : RSCtx,
      rc.w = ctx.w ∧ rc.vCap = ctx.vCap ∧ rc.eCap = ctx.eCap ∧
      rc.G = ctx.G' ∧ rc.embLt = ctx.piLt_mid ∧ rc.embJH = ctx.embJH ∧
      rc.outEmb = ctx.outEmb ∧ rc.S = ctx.S_prev ∧ rc.es = ctx.eAff ∧
      rc.gPtr = dsGPtr ctx.b ∧ rc.sBitPtr = dsSBitBase ctx.b ctx.L ctx.vCap ctx.eCap ∧
      rc.tab = dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap ∧ rc.piTab = retSp ∧
      rc.esPtr = ctx.eAffPtr ∧ rc.wpPtr = ctx.wpPtr ∧ rc.qTab = qTab ∧
      rc.heap = heapReemb ∧ rc.mem0 = memSp ∧
      ctx.guestBase ≤ jtPtr ∧ jtPtr + dynGraphSize ctx.vCap ctx.eCap = qTab ∧
      qTab + ctx.eCap ≤ retSp ∧
      retSp ≤ spOutBound ctx.impl ctx.mMax ctx.vCap ctx.eCap ctx.guestBase ctx.G' ctx.J ctx.embJH +
        dsShortcutHeapSpace ctx.eAff ctx.out.emb ∧
      DynGraphAt memSp jtPtr ctx.vCap ctx.eCap ctx.out.Jtilde ∧
      ZeroFrom memSp retSp ∧
      (∀ v < ctx.vCap, memSp (dsVStampBase ctx.b ctx.L ctx.vCap ctx.eCap + v) ≤
        ctx.memAff (ctx.b + dsGenOff)) ∧
      (∀ addr, addr < ctx.scratchPtr →
        (∀ v < ctx.vCap, addr ≠ dsVStampBase ctx.b ctx.L ctx.vCap ctx.eCap + v) →
        memSp addr = ctx.memAff addr) := by
  have hfl := fixed_layout_order ctx.b ctx.L ctx.vCap ctx.eCap
  have hch := ctx.addr_chain
  obtain ⟨hne, hJE_eq, _, hJt_t, hJt_h, hJt_E, hJt_w, hembCap, _⟩ := stepPosNE_spPre ctx
  rcases hSp with ⟨mid, r₁, hSpPost, hShPost⟩
  rcases hSpPost with ⟨_, _, _, _, _, hargs1, hgb_jt, hjt_q, hq_r1, hr1_lt, hr1_le, hDynJt,
    _, _, hZero1, hFrame1⟩
  simp only [List.take, List.cons.injEq, and_true] at hargs1
  obtain ⟨rfl, rfl, rfl, -, -, rfl, rfl⟩ := hargs1
  rcases hShPost with ⟨_, _, _, _, hargs2, hr1_ret, hret_le, hVSt_sp, hShWalks, hFrame2⟩
  simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
    List.cons.injEq, and_true] at hargs2
  obtain ⟨-, rfl, rfl, -, rfl, rfl⟩ := hargs2
  have hgb_le_q : ctx.guestBase ≤ mid (ctx.scratchPtr + 1) := by omega
  have hgb_le_r1 : ctx.guestBase ≤ r₁ := by omega
  have hscr_ag : ∀ a, ctx.scratchPtr ≤ a → a < ctx.guestBase → memSp a = mid a := by
    intro a ha1 ha2
    refine hFrame2 a ⟨fun v hv => by omega, fun e he => by omega, Or.inl (by omega)⟩
  have hjt_eq : memSp ctx.scratchPtr = mid ctx.scratchPtr :=
    hscr_ag _ (le_refl _) (by omega)
  have hq_eq : memSp (ctx.scratchPtr + 1) = mid (ctx.scratchPtr + 1) :=
    hscr_ag _ (by omega) (by omega)
  have hlt_scr_ag : ∀ addr, addr < ctx.scratchPtr →
      (∀ v < ctx.vCap, addr ≠ dsVStampBase ctx.b ctx.L ctx.vCap ctx.eCap + v) →
      memSp addr = ctx.memAff addr := by
    intro addr hlt hv
    have h2 : memSp addr = mid addr :=
      hFrame2 addr ⟨hv, fun e he => by omega, Or.inl (by omega)⟩
    have h1 : mid addr = ctx.memAff addr :=
      hFrame1 addr (Or.inl hlt) (by omega)
    exact h2.trans h1
  have hgen_mid : mid (ctx.b + dsGenOff) = ctx.memAff (ctx.b + dsGenOff) :=
    hFrame1 _ (Or.inl (by simp [dsGenOff, dsHdrSize] at hfl ⊢; omega))
      (by simp [dsGenOff, dsHdrSize] at hfl ⊢; omega)
  have hVSt_sp' : ∀ v < ctx.vCap,
      memSp (dsVStampBase ctx.b ctx.L ctx.vCap ctx.eCap + v) ≤ ctx.memAff (ctx.b + dsGenOff) := by
    intro v hv; rw [← hgen_mid]; exact hVSt_sp v hv
  have hZeroSp : ZeroFrom memSp retSp := by
    intro a ha
    have h2 : memSp a = mid a :=
      hFrame2 a ⟨fun v hv => by omega, fun e he => by omega, Or.inr ha⟩
    rw [h2]
    exact hZero1 a (le_trans hr1_ret ha)
  have hDynJt_sp : DynGraphAt memSp (memSp ctx.scratchPtr) ctx.vCap ctx.eCap ctx.out.Jtilde := by
    rw [hjt_eq]
    exact dynGraphAt_of_agree hDynJt fun a ha1 ha2 =>
      hFrame2 a ⟨fun v hv => by omega, fun e he => by omega, Or.inl (by omega)⟩
  have hretSp_le : retSp ≤ spOutBound ctx.impl ctx.mMax ctx.vCap ctx.eCap ctx.guestBase
      ctx.G' ctx.J ctx.embJH + dsShortcutHeapSpace ctx.eAff ctx.out.emb := by
    change r₁ ≤ spOutBound ctx.impl ctx.mMax ctx.vCap ctx.eCap ctx.guestBase
      ctx.G' ctx.J ctx.embJH at hr1_le
    change retSp ≤ r₁ + dsShortcutHeapSpace ctx.eAff ctx.out.emb at hret_le
    omega
  have hReEnd : retSp + ctx.eCap +
      reembStageNeed ctx.piLt_mid ctx.embJH ctx.outEmb ctx.eAff < 2 ^ ctx.w := by
    have h1 : spOutBound ctx.impl ctx.mMax ctx.vCap ctx.eCap ctx.guestBase ctx.G' ctx.J ctx.embJH +
        dsShortcutHeapSpace ctx.eAff ctx.out.emb + ctx.eCap +
        reembStageNeed ctx.piLt_mid ctx.embJH ctx.outEmb ctx.eAff < 2 ^ ctx.w :=
      spEnd_add_reemb_lt_of_end ctx.hEnd_ltw
    omega
  have hdu := (batchIsValid_take ctx.us ctx.G₀ ctx.k ctx.hBV ctx.hds).2.2 ctx.u ctx.hu_some
  have hG'val : ctx.G'.IsValid :=
    isValid_applyUpdate_of_delOrSplit ctx.hState.2.2.2.2.1
      ((ctx.hPref ctx.k (le_refl _)).G_eq ▸ hdu.1) hdu.2
  have hGE'_cap : ∀ e ∈ ctx.G'.E, e < ctx.eCap := fun e he =>
    ctx.hState.2.2.2.2.2.2.2.2.2.2.1 e (E_applyUpdate_subset hdu.2 he)
  have hDG'_sp : DynGraphAt memSp (dsGPtr ctx.b) ctx.vCap ctx.eCap ctx.G' := by
    have hDG'_aff := dynGraphAt_of_agree ctx.hG'_graph fun a ha1 ha2 =>
      ctx.hAff_frame a (by omega) (by simp [dsGPtr, dsHdrSize, dsGenOff] at ha1 ⊢; omega)
        (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    exact dynGraphAt_of_agree hDG'_aff fun a ha1 ha2 =>
      hlt_scr_ag a (by omega) (fun v hv => by omega)
  have hPw : ∀ e ∈ ctx.eAff, PrefixWalksValid ctx.G' ctx.S_prev ctx.eCap
      (ctx.G'.tail e) (ctx.G'.head e) (ctx.piLt_mid e) := by
    intro e he
    have heG' : e ∈ ctx.G'.E := (Finset.mem_filter.mp ((ctx.hAff_iff e).mp he)).1
    exact (prefixWalksValid_of_snapInv ctx.hVG₀ ctx.hq ctx.hE₀_cap ctx.hBV ctx.hds ctx.hu_some
      ctx.hPref ctx.hj_pos e heG').1
  have hprojH : projHeapNeed ctx.piLt_mid ctx.eAff ≤ 14 * ctx.lenSum + 15 * ctx.eAff.length :=
    projHeapNeed_le_linear ctx.piLt_mid ctx.eAff
  have hwp_le_scr : ctx.wpPtr + ctx.eAff.length + projHeapNeed ctx.piLt_mid ctx.eAff ≤
      ctx.scratchPtr := by omega
  let rc : RSCtx :=
    { w := ctx.w, vCap := ctx.vCap, eCap := ctx.eCap
      G := ctx.G', embLt := ctx.piLt_mid, embJH := ctx.embJH, outEmb := ctx.outEmb
      S := ctx.S_prev, es := ctx.eAff
      gPtr := dsGPtr ctx.b, sBitPtr := dsSBitBase ctx.b ctx.L ctx.vCap ctx.eCap
      tab := dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap
      piTab := retSp, esPtr := ctx.eAffPtr, wpPtr := ctx.wpPtr
      qTab := memSp (ctx.scratchPtr + 1), heap := retSp + ctx.eCap, mem0 := memSp
      hw16 := ctx.hw16
      hgB := by omega
      hsB := by omega
      htB := by omega
      hpB := by omega
      hesB := by omega
      hwpB := by omega
      hqB := by rw [hq_eq]; omega
      hhB := hReEnd
      dRG := Or.inr (by omega)
      dRS := Or.inr (by omega)
      dRT := Or.inr (by omega)
      dRP := Or.inr (by omega)
      dRE := Or.inr (by omega)
      dRW := Or.inr (by omega)
      dRQ := Or.inr (by rw [hq_eq]; omega)
      dPG := Or.inr (by omega)
      dPS := Or.inr (by omega)
      dPE := Or.inr (by omega)
      dPW := Or.inr (by omega)
      hwalk := fun k' hk' => by
        have hwp_k := ctx.hAff_wp k' hk'
        have hwp_ge : ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ ctx.memAff (ctx.wpPtr + k') :=
          hwp_k.1
        have hwp_len : ctx.memAff (ctx.wpPtr + k') + (2 * (ctx.piLt_mid ctx.eAff[k']).length + 1) ≤
            ctx.heapStep := by
          have h1 : ctx.memAff (ctx.wpPtr + k') +
              (mWalkEncode (ctx.piLt_mid ctx.eAff[k'])).length ≤ ctx.heapStep := hwp_k.2.1
          rw [mWalkEncode_length] at h1; omega
        have hwp_ag : memSp (ctx.wpPtr + k') = ctx.memAff (ctx.wpPtr + k') :=
          hlt_scr_ag _ (by omega) (fun v hv => by omega)
        have hWlt : MWalkAt memSp (memSp (ctx.wpPtr + k')) (ctx.piLt_mid ctx.eAff[k']) := by
          rw [hwp_ag]
          have hwk_at : MWalkAt ctx.memAff (ctx.memAff (ctx.wpPtr + k'))
              (ctx.piLt_mid ctx.eAff[k']) := hwp_k.2.2
          exact hwk_at.of_agree fun a ha1 ha2 =>
            hlt_scr_ag a (by omega) (fun v hv => by omega)
        have hSh_k := hShWalks ctx.eAff[k'] (List.getElem_mem hk')
        have hsh_congr : shortcutWalk ctx.J (ctx.J.tail ctx.eAff[k']) (ctx.out.emb ctx.eAff[k']) =
            ctx.outEmb ctx.eAff[k'] :=
          shortcutWalk_congr_ends hJt_t.symm hJt_h.symm _ _
        rw [hsh_congr] at hSh_k
        have hq_k_eq : memSp (memSp (ctx.scratchPtr + 1) + ctx.eAff[k']) =
            memSp (mid (ctx.scratchPtr + 1) + ctx.eAff[k']) := by rw [hq_eq]
        have hek_J : ctx.eAff[k'] ∈ ctx.J.E := by
          rw [hJE_eq]; exact List.mem_toFinset.mpr (List.getElem_mem hk')
        have hsw_walk : ctx.out.Jtilde.IsWalk (ctx.J.tail ctx.eAff[k']) (ctx.J.head ctx.eAff[k'])
            (ctx.outEmb ctx.eAff[k']) :=
          shortcutWalk_isWalk rfl rfl (hJt_w _ hek_J)
        refine ⟨hWlt, by rw [hwp_ag]; omega,
          Or.inr (by rw [hwp_ag]; omega), Or.inr (by rw [hwp_ag]; omega),
          by rw [hq_k_eq]; exact hSh_k.2.2,
          by rw [hq_k_eq]; omega, Or.inr (by rw [hq_k_eq]; omega),
          fun x hx => ?_⟩
        have hx_Jt : x.1 ∈ ctx.out.Jtilde.E := IsWalk.mem_edge hsw_walk x hx
        have hx_aff : x.1 ∈ ctx.E_aff := hJt_E hx_Jt
        have hx_mem : x.1 ∈ ctx.eAff := (ctx.hAff_iff _).mpr hx_aff
        have hx_emb := ctx.hAff_emb x.1 hx_mem
        have hx_bnd : ctx.memAff (dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap + x.1) +
            (2 * (ctx.embJH x.1).length + 1) ≤ ctx.scratchPtr := by
          have h1 : ctx.memAff (dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap + x.1) +
              (2 * (ctx.embJH x.1).length + 1) ≤
              ctx.wpPtr + ctx.eAff.length + projHeapNeed ctx.piLt_mid ctx.eAff := hx_emb.2.1
          omega
        have hx_cap : x.1 < ctx.eCap := hGE'_cap x.1 (Finset.mem_filter.mp hx_aff).1
        have htab_ag : memSp (dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap + x.1) =
            ctx.memAff (dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap + x.1) :=
          hlt_scr_ag _ (by omega) (fun v hv => by omega)
        have hx_mw : MWalkAt ctx.memAff
            (ctx.memAff (dsMEmbTempBase ctx.b ctx.L ctx.vCap ctx.eCap + x.1)) (ctx.embJH x.1) :=
          hx_emb.2.2
        refine ⟨hx_cap,
          by rw [htab_ag]; exact hx_mw.of_agree fun a ha1 ha2 =>
            hlt_scr_ag a (by omega) (fun v hv => by omega),
          by rw [htab_ag]; omega, Or.inr (by rw [htab_ag]; omega),
          fun y hy => hembCap x.1 hx_aff y hy⟩
      hG := hDG'_sp
      hGv := hG'val
      hVc := ctx.hGV'_cap
      hEc := hGE'_cap
      hes := listAt_of_agree (fun k' hk' =>
        hlt_scr_ag _ (by omega) (fun v hv => by omega)) ctx.hAff_at
      hnd := ctx.hAff_eNd
      hesG := fun e he => (Finset.mem_filter.mp ((ctx.hAff_iff e).mp he)).1
      hPw := hPw
      hsBit := fun v hv => by
        rw [hlt_scr_ag _ (by omega) (fun v' hv' => by omega)]
        exact ctx.hAff_sBit v hv }
  exact ⟨rc, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, hjt_eq ▸ hgb_jt, hjt_eq ▸ hq_eq ▸ hjt_q, hq_eq ▸ le_trans hq_r1 hr1_ret, hretSp_le,
    hDynJt_sp, hZeroSp, hVSt_sp', hlt_scr_ag⟩

end

end MinCostFlow.DynSpanner.Program
