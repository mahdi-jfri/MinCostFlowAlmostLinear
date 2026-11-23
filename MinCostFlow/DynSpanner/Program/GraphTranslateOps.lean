module

public import MinCostFlow.DynSpanner.Program.GraphTranslateEmitWalk
public import MinCostFlow.DynSpanner.Program.DynGraphBatch

/-!
# Forward Graph Translation Operations (`GraphTranslateOps`)

Defines and verifies the scratch-preparation half of the forward graph-translation pipeline:

* `dgApplyBatch_small_cost_le`: bounds `dgApplyBatchContract.cost` by `3350 * G.batchEnc U + 700`
  for any `SmallBatchAt` encoding.
* `gtForwardCoreScratchStmt` / `gtForwardCoreEmitStmt` / `gtForwardCoreStmt`: computes
  `hEs` (`vertsOf (usedHEdges J emb)`) and `exVs` (`vertsOf (usedHVerts H' J emb \ J.V)`)
  inside `[scratchPtr, scratchPtr + 5 * rawEsLen + 3 * J.m)`, then emits
  `canonSparsifyInput H' J emb` at `outPtr`.
* `gtForwardCore_scratchPhase`: `Triple` correctness and time bound for `gtForwardCoreScratchStmt`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner

@[expose] public section

lemma collectRawVsFun_length_eq (H' : MGraph) (jEs jTails : List ℕ)
    (emb : MinCostFlow.Embedding) :
    (collectRawVsFun H' jEs jTails emb).length = jEs.length + (collectRawEsFun jEs emb).length := by
  unfold collectRawVsFun collectRawEsFun
  have hL : ∀ k, k ≤ jEs.length →
      ((List.range k).flatMap fun j => H'.walkVertices (jTails.getD j 0) (emb (jEs.getD j 0))).length =
        k + ((jEs.take k).flatMap fun e => (emb e).map Prod.fst).length := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hk' : k < jEs.length := hk
      rw [List.range_succ, List.flatMap_append, List.length_append, ih (Nat.le_of_lt hk'),
        List.take_succ_eq_append_getElem hk', List.flatMap_append, List.length_append]
      simp only [List.flatMap_singleton, MGraph.walkVertices, List.length_cons, List.length_map,
        List.getD_eq_getElem _ _ hk']
      omega
  simpa using hL jEs.length le_rfl

lemma mgraph_usedEdges_in_H {H' J : MGraph} {emb : MinCostFlow.Embedding}
    (hemb : emb.IsEmbedding J H') :
    ∀ e ∈ usedHEdges J emb, e ∈ H'.E := by
  intro e he
  simp only [usedHEdges, Finset.mem_biUnion, MinCostFlow.walkEdges, List.mem_toFinset,
    List.mem_map] at he
  rcases he with ⟨eJ, heJ, x, hx, rfl⟩
  exact (mgraph_mem_walkVertices_src_dst (hemb.2 eJ heJ) x hx).1

lemma mgraph_usedEdge_ends_in_usedHVerts {H' J : MGraph} {emb : MinCostFlow.Embedding}
    (hemb : emb.IsEmbedding J H') :
    ∀ e ∈ usedHEdges J emb, H'.tail e ∈ usedHVerts H' J emb ∧ H'.head e ∈ usedHVerts H' J emb := by
  intro e he
  simp only [usedHEdges, Finset.mem_biUnion, MinCostFlow.walkEdges, List.mem_toFinset,
    List.mem_map] at he
  rcases he with ⟨eJ, heJ, ⟨e', dir⟩, hx, rfl⟩
  have hstep := mgraph_mem_walkVertices_src_dst (hemb.2 eJ heJ) (e', dir) hx
  have hmem : ∀ v, v ∈ H'.walkVertices (J.tail eJ) (emb eJ) → v ∈ usedHVerts H' J emb := by
    intro v hv
    simp only [usedHVerts, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset]
    exact Or.inr ⟨eJ, heJ, hv⟩
  have hsrc : H'.src (e', dir) ∈ usedHVerts H' J emb := hmem _ hstep.2.1
  have hdst : H'.dst (e', dir) ∈ usedHVerts H' J emb := hmem _ hstep.2.2
  cases dir
  · exact ⟨hdst, hsrc⟩
  · exact ⟨hsrc, hdst⟩

lemma mgraph_usedHVerts_sub_HV {H' J : MGraph} {emb : MinCostFlow.Embedding}
    (hH' : H'.IsValid) (hJ : J.IsValid) (hemb : emb.IsEmbedding J H') :
    usedHVerts H' J emb ⊆ H'.V := by
  intro v hv
  simp only [usedHVerts, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset] at hv
  rcases hv with hvJ | ⟨eJ, heJ, hvW⟩
  · exact hemb.1 hvJ
  · exact mgraph_walkVertices_subset hH' (hemb.2 eJ heJ) (hemb.1 (hJ eJ heJ).1) _ hvW

lemma usedHVerts_sdiff_eq_rawVs {H' J : MGraph} {jEs jTails : List ℕ}
    {emb : MinCostFlow.Embedding}
    (hLen : jTails.length = jEs.length)
    (hjE : ∀ e, e ∈ jEs ↔ e ∈ J.E)
    (htail : ∀ j (hj : j < jEs.length), jTails.getD j 0 = J.tail (jEs[j]'hj)) :
    (collectRawVsFun H' jEs jTails emb).toFinset \ J.V = usedHVerts H' J emb \ J.V := by
  ext x
  simp only [Finset.mem_sdiff, List.mem_toFinset]
  have hmem := collectRawVsFun_mem (H' := H') (emb := emb) hLen hjE (fun j hj => by
    have := htail j hj
    rwa [List.getD_eq_getElem _ _ (by omega)] at this) x
  tauto

lemma vertsOf_usedHVerts_card_le {H' J : MGraph} {emb : MinCostFlow.Embedding}
    (hH' : H'.IsValid) (hJ : J.IsValid) (hemb : emb.IsEmbedding J H') :
    (vertsOf J.V).length + (vertsOf (usedHVerts H' J emb \ J.V)).length ≤ H'.n := by
  rw [vertsOf_length, vertsOf_length]
  have h1 : Finset.card J.V + Finset.card (usedHVerts H' J emb \ J.V) =
      Finset.card (J.V ∪ (usedHVerts H' J emb \ J.V)) := by
    rw [Finset.card_union_of_disjoint]
    exact disjoint_sdiff_self_right
  rw [h1]
  have h2 : J.V ∪ (usedHVerts H' J emb \ J.V) ⊆ H'.V := by
    refine Finset.union_subset hemb.1 ?_
    exact Finset.sdiff_subset.trans (mgraph_usedHVerts_sub_HV hH' hJ hemb)
  exact Finset.card_le_card h2

lemma dynGraph_n_le_vCap {mem : ℕ → ℕ} {a vCap eCap : ℕ} {G : MGraph}
    (hDyn : DynGraphAt mem a vCap eCap G) : G.n ≤ vCap := by
  have hsub : G.V ⊆ Finset.range vCap := fun v hv => Finset.mem_range.mpr (hDyn.2.1 v hv)
  calc G.n = G.V.card := rfl
    _ ≤ (Finset.range vCap).card := Finset.card_le_card hsub
    _ = vCap := Finset.card_range vCap

lemma dynGraph_m_le_eCap {mem : ℕ → ℕ} {a vCap eCap : ℕ} {G : MGraph}
    (hDyn : DynGraphAt mem a vCap eCap G) : G.m ≤ eCap := by
  have hsub : G.E ⊆ Finset.range eCap := fun e he => Finset.mem_range.mpr (hDyn.2.2.1 e he)
  calc G.m = G.E.card := rfl
    _ ≤ (Finset.range eCap).card := Finset.card_le_card hsub
    _ = eCap := Finset.card_range eCap

lemma embToCited_dataLen_le {H' J : MGraph} {jEs : List ℕ} {emb : MinCostFlow.Embedding}
    (hjE : jEs = vertsOf J.E) :
    (((List.range jEs.length).map (embToCited H' J emb)).flatMap Walk.encode).length ≤
      2 * (collectRawEsFun jEs emb).length + 3 * jEs.length := by
  have h1 : ∀ k ≤ jEs.length,
      (((List.range k).map (embToCited H' J emb)).flatMap Walk.encode).length ≤
        2 * ((jEs.take k).flatMap fun e => (emb e).map Prod.fst).length + 3 * k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hk' : k < jEs.length := hk
      rw [List.range_succ, List.map_append, List.flatMap_append, List.length_append,
        List.take_succ_eq_append_getElem hk', List.flatMap_append, List.length_append]
      simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.length_map]
      have ih' := ih (Nat.le_of_lt hk')
      by_cases h0 : emb (jEs[k]'hk') = []
      · have he : embToCited H' J emb k =
            walkToCited H' (hVerts H' J emb) (hEdges J emb) (J.tail (jEs[k]'hk')) [] := by
          dsimp only [embToCited]
          rw [← hjE, List.getD_eq_getElem _ _ hk', h0]
        rw [he, walkToCited_empty_encode, h0]
        simp only [List.length_cons, List.length_nil]
        omega
      · have he_enc := walkToCited_nonempty_encode H' (hVerts H' J emb) (hEdges J emb)
          (J.tail (jEs[k]'hk')) (emb (jEs[k]'hk')) h0
        have he' : embToCited H' J emb k =
            walkToCited H' (hVerts H' J emb) (hEdges J emb)
              (J.tail (jEs[k]'hk')) (emb (jEs[k]'hk')) := by
          dsimp only [embToCited]
          rw [← hjE, List.getD_eq_getElem _ _ hk']
        rw [he', he_enc]
        simp only [List.length_cons, List.length_append, List.length_map, List.length_range]
        omega
  simpa [collectRawEsFun] using h1 jEs.length le_rfl

/-- Procedure index of `gtForwardCoreStmt` inside `gtForwardProcs`. -/
def gtIdxForwardCore : ℕ := 0

/-- Procedure index of `gtForwardDynStmt` inside `gtForwardProcs`. -/
def gtIdxForwardDyn : ℕ := 1

/-- Scratch word budget required by `gtForwardCoreStmt`. -/
def gtFwdCoreScratchLen (mJ rawEsLen : ℕ) : ℕ :=
  5 * rawEsLen + 3 * mJ

/-- `dgApplyBatch` cost corollary for any `SmallBatchAt` input encoding (`≤ 3350 * G.batchEnc U + 700`). -/
theorem dgApplyBatch_small_cost_le {w vCap eCap : ℕ} {mem : ℕ → ℕ} {batchPtr : ℕ}
    {G H : MGraph} {U : List Update} {totalWords : ℕ}
    (hSmall : SmallBatchAt mem batchPtr G U totalWords)
    (args : List ℕ) (mem' : ℕ → ℕ) :
    (dgApplyBatchContract w vCap eCap G H U totalWords).cost args mem' ≤
      3350 * G.batchEnc U + 700 := by
  dsimp only [dgApplyBatchContract]
  have htw := hSmall.2
  omega

/-- Scratch-computation phase of `gtForwardCoreStmt`: computes sorted `hEs` at `reg 12` (len `reg 14`)
and sorted `exVs` at `reg 20` (len `reg 21`). -/
def gtForwardCoreScratchStmt (bGT : ℕ) : Stmt :=
  .assign 10 (.reg 8) ;;
  .call 11 (bGT + gtIdxCollectRawEs) [.reg 2, .reg 4, .reg 7, .reg 10] ;;
  .assign 12 (.bin .add (.reg 10) (.reg 11)) ;;
  .assign 13 (.bin .add (.reg 12) (.reg 11)) ;;
  .call 14 (bGT + gtIdxSortDedup) [.reg 10, .reg 11, .reg 12, .reg 13] ;;
  .assign 15 (.bin .add (.reg 12) (.reg 14)) ;;
  .call 16 (bGT + gtIdxCollectRawVs) [.reg 0, .reg 2, .reg 4, .reg 5, .reg 7, .reg 15] ;;
  .assign 17 (.bin .add (.reg 15) (.reg 16)) ;;
  .assign 18 (.bin .add (.reg 17) (.reg 16)) ;;
  .call 19 (bGT + gtIdxSortDedup) [.reg 15, .reg 16, .reg 17, .reg 18] ;;
  .assign 20 (.bin .add (.reg 17) (.reg 19)) ;;
  .call 21 (bGT + gtIdxSortedDiff) [.reg 17, .reg 19, .reg 3, .reg 1, .reg 20]

/-- Emission phase of `gtForwardCoreStmt`: writes `[3, pJ, pEmb]`, `toCitedH`, `toCitedJ`, and
`embToCited` at `outPtr` (`reg 9`) and returns total encoded length. -/
def gtForwardCoreEmitStmt (bEmit : ℕ) : Stmt :=
  .assign 22 (.bin .add (.const 5) (.bin .mul (.const 2) (.reg 14))) ;;
  .assign 23 (.bin .add (.reg 22) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 2)))) ;;
  .assign 24 (.bin .add (.reg 23) (.reg 2)) ;;
  .store (.reg 9) (.const 3) ;;
  .store (.bin .add (.reg 9) (.const 1)) (.reg 22) ;;
  .store (.bin .add (.reg 9) (.const 2)) (.reg 23) ;;
  .call 25 (bEmit + gtIdxEmitCitedH)
    [.reg 0, .reg 1, .reg 20, .reg 21, .reg 12, .reg 14, .reg 3, .bin .add (.reg 9) (.const 3)] ;;
  .call 25 (bEmit + gtIdxEmitCitedJ)
    [.reg 2, .reg 3, .reg 1, .reg 5, .reg 6, .bin .add (.reg 9) (.reg 22)] ;;
  .call 25 (bEmit + gtIdxEmitEmbToCited)
    [.reg 0, .reg 2, .reg 4, .reg 5, .reg 7, .reg 3, .reg 1, .reg 20, .reg 21, .reg 12, .reg 14,
     .bin .add (.reg 9) (.reg 23), .bin .add (.reg 9) (.reg 24), .reg 24] ;;
  .ret (.bin .add (.reg 24) (.reg 25))

/-- Deterministic Word-RAM forward core translator:
`[hPtr, nJ, mJ, jVsPtr, jEsPtr, jTailsPtr, jHeadsPtr, mEmbPtr, scratchPtr, outPtr]`. -/
def gtForwardCoreStmt (bGT bEmit : ℕ) : Stmt :=
  gtForwardCoreScratchStmt bGT ;; gtForwardCoreEmitStmt bEmit

/-- Contract for `gtForwardCoreStmt`. -/
def gtForwardCoreContract (w vCap eCap : ℕ) (H' J : MGraph) (emb : MinCostFlow.Embedding)
    (jVs jEs jTails jHeads : List ℕ) : Contract where
  pre args mem := ∃ hPtr jVsPtr jEsPtr jTailsPtr jHeadsPtr mEmbPtr scratchPtr outPtr,
    let rawEsLen := (collectRawEsFun jEs emb).length
    let sLen := gtFwdCoreScratchLen jEs.length rawEsLen
    let outLen := (canonSparsifyInput H' J emb).length
    args = [hPtr, jVs.length, jEs.length, jVsPtr, jEsPtr, jTailsPtr, jHeadsPtr,
      mEmbPtr, scratchPtr, outPtr] ∧
    16 ≤ 2 ^ w ∧
    hPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    jVsPtr + jVs.length < 2 ^ w ∧ jEsPtr + jEs.length < 2 ^ w ∧
    jTailsPtr + jEs.length < 2 ^ w ∧ jHeadsPtr + jEs.length < 2 ^ w ∧
    mEmbPtr + eCap < 2 ^ w ∧
    scratchPtr + sLen < 2 ^ w ∧
    outPtr + outLen < 2 ^ w ∧
    let dis := fun addr =>
      (addr < scratchPtr ∨ scratchPtr + sLen ≤ addr) ∧
      (addr < outPtr ∨ outPtr + outLen ≤ addr)
    (scratchPtr + sLen ≤ outPtr ∨ outPtr + outLen ≤ scratchPtr) ∧
    (∀ i < dynGraphSize vCap eCap, dis (hPtr + i)) ∧
    (∀ i < jVs.length, dis (jVsPtr + i)) ∧
    (∀ i < jEs.length, dis (jEsPtr + i)) ∧
    (∀ i < jEs.length, dis (jTailsPtr + i)) ∧
    (∀ i < jEs.length, dis (jHeadsPtr + i)) ∧
    (∀ e ∈ J.E, dis (mEmbPtr + e)) ∧
    (∀ e ∈ J.E, ∀ k < (mWalkEncode (emb e)).length, dis (mem (mEmbPtr + e) + k)) ∧
    DynGraphAt mem hPtr vCap eCap H' ∧ J.IsValid ∧ emb.IsEmbedding J H' ∧
    jVs = vertsOf J.V ∧ jEs = vertsOf J.E ∧
    jTails.length = jEs.length ∧ jHeads.length = jEs.length ∧
    (∀ i (hi : i < jEs.length),
      jTails.getD i 0 = J.tail (jEs[i]'hi) ∧ jHeads.getD i 0 = J.head (jEs[i]'hi)) ∧
    MEmbAt mem mEmbPtr J.E eCap emb ∧
    ListAt mem jVsPtr jVs ∧ ListAt mem jEsPtr jEs ∧
    ListAt mem jTailsPtr jTails ∧ ListAt mem jHeadsPtr jHeads ∧
    (∀ e ∈ J.E, (emb e).length < 2 ^ w ∧ mem (mEmbPtr + e) + (mWalkEncode (emb e)).length < 2 ^ w)
  post args mem ret mem' := ∃ hPtr jVsPtr jEsPtr jTailsPtr jHeadsPtr mEmbPtr scratchPtr outPtr,
    let rawEsLen := (collectRawEsFun jEs emb).length
    let sLen := gtFwdCoreScratchLen jEs.length rawEsLen
    let outLen := (canonSparsifyInput H' J emb).length
    args = [hPtr, jVs.length, jEs.length, jVsPtr, jEsPtr, jTailsPtr, jHeadsPtr,
      mEmbPtr, scratchPtr, outPtr] ∧
    ret = outLen ∧
    ListAt mem' outPtr (canonSparsifyInput H' J emb) ∧
    ∀ addr, (addr < scratchPtr ∨ scratchPtr + sLen ≤ addr) →
      (addr < outPtr ∨ outPtr + outLen ≤ addr) → mem' addr = mem addr
  cost _ _ :=
    let rawEsLen := (collectRawEsFun jEs emb).length
    let lArg := jVs.length + 2 * rawEsLen + jEs.length + 2
    1180 * (rawEsLen + jEs.length) * (Nat.log 2 lArg + 1) +
      950 * (jVs.length + jEs.length + rawEsLen) + 800

/-- Precondition for `gtForwardCore_scratchPhase`. -/
def gtScratchPre (w vCap eCap : ℕ) (H' J : MGraph) (emb : MinCostFlow.Embedding)
    (jVs jEs jTails : List ℕ)
    (hPtr jVsPtr jEsPtr jTailsPtr jHeadsPtr mEmbPtr scratchPtr outPtr : ℕ)
    (mem : ℕ → ℕ) (st : State) : Prop :=
  let rawEsLen := (collectRawEsFun jEs emb).length
  let sLen := gtFwdCoreScratchLen jEs.length rawEsLen
  16 ≤ 2 ^ w ∧
  hPtr + dynGraphSize vCap eCap < 2 ^ w ∧
  jVsPtr + jVs.length < 2 ^ w ∧ jEsPtr + jEs.length < 2 ^ w ∧
  jTailsPtr + jEs.length < 2 ^ w ∧ mEmbPtr + eCap < 2 ^ w ∧
  scratchPtr + sLen < 2 ^ w ∧
  (∀ i < dynGraphSize vCap eCap, hPtr + i < scratchPtr ∨ scratchPtr + sLen ≤ hPtr + i) ∧
  (∀ i < jVs.length, jVsPtr + i < scratchPtr ∨ scratchPtr + sLen ≤ jVsPtr + i) ∧
  (∀ i < jEs.length, jEsPtr + i < scratchPtr ∨ scratchPtr + sLen ≤ jEsPtr + i) ∧
  (∀ i < jEs.length, jTailsPtr + i < scratchPtr ∨ scratchPtr + sLen ≤ jTailsPtr + i) ∧
  (∀ e ∈ J.E, mEmbPtr + e < scratchPtr ∨ scratchPtr + sLen ≤ mEmbPtr + e) ∧
  (∀ e ∈ J.E, ∀ k < (mWalkEncode (emb e)).length,
    mem (mEmbPtr + e) + k < scratchPtr ∨ scratchPtr + sLen ≤ mem (mEmbPtr + e) + k) ∧
  DynGraphAt mem hPtr vCap eCap H' ∧ J.IsValid ∧ emb.IsEmbedding J H' ∧
  jVs = vertsOf J.V ∧ jEs = vertsOf J.E ∧ jTails.length = jEs.length ∧
  (∀ i (hi : i < jEs.length), jTails.getD i 0 = J.tail (jEs[i]'hi)) ∧
  MEmbAt mem mEmbPtr J.E eCap emb ∧
  ListAt mem jVsPtr jVs ∧ ListAt mem jEsPtr jEs ∧ ListAt mem jTailsPtr jTails ∧
  (∀ e ∈ J.E, (emb e).length < 2 ^ w ∧ mem (mEmbPtr + e) + (mWalkEncode (emb e)).length < 2 ^ w) ∧
  st.mem = mem ∧ st.regs 0 = hPtr ∧ st.regs 1 = jVs.length ∧ st.regs 2 = jEs.length ∧
  st.regs 3 = jVsPtr ∧ st.regs 4 = jEsPtr ∧ st.regs 5 = jTailsPtr ∧
  st.regs 6 = jHeadsPtr ∧ st.regs 7 = mEmbPtr ∧ st.regs 8 = scratchPtr ∧ st.regs 9 = outPtr

/-- Postcondition for `gtForwardCore_scratchPhase`. -/
def gtScratchPost (H' J : MGraph) (emb : MinCostFlow.Embedding) (jEs jTails : List ℕ)
    (hPtr jVsPtr jEsPtr jTailsPtr jHeadsPtr mEmbPtr scratchPtr outPtr nJ : ℕ)
    (mem : ℕ → ℕ) (st' : State) : Prop :=
  let hEs := vertsOf (usedHEdges J emb)
  let exVs := vertsOf (usedHVerts H' J emb \ J.V)
  let rawEsLen := (collectRawEsFun jEs emb).length
  let hEsPtr := scratchPtr + rawEsLen
  let exVsPtr := hEsPtr + hEs.length + (jEs.length + rawEsLen) +
    (vertsOf (collectRawVsFun H' jEs jTails emb).toFinset).length
  st'.regs 0 = hPtr ∧ st'.regs 1 = nJ ∧ st'.regs 2 = jEs.length ∧
  st'.regs 3 = jVsPtr ∧ st'.regs 4 = jEsPtr ∧ st'.regs 5 = jTailsPtr ∧
  st'.regs 6 = jHeadsPtr ∧ st'.regs 7 = mEmbPtr ∧ st'.regs 8 = scratchPtr ∧
  st'.regs 9 = outPtr ∧
  st'.regs 12 = hEsPtr ∧ st'.regs 14 = hEs.length ∧
  st'.regs 20 = exVsPtr ∧ st'.regs 21 = exVs.length ∧
  ListAt st'.mem hEsPtr hEs ∧ ListAt st'.mem exVsPtr exVs ∧
  hEsPtr + hEs.length ≤ exVsPtr ∧
  exVsPtr + exVs.length ≤ scratchPtr + gtFwdCoreScratchLen jEs.length rawEsLen ∧
  ∀ addr, addr < scratchPtr ∨
    scratchPtr + gtFwdCoreScratchLen jEs.length rawEsLen ≤ addr → st'.mem addr = mem addr

private lemma runs_call_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {C : Contract} {st : State} {vs : List ℕ} {k T : ℕ} {Q : Outcome → State → Prop}
    (hf : MeetsContract w p f C)
    (hargs : evalArgs w st args = some vs)
    (hwords : ∀ v ∈ vs, v < 2 ^ w)
    (hpre : C.pre vs st.mem)
    (hrest : ∀ v mem' pos', C.post vs st.mem v mem' →
      Q .normal (State.mk mem' (Function.update st.regs r v) pos') ∧
      (k + argsSize args + C.cost vs st.mem + 1) ≤ T) :
    ∃ o st' c, Runs w p ω (.call r f args) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases runs_call_of_meetsContract (r := r) hf hargs hwords hpre ω with
    ⟨st₁, c₁, v, hr₁, hcpost, hr, hother, hcost⟩
  have hst₁ : st₁ = State.mk st₁.mem (Function.update st.regs r v) st₁.pos := by
    cases st₁
    dsimp only at hr hother
    congr 1
    funext x
    by_cases hx : x = r
    · subst hx; simp [hr]
    · simp [Function.update_of_ne hx, hother x hx]
  rcases hrest v st₁.mem st₁.pos hcpost with ⟨hq, hbd⟩
  exact ⟨.normal, st₁, c₁, hr₁, hst₁ ▸ hq, by omega⟩

theorem gtForwardCore_scratchPhase {w vCap eCap : ℕ} {p : Program} {bSort bOps bGT : ℕ}
    {H' J : MGraph} {emb : MinCostFlow.Embedding} {jVs jEs jTails : List ℕ}
    {hPtr jVsPtr jEsPtr jTailsPtr jHeadsPtr mEmbPtr scratchPtr outPtr : ℕ}
    {mem : ℕ → ℕ}
    (hpGT : p.HasAt bGT (gtProcs bSort bOps))
    (hpSort : p.HasAt bSort (sortProcs bSort))
    (hpOps : p.HasAt bOps dgOpsProcs) :
    Triple w p
      (gtScratchPre w vCap eCap H' J emb jVs jEs jTails
        hPtr jVsPtr jEsPtr jTailsPtr jHeadsPtr mEmbPtr scratchPtr outPtr mem)
      (gtForwardCoreScratchStmt bGT)
      (normalPost (gtScratchPost H' J emb jEs jTails
        hPtr jVsPtr jEsPtr jTailsPtr jHeadsPtr mEmbPtr scratchPtr outPtr jVs.length mem))
      (fun _ =>
        let rawEsLen := (collectRawEsFun jEs emb).length
        500 * rawEsLen * (Nat.log 2 (rawEsLen + 1) + 1) +
        250 * (rawEsLen + jEs.length) * (Nat.log 2 (rawEsLen + jEs.length + 1) + 1) +
        200 * (rawEsLen + jEs.length) + 50 * jVs.length + 460) := by
  intro st ω hPre
  rcases hPre with ⟨hw16, hhB, hjVB, hjEB, hjTB, hmEB, hscB,
    hdisjH, hdisjV, hdisjE, hdisjT, hdisjME, hdisjW,
    hDynH, hJ, hemb, hjV, hjE, hLenT, hT, hmEmb, hjAt, hjEAt, hjTAt, hwLens,
    hmemEq, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9⟩
  subst hmemEq
  let rawEs := collectRawEsFun jEs emb
  let rawEsLen := (collectRawEsFun jEs emb).length
  let sLen := gtFwdCoreScratchLen jEs.length rawEsLen
  let hEs := vertsOf (usedHEdges J emb)
  let rawVs := collectRawVsFun H' jEs jTails emb
  let rawVsLen := rawVs.length
  let uRawSet := rawVs.toFinset
  let uRaw := vertsOf uRawSet
  let exVs := vertsOf (usedHVerts H' J emb \ J.V)
  have hjE_iff : ∀ e, e ∈ jEs ↔ e ∈ J.E := by intro e; simp [hjE, mem_vertsOf]
  have hrawVs_len : rawVsLen = jEs.length + rawEsLen :=
    collectRawVsFun_length_eq H' jEs jTails emb
  have hmH_le : hEs.length ≤ rawEsLen := by
    rw [vertsOf_length]
    have hsub : usedHEdges J emb ⊆ rawEs.toFinset := fun x hx => by
      rw [List.mem_toFinset]; exact (collectRawEsFun_mem hjE_iff x).mpr hx
    exact (Finset.card_le_card hsub).trans (List.toFinset_card_le rawEs)
  have huRaw_le : uRaw.length ≤ rawVsLen := by
    rw [vertsOf_length]; exact List.toFinset_card_le rawVs
  have hex_eq : uRawSet \ J.V = usedHVerts H' J emb \ J.V :=
    usedHVerts_sdiff_eq_rawVs hLenT hjE_iff hT
  have hex_le : exVs.length ≤ uRaw.length := by
    rw [vertsOf_length, vertsOf_length, ← hex_eq]
    exact Finset.card_le_card Finset.sdiff_subset
  have hlt_hP : hPtr < 2 ^ w := by omega
  have hlt_nJ : jVs.length < 2 ^ w := by omega
  have hlt_mJ : jEs.length < 2 ^ w := by omega
  have hlt_jVP : jVsPtr < 2 ^ w := by omega
  have hlt_jEP : jEsPtr < 2 ^ w := by omega
  have hlt_jTP : jTailsPtr < 2 ^ w := by omega
  have hlt_mEP : mEmbPtr < 2 ^ w := by omega
  have hlt_scP : scratchPtr < 2 ^ w := by omega
  have hrawEs_ltw : rawEsLen < 2 ^ w := by
    dsimp [sLen, gtFwdCoreScratchLen] at hscB; omega
  have hrawVs_ltw : rawVsLen < 2 ^ w := by
    dsimp [rawVsLen, hrawVs_len, sLen, gtFwdCoreScratchLen] at hscB ⊢; omega
  have hvCap_ltw : vCap < 2 ^ w := by
    have : vCap ≤ dynGraphSize vCap eCap := by unfold dynGraphSize; omega
    omega
  have heCap_ltw : eCap < 2 ^ w := by
    have : eCap ≤ dynGraphSize vCap eCap := by unfold dynGraphSize; omega
    omega
  refine runs_start_le ?_
  dsimp only [gtForwardCoreScratchStmt]
  -- 1. assign 10 := scratchPtr
  refine runs_seq_assign_le (v := scratchPtr) (by simp [Expr.eval, r8]) ?_
  -- 2. call 11 gtCollectRawEs [mJ, jEsPtr, mEmbPtr, scratchPtr]
  refine runs_seq_call_le (gtCollectRawEs_meetsContract hpGT)
    (vs := [jEs.length, jEsPtr, mEmbPtr, scratchPtr])
    (by
      simp only [evalArgs, Expr.eval]
      simp (disch := decide) only [Function.update_of_ne, Function.update_self, r2, r4, r7])
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl <;> assumption)
    ⟨jEsPtr, mEmbPtr, scratchPtr, rfl, hw16, hjEB, hmEB,
      by dsimp [sLen, gtFwdCoreScratchLen] at hscB; omega,
      fun i hi => by have := hdisjE i hi; rcases this with h | h <;> [left; right] <;> dsimp [sLen, gtFwdCoreScratchLen] at * <;> omega,
      fun e he => by have := hdisjME e he; rcases this with h | h <;> [left; right] <;> dsimp [sLen, gtFwdCoreScratchLen] at * <;> omega,
      fun e he k hk => by have := hdisjW e he k hk; rcases this with h | h <;> [left; right] <;> dsimp [sLen, gtFwdCoreScratchLen] at * <;> omega,
      hjE_iff, hmEmb, hjEAt,
      fun e he x hx => lt_trans (hDynH.2.2.1 x.1 (mgraph_mem_walkVertices_src_dst (hemb.2 e he) x hx).1) heCap_ltw,
      hwLens⟩
    ?_
  intro ret1 mem1 pos1 ⟨_, _, _, hargs1, hret1, hrawEsAt1, hfr1⟩
  simp only [List.cons.injEq, and_true] at hargs1
  rcases hargs1 with ⟨_, rfl, rfl, rfl⟩
  subst hret1
  have hfr1_out : ∀ addr, addr < scratchPtr ∨ scratchPtr + sLen ≤ addr → mem1 addr = st.mem addr :=
    fun addr ha => hfr1 addr (by rcases ha with h | h <;> [left; right] <;> dsimp [sLen, gtFwdCoreScratchLen, rawEsLen] at * <;> omega)
  -- 3. assign 12 := hEsPtr, 4. assign 13 := sortS1
  let hEsPtr := scratchPtr + rawEsLen
  let sortS1 := hEsPtr + rawEsLen
  have hhEsP_ltw : hEsPtr < 2 ^ w := by dsimp [hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen] at *; omega
  have hsort1_ltw : sortS1 < 2 ^ w := by dsimp [sortS1, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen] at *; omega
  refine runs_seq_assign_le (v := hEsPtr)
    (by
      simp only [Expr.eval, BinOp.eval]
      simp (disch := decide) only [Function.update_of_ne, Function.update_self]
      exact ite_eq_left_iff.mpr fun hbad => False.elim (hbad hhEsP_ltw)) ?_
  refine runs_seq_assign_le (v := sortS1)
    (by
      simp only [Expr.eval, BinOp.eval]
      simp (disch := decide) only [Function.update_of_ne, Function.update_self]
      exact ite_eq_left_iff.mpr fun hbad => False.elim (hbad hsort1_ltw)) ?_
  -- 5. call 14 gtSortDedup [scratchPtr, rawEsLen, hEsPtr, sortS1]
  have hrawEs_w : ∀ x ∈ rawEs, x < 2 ^ w := fun x hx => by
    rw [collectRawEsFun_mem hjE_iff] at hx
    exact lt_trans (hDynH.2.2.1 x (mgraph_usedEdges_in_H hemb x hx)) heCap_ltw
  refine runs_seq_call_le (gtSortDedup_meetsContract hpGT hpSort)
    (vs := [scratchPtr, rawEsLen, hEsPtr, sortS1])
    (by
      simp only [evalArgs, Expr.eval]
      simp (disch := decide) only [Function.update_of_ne, Function.update_self]
      rfl)
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl <;> assumption)
    ⟨scratchPtr, hEsPtr, sortS1, rfl, hw16,
      by dsimp [hEsPtr, sortS1, sLen, gtFwdCoreScratchLen, rawEsLen] at *; omega,
      by dsimp [hEsPtr, sortS1, sLen, gtFwdCoreScratchLen, rawEsLen] at *; omega,
      by dsimp [hEsPtr, sortS1, sLen, gtFwdCoreScratchLen, rawEsLen] at *; omega,
      Or.inl (by dsimp [hEsPtr, sortS1]; omega),
      Or.inl (by dsimp [hEsPtr]; omega),
      hrawEsAt1, hrawEs_w, fun x => collectRawEsFun_mem hjE_iff x⟩
    ?_
  intro ret2 mem2 pos2 ⟨_, _, _, hargs2, hret2, hhEsAt2, hfr2⟩
  simp only [List.cons.injEq, and_true] at hargs2
  rcases hargs2 with ⟨rfl, _, rfl, rfl⟩
  subst hret2
  have hmH_ltw : hEs.length < 2 ^ w := by omega
  have hhEs_le : (vertsOf (usedHEdges J emb)).length ≤ rawEsLen := hmH_le
  have hfr2_out : ∀ addr, addr < scratchPtr ∨ scratchPtr + sLen ≤ addr → mem2 addr = st.mem addr := by
    intro addr ha
    exact (hfr2 addr
      (by rcases ha with h | h <;> [left; right] <;> dsimp [sLen, gtFwdCoreScratchLen, rawEsLen] at * <;> omega)
      (by rcases ha with h | h <;> [left; right] <;> dsimp [sortS1, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen] at * <;> omega)
      (by rcases ha with h | h <;> [left; right] <;> dsimp [hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen] at * <;> omega)).trans (hfr1_out addr ha)
  -- 6. assign 15 := rawVsPtr (= hEsPtr + hEs.length)
  let rawVsPtr := hEsPtr + hEs.length
  have hrawVsP_ltw : rawVsPtr < 2 ^ w := by dsimp [rawVsPtr, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen] at *; omega
  refine runs_seq_assign_le (v := rawVsPtr)
    (by
      simp only [Expr.eval, BinOp.eval]
      simp (disch := decide) only [Function.update_of_ne, Function.update_self]
      exact ite_eq_left_iff.mpr fun hbad => False.elim (hbad hrawVsP_ltw)) ?_
  -- 7. call 16 gtCollectRawVs [hPtr, mJ, jEsPtr, jTailsPtr, mEmbPtr, rawVsPtr]
  have hDynH2 : DynGraphAt mem2 hPtr vCap eCap H' := hDynH.of_agree fun addr ha1 ha2 =>
    hfr2_out addr (by
      have := hdisjH (addr - hPtr) (by omega)
      rw [show hPtr + (addr - hPtr) = addr by omega] at this; exact this)
  have hmEmb2 : MEmbAt mem2 mEmbPtr J.E eCap emb := by
    intro e he
    rcases hmEmb e he with ⟨heCap, hmw⟩
    refine ⟨heCap, ?_⟩
    rw [hfr2_out _ (hdisjME e he)]
    intro k hk
    rw [hfr2_out _ (hdisjW e he k hk)]
    exact hmw k hk
  have hjEAt2 : ListAt mem2 jEsPtr jEs := fun i hi => (hfr2_out _ (hdisjE i hi)).trans (hjEAt i hi)
  have hjTAt2 : ListAt mem2 jTailsPtr jTails := fun i hi =>
    (hfr2_out _ (hdisjT i (by rw [hLenT] at hi; exact hi))).trans (hjTAt i hi)
  have hrv : (collectRawVsFun H' jEs jTails emb).length = jEs.length + rawEsLen := hrawVs_len
  refine runs_seq_call_le (gtCollectRawVs_meetsContract hpGT hpOps)
    (vs := [hPtr, jEs.length, jEsPtr, jTailsPtr, mEmbPtr, rawVsPtr])
    (by
      simp only [evalArgs, Expr.eval]
      simp (disch := decide) only [Function.update_of_ne, Function.update_self, r0, r2, r4, r5, r7])
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    ⟨hPtr, jEsPtr, jTailsPtr, mEmbPtr, rawVsPtr, rfl, hw16, hhB, hjEB, hjTB, hmEB,
      by rw [hrv]; dsimp [rawVsPtr, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen] at *; omega,
      fun i hi => by
        rcases hdisjH i hi with h | h
        · left; dsimp [rawVsPtr, hEsPtr] at *; omega
        · right; rw [hrv]; dsimp [rawVsPtr, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen] at *; omega,
      fun i hi => by
        rcases hdisjE i hi with h | h
        · left; dsimp [rawVsPtr, hEsPtr] at *; omega
        · right; rw [hrv]; dsimp [rawVsPtr, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen] at *; omega,
      fun i hi => by
        rcases hdisjT i hi with h | h
        · left; dsimp [rawVsPtr, hEsPtr] at *; omega
        · right; rw [hrv]; dsimp [rawVsPtr, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen] at *; omega,
      fun e he => by
        rcases hdisjME e he with h | h
        · left; dsimp [rawVsPtr, hEsPtr] at *; omega
        · right; rw [hrv]; dsimp [rawVsPtr, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen] at *; omega,
      fun e he k hk => by
        dsimp only
        rw [hfr2_out _ (hdisjME e he)]
        rcases hdisjW e he k hk with h | h
        · left; dsimp [rawVsPtr, hEsPtr] at *; omega
        · right; rw [hrv]; dsimp [rawVsPtr, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen] at *; omega,
      hDynH2, hLenT, hjE_iff,
      fun j hj => ⟨hT j hj, lt_trans (hDynH.2.1 _ (hemb.1 (hJ _ ((hjE_iff _).mp (List.getElem_mem hj))).1)) hvCap_ltw⟩,
      hmEmb2, hjEAt2, hjTAt2,
      fun e he x hx => ⟨(mgraph_mem_walkVertices_src_dst (hemb.2 e he) x hx).1,
        lt_trans (hDynH.2.2.1 x.1 (mgraph_mem_walkVertices_src_dst (hemb.2 e he) x hx).1) heCap_ltw⟩,
      fun v hv => lt_trans (hDynH.2.1 v hv) hvCap_ltw,
      fun e he => by
        dsimp only
        have hmEq : mem2 (mEmbPtr + e) = st.mem (mEmbPtr + e) := hfr2_out _ (hdisjME e he)
        simpa only [hmEq] using hwLens e he⟩
    ?_
  intro ret3 mem3 pos3 ⟨_, _, _, _, _, hargs3, hret3, hrawVsAt3, hfr3⟩
  simp only [List.cons.injEq, and_true] at hargs3
  rcases hargs3 with ⟨rfl, _, rfl, rfl, rfl, rfl⟩
  subst hret3
  have hfr3_out : ∀ addr, addr < scratchPtr ∨ scratchPtr + sLen ≤ addr → mem3 addr = st.mem addr := by
    intro addr ha
    refine (hfr3 addr ?_).trans (hfr2_out addr ha)
    rcases ha with h | h
    · left; dsimp [rawVsPtr, hEsPtr] at *; omega
    · right; rw [hrv]; dsimp [rawVsPtr, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen] at *; omega
  have hhEsAt3 : ListAt mem3 hEsPtr hEs := fun i hi => by
    rw [hfr3 _ (Or.inl (by dsimp [rawVsPtr]; omega))]
    exact hhEsAt2 i hi
  -- 8. assign 17 := uRawPtr, 9. assign 18 := sortS2
  let uRawPtr := rawVsPtr + rawVsLen
  let sortS2 := uRawPtr + rawVsLen
  have huRawP_ltw : uRawPtr < 2 ^ w := by
    dsimp [uRawPtr, rawVsPtr, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen] at *; rw [hrawVs_len] at *; omega
  have hsort2_ltw : sortS2 < 2 ^ w := by
    dsimp [sortS2, uRawPtr, rawVsPtr, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen] at *; rw [hrawVs_len] at *; omega
  refine runs_seq_assign_le (v := uRawPtr)
    (by
      simp only [Expr.eval, BinOp.eval]
      simp (disch := decide) only [Function.update_of_ne, Function.update_self]
      exact ite_eq_left_iff.mpr fun hbad => False.elim (hbad huRawP_ltw)) ?_
  refine runs_seq_assign_le (v := sortS2)
    (by
      simp only [Expr.eval, BinOp.eval]
      simp (disch := decide) only [Function.update_of_ne, Function.update_self]
      exact ite_eq_left_iff.mpr fun hbad => False.elim (hbad hsort2_ltw)) ?_
  -- 10. call 19 gtSortDedup [rawVsPtr, rawVsLen, uRawPtr, sortS2]
  have hrawVs_w : ∀ x ∈ rawVs, x < 2 ^ w := fun x hx => by
    have hV : x ∈ usedHVerts H' J emb :=
      (collectRawVsFun_mem (H' := H') (emb := emb) hLenT hjE_iff (fun j hj => by
        have := hT j hj; rwa [List.getD_eq_getElem _ _ (by omega)] at this) x).mp (Or.inl hx)
    exact lt_trans (hDynH.2.1 x (mgraph_usedHVerts_sub_HV hDynH.1 hJ hemb hV)) hvCap_ltw
  refine runs_seq_call_le (gtSortDedup_meetsContract hpGT hpSort)
    (vs := [rawVsPtr, rawVsLen, uRawPtr, sortS2])
    (by
      simp only [evalArgs, Expr.eval]
      simp (disch := decide) only [Function.update_of_ne, Function.update_self]
      rfl)
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl <;> assumption)
    ⟨rawVsPtr, uRawPtr, sortS2, rfl, hw16,
      by dsimp [rawVsPtr, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen, rawVs] at *; rw [hrv] at *; omega,
      by dsimp [uRawPtr, rawVsPtr, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen, rawVs] at *; rw [hrv, hrawVs_len] at *; omega,
      by dsimp [sortS2, uRawPtr, rawVsPtr, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen, rawVs] at *; rw [hrv, hrawVs_len] at *; omega,
      Or.inl (by dsimp [sortS2, uRawPtr]; omega),
      Or.inl (by dsimp [uRawPtr]; omega),
      hrawVsAt3, hrawVs_w, fun x => List.mem_toFinset.symm⟩
    ?_
  intro ret4 mem4 pos4 ⟨_, _, _, hargs4, hret4, huRawAt4, hfr4⟩
  simp only [List.cons.injEq, and_true] at hargs4
  rcases hargs4 with ⟨rfl, _, rfl, rfl⟩
  subst hret4
  have huRaw_ltw : uRaw.length < 2 ^ w := by omega
  have huRaw_le' : (vertsOf rawVs.toFinset).length ≤ jEs.length + rawEsLen := by
    rw [← hrawVs_len]; exact huRaw_le
  have hfr4_out : ∀ addr, addr < scratchPtr ∨ scratchPtr + sLen ≤ addr → mem4 addr = st.mem addr := by
    intro addr ha
    exact (hfr4 addr
      (by rcases ha with h | h
          · left; dsimp [rawVsPtr, hEsPtr] at *; omega
          · right; dsimp [rawVsPtr, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen, rawVs] at *; rw [hrv] at *; omega)
      (by rcases ha with h | h
          · left; dsimp [sortS2, uRawPtr, rawVsPtr, hEsPtr] at *; omega
          · right; dsimp [sortS2, uRawPtr, rawVsPtr, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen, rawVs] at *; rw [hrv, hrawVs_len] at *; omega)
      (by have h1 := huRaw_le'
          rcases ha with h | h
          · left; dsimp [uRawPtr, rawVsPtr, hEsPtr] at *; omega
          · right; dsimp [uRawPtr, rawVsPtr, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen, rawVs] at *; rw [hrv, hrawVs_len] at *; omega)).trans (hfr3_out addr ha)
  have hhEsAt4 : ListAt mem4 hEsPtr hEs := fun i hi => by
    rw [hfr4 _ (Or.inl (by dsimp [rawVsPtr]; omega))
      (Or.inl (by dsimp [sortS2, uRawPtr, rawVsPtr]; omega))
      (Or.inl (by dsimp [uRawPtr, rawVsPtr]; omega))]
    exact hhEsAt3 i hi
  -- 11. assign 20 := exVsPtr (= uRawPtr + uRaw.length)
  let exVsPtr := uRawPtr + uRaw.length
  have hexP_ltw : exVsPtr < 2 ^ w := by
    dsimp [exVsPtr, uRawPtr, rawVsPtr, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen] at *; omega
  refine runs_seq_assign_le (v := exVsPtr)
    (by
      simp only [Expr.eval, BinOp.eval]
      simp (disch := decide) only [Function.update_of_ne, Function.update_self]
      exact ite_eq_left_iff.mpr fun hbad => False.elim (hbad hexP_ltw)) ?_
  -- 12. terminal call 21 gtSortedDiff [uRawPtr, uRaw.length, jVsPtr, jVs.length, exVsPtr]
  have hjAt4 : ListAt mem4 jVsPtr jVs := fun i hi => (hfr4_out _ (hdisjV i hi)).trans (hjAt i hi)
  have hjVs_w : ∀ x ∈ jVs, x < 2 ^ w := fun x hx => by
    rw [hjV, mem_vertsOf] at hx
    exact lt_trans (hDynH.2.1 x (hemb.1 hx)) hvCap_ltw
  have huRaw_w : ∀ x ∈ uRaw, x < 2 ^ w := fun x hx => by
    rw [mem_vertsOf, List.mem_toFinset] at hx
    exact hrawVs_w x hx
  refine runs_call_le (gtSortedDiff_meetsContract (U := uRawSet) (J := J.V) hpGT)
    (vs := [uRawPtr, uRaw.length, jVsPtr, jVs.length, exVsPtr])
    (by
      simp only [evalArgs, Expr.eval]
      simp (disch := decide) only [Function.update_of_ne, Function.update_self, r3, r1]
      rfl)
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption)
    ⟨uRawPtr, jVsPtr, exVsPtr, rfl, hw16,
      by dsimp [uRawPtr, rawVsPtr, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen] at *; omega,
      hjVB,
      by dsimp [exVsPtr, uRawPtr, rawVsPtr, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen] at *; omega,
      fun i hi => by left; dsimp [exVsPtr]; omega,
      fun i hi => by
        have := hdisjV i hi; rcases this with h | h <;> [left; right] <;> dsimp [exVsPtr, uRawPtr, rawVsPtr, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen] at * <;> omega,
      vertsOf_pairwise_lt uRawSet, hjV ▸ vertsOf_pairwise_lt J.V,
      fun x => mem_vertsOf, fun x => by simp [hjV, mem_vertsOf],
      huRawAt4, hjAt4, huRaw_w, hjVs_w⟩
    ?_
  intro ret5 mem5 pos5 ⟨_, _, _, hargs5, hret5, hexAt5, hfr5⟩
  simp only [List.cons.injEq, and_true] at hargs5
  rcases hargs5 with ⟨rfl, _, rfl, _, rfl⟩
  have hhex : ret5 = exVs.length := by rw [hret5, hex_eq]
  have hex_ptr_eq : exVsPtr = scratchPtr + rawEsLen + hEs.length + (jEs.length + rawEsLen) +
      (vertsOf (collectRawVsFun H' jEs jTails emb).toFinset).length := by
    dsimp [exVsPtr, uRawPtr, rawVsPtr, hEsPtr, uRaw]
    rw [hrawVs_len]
  have hexAt5' : ListAt mem5 (scratchPtr + rawEsLen + hEs.length + (jEs.length + rawEsLen) +
      (vertsOf (collectRawVsFun H' jEs jTails emb).toFinset).length) exVs := by
    rw [← hex_ptr_eq]
    have : vertsOf (uRawSet \ J.V) = exVs := by simp [exVs, hex_eq]
    rwa [← this]
  have hhEsAt5 : ListAt mem5 hEsPtr hEs := fun i hi => by
    rw [hfr5 _ (Or.inl (by dsimp [exVsPtr, uRawPtr, rawVsPtr]; omega))]
    exact hhEsAt4 i hi
  have hex_le' : exVs.length ≤ jEs.length + rawEsLen := le_trans hex_le huRaw_le'
  have hfr5_out : ∀ addr, addr < scratchPtr ∨ scratchPtr + sLen ≤ addr → mem5 addr = st.mem addr :=
    fun addr ha => (hfr5 addr (by
      have hex_le'' : (vertsOf (uRawSet \ J.V)).length ≤ jEs.length + rawEsLen := by
        rw [hex_eq]; exact hex_le'
      rcases ha with h | h <;> [left; right] <;> dsimp [exVsPtr, uRawPtr, rawVsPtr, hEsPtr, sLen, gtFwdCoreScratchLen, rawEsLen] at * <;> omega)).trans (hfr4_out addr ha)
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hhEsAt5, hexAt5',
      by omega,
      by
        have h1 := hex_le'
        have h2 := huRaw_le'
        have h3 := hmH_le
        dsimp only [exVs, hEs] at h1 h3
        dsimp [hEsPtr, gtFwdCoreScratchLen, rawEsLen] at *
        omega,
      hfr5_out⟩
    · simp (disch := decide) only [Function.update_of_ne, r0]
    · simp (disch := decide) only [Function.update_of_ne, r1]
    · simp (disch := decide) only [Function.update_of_ne, r2]
    · simp (disch := decide) only [Function.update_of_ne, r3]
    · simp (disch := decide) only [Function.update_of_ne, r4]
    · simp (disch := decide) only [Function.update_of_ne, r5]
    · simp (disch := decide) only [Function.update_of_ne, r6]
    · simp (disch := decide) only [Function.update_of_ne, r7]
    · simp (disch := decide) only [Function.update_of_ne, r8]
    · simp (disch := decide) only [Function.update_of_ne, r9]
    · simp (disch := decide) only [Function.update_of_ne, Function.update_self]; rfl
    · simp (disch := decide) only [Function.update_of_ne, Function.update_self]
    · simp (disch := decide) only [Function.update_of_ne, Function.update_self]; exact hex_ptr_eq
    · simp (disch := decide) only [Function.update_self]; exact hhex
  · dsimp only [gtCollectRawEsContract, gtSortDedupContract, gtCollectRawVsContract,
      gtSortedDiffContract, argsSize, Expr.size]
    have huR' : uRaw.length ≤ rawEsLen + jEs.length := by
      have := huRaw_le'; omega
    rw [hrv]
    dsimp only [rawEsLen] at *
    rw [Nat.add_comm jEs.length (collectRawEsFun jEs emb).length]
    have hmul1 : 250 * (collectRawEsFun jEs emb).length * (Nat.log 2 ((collectRawEsFun jEs emb).length + 1) + 1) +
        250 * (collectRawEsFun jEs emb).length * (Nat.log 2 ((collectRawEsFun jEs emb).length + 1) + 1) =
        500 * (collectRawEsFun jEs emb).length * (Nat.log 2 ((collectRawEsFun jEs emb).length + 1) + 1) := by ring
    omega

end

end MinCostFlow.DynSpanner.Program
