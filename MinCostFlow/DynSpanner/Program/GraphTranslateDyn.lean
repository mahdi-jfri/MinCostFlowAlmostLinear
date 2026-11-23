module

public import MinCostFlow.DynSpanner.Program.GraphTranslateHelpers

/-!
# Dynamic Forward Graph Translation (`GraphTranslateDyn`)

Completes verification of `gtForwardCore_meetsContract` (`gtIdxForwardCore = 0`) and
`gtForwardDyn_meetsContract` (`gtIdxForwardDyn = 1`) for translating `DynGraphAt H'` and
`DynGraphAt J` with `MEmbAt emb` into canonical `canonSparsifyInput` memory.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner

@[expose] public section

/-- Contract for `gtForwardDynStmt`. -/
def gtForwardDynContract (w vCapH eCapH vCapJ eCapJ : ℕ) (H' J : MGraph)
    (emb : MinCostFlow.Embedding) : Contract where
  pre args mem := ∃ hPtr jPtr mEmbPtr scratchPtr outPtr,
    let rawEsLen := (collectRawEsFun (vertsOf J.E) emb).length
    let sLen := gtFwdDynScratchLen J.n J.m rawEsLen
    let outLen := (canonSparsifyInput H' J emb).length
    args = [hPtr, jPtr, mEmbPtr, scratchPtr, outPtr] ∧
    16 ≤ 2 ^ w ∧
    hPtr + dynGraphSize vCapH eCapH < 2 ^ w ∧
    jPtr + dynGraphSize vCapJ eCapJ < 2 ^ w ∧
    mEmbPtr + eCapH < 2 ^ w ∧
    scratchPtr + sLen < 2 ^ w ∧
    outPtr + outLen < 2 ^ w ∧
    let dis := fun addr =>
      (addr < scratchPtr ∨ scratchPtr + sLen ≤ addr) ∧
      (addr < outPtr ∨ outPtr + outLen ≤ addr)
    (scratchPtr + sLen ≤ outPtr ∨ outPtr + outLen ≤ scratchPtr) ∧
    (∀ i < dynGraphSize vCapH eCapH, dis (hPtr + i)) ∧
    (∀ i < dynGraphSize vCapJ eCapJ, dis (jPtr + i)) ∧
    (∀ e ∈ J.E, dis (mEmbPtr + e)) ∧
    (∀ e ∈ J.E, ∀ k < (mWalkEncode (emb e)).length, dis (mem (mEmbPtr + e) + k)) ∧
    DynGraphAt mem hPtr vCapH eCapH H' ∧
    DynGraphAt mem jPtr vCapJ eCapJ J ∧
    emb.IsEmbedding J H' ∧
    MEmbAt mem mEmbPtr J.E eCapH emb ∧
    (∀ e ∈ J.E, (emb e).length < 2 ^ w ∧ mem (mEmbPtr + e) + (mWalkEncode (emb e)).length < 2 ^ w)
  post args mem ret mem' := ∃ hPtr jPtr mEmbPtr scratchPtr outPtr,
    let rawEsLen := (collectRawEsFun (vertsOf J.E) emb).length
    let sLen := gtFwdDynScratchLen J.n J.m rawEsLen
    let outLen := (canonSparsifyInput H' J emb).length
    args = [hPtr, jPtr, mEmbPtr, scratchPtr, outPtr] ∧
    ret = outLen ∧
    ListAt mem' outPtr (canonSparsifyInput H' J emb) ∧
    ∀ addr, (addr < scratchPtr ∨ scratchPtr + sLen ≤ addr) →
      (addr < outPtr ∨ outPtr + outLen ≤ addr) → mem' addr = mem addr
  cost _ _ :=
    let rawEsLen := (collectRawEsFun (vertsOf J.E) emb).length
    let lArg := J.n + 2 * rawEsLen + J.m + 2
    1430 * (J.n + J.m + rawEsLen) * (Nat.log 2 lArg + 1) +
      1250 * (J.n + J.m + rawEsLen) + 1500

private lemma gt_pt_ne3 {outPtr x : ℕ} (h : x < outPtr ∨ outPtr + 3 ≤ x) :
    x ≠ outPtr ∧ x ≠ outPtr + 1 ∧ x ≠ outPtr + 2 := by
  rcases h with h | h <;> exact ⟨by omega, by omega, by omega⟩

private lemma gtForwardCore_emitPhase {w vCap eCap : ℕ} {p : Program}
    {bSort bOps bGT bEmit : ℕ}
    {H' J : MGraph} {emb : MinCostFlow.Embedding} {jVs jEs jTails jHeads : List ℕ}
    {hPtr jVsPtr jEsPtr jTailsPtr jHeadsPtr mEmbPtr scratchPtr outPtr : ℕ}
    {mem : ℕ → ℕ} {st1 : State} (ω : ℕ → Bool)
    (hpEmit : p.HasAt bEmit (gtEmitProcs bSort bOps bGT))
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hpGT : p.HasAt bGT (gtProcs bSort bOps))
    (hpSort : p.HasAt bSort (sortProcs bSort))
    (hw16 : 16 ≤ 2 ^ w) (hhB : hPtr + dynGraphSize vCap eCap < 2 ^ w)
    (hjVB : jVsPtr + jVs.length < 2 ^ w) (hjEB : jEsPtr + jEs.length < 2 ^ w)
    (hjTB : jTailsPtr + jEs.length < 2 ^ w) (hjHB : jHeadsPtr + jEs.length < 2 ^ w)
    (hmEB : mEmbPtr + eCap < 2 ^ w)
    (hscB : scratchPtr + gtFwdCoreScratchLen jEs.length (collectRawEsFun jEs emb).length < 2 ^ w)
    (houtB : outPtr + (canonSparsifyInput H' J emb).length < 2 ^ w)
    (hscOutDisj : scratchPtr + gtFwdCoreScratchLen jEs.length (collectRawEsFun jEs emb).length ≤ outPtr ∨
      outPtr + (canonSparsifyInput H' J emb).length ≤ scratchPtr)
    (hdisjH : ∀ i < dynGraphSize vCap eCap,
      (hPtr + i < scratchPtr ∨ scratchPtr + gtFwdCoreScratchLen jEs.length (collectRawEsFun jEs emb).length ≤ hPtr + i) ∧
      (hPtr + i < outPtr ∨ outPtr + (canonSparsifyInput H' J emb).length ≤ hPtr + i))
    (hdisjV : ∀ i < jVs.length,
      (jVsPtr + i < scratchPtr ∨ scratchPtr + gtFwdCoreScratchLen jEs.length (collectRawEsFun jEs emb).length ≤ jVsPtr + i) ∧
      (jVsPtr + i < outPtr ∨ outPtr + (canonSparsifyInput H' J emb).length ≤ jVsPtr + i))
    (hdisjE : ∀ i < jEs.length,
      (jEsPtr + i < scratchPtr ∨ scratchPtr + gtFwdCoreScratchLen jEs.length (collectRawEsFun jEs emb).length ≤ jEsPtr + i) ∧
      (jEsPtr + i < outPtr ∨ outPtr + (canonSparsifyInput H' J emb).length ≤ jEsPtr + i))
    (hdisjT : ∀ i < jEs.length,
      (jTailsPtr + i < scratchPtr ∨ scratchPtr + gtFwdCoreScratchLen jEs.length (collectRawEsFun jEs emb).length ≤ jTailsPtr + i) ∧
      (jTailsPtr + i < outPtr ∨ outPtr + (canonSparsifyInput H' J emb).length ≤ jTailsPtr + i))
    (hdisjHd : ∀ i < jEs.length,
      (jHeadsPtr + i < scratchPtr ∨ scratchPtr + gtFwdCoreScratchLen jEs.length (collectRawEsFun jEs emb).length ≤ jHeadsPtr + i) ∧
      (jHeadsPtr + i < outPtr ∨ outPtr + (canonSparsifyInput H' J emb).length ≤ jHeadsPtr + i))
    (hdisjME : ∀ e ∈ J.E,
      (mEmbPtr + e < scratchPtr ∨ scratchPtr + gtFwdCoreScratchLen jEs.length (collectRawEsFun jEs emb).length ≤ mEmbPtr + e) ∧
      (mEmbPtr + e < outPtr ∨ outPtr + (canonSparsifyInput H' J emb).length ≤ mEmbPtr + e))
    (hdisjW : ∀ e ∈ J.E, ∀ k < (mWalkEncode (emb e)).length,
      (mem (mEmbPtr + e) + k < scratchPtr ∨ scratchPtr + gtFwdCoreScratchLen jEs.length (collectRawEsFun jEs emb).length ≤ mem (mEmbPtr + e) + k) ∧
      (mem (mEmbPtr + e) + k < outPtr ∨ outPtr + (canonSparsifyInput H' J emb).length ≤ mem (mEmbPtr + e) + k))
    (hDynH : DynGraphAt mem hPtr vCap eCap H') (hJ : J.IsValid) (hemb : emb.IsEmbedding J H')
    (hjV : jVs = vertsOf J.V) (hjE : jEs = vertsOf J.E)
    (hLenT : jTails.length = jEs.length) (hLenHd : jHeads.length = jEs.length)
    (hTHd : ∀ i (hi : i < jEs.length),
      jTails.getD i 0 = J.tail (jEs[i]'hi) ∧ jHeads.getD i 0 = J.head (jEs[i]'hi))
    (hmEmb : MEmbAt mem mEmbPtr J.E eCap emb)
    (hjAt : ListAt mem jVsPtr jVs) (hjEAt : ListAt mem jEsPtr jEs)
    (hjTAt : ListAt mem jTailsPtr jTails) (hjHAt : ListAt mem jHeadsPtr jHeads)
    (hwLens : ∀ e ∈ J.E, (emb e).length < 2 ^ w ∧ mem (mEmbPtr + e) + (mWalkEncode (emb e)).length < 2 ^ w)
    (hScr : gtScratchPost H' J emb jEs jTails
      hPtr jVsPtr jEsPtr jTailsPtr jHeadsPtr mEmbPtr scratchPtr outPtr jVs.length mem st1) :
    ∃ o st' c,
      Runs w p ω (gtForwardCoreEmitStmt bEmit) st1 o st' c ∧
      (o = .returned (canonSparsifyInput H' J emb).length ∧
        ListAt st'.mem outPtr (canonSparsifyInput H' J emb) ∧
        ∀ addr, (addr < scratchPtr ∨ scratchPtr + gtFwdCoreScratchLen jEs.length (collectRawEsFun jEs emb).length ≤ addr) →
          (addr < outPtr ∨ outPtr + (canonSparsifyInput H' J emb).length ≤ addr) → st'.mem addr = mem addr) ∧
      c ≤
        (gtEmitCitedHContract w vCap eCap H' J emb jVs
          (vertsOf (usedHVerts H' J emb \ J.V)) (vertsOf (usedHEdges J emb))).cost [] mem +
        (gtEmitCitedJContract w J jVs jEs jTails jHeads).cost [] mem +
        (gtEmitEmbToCitedContract w vCap eCap H' J emb jVs
          (vertsOf (usedHVerts H' J emb \ J.V)) jEs jTails (vertsOf (usedHEdges J emb))).cost [] mem + 120 := by
  let rawEsLen := (collectRawEsFun jEs emb).length
  let sLen := gtFwdCoreScratchLen jEs.length rawEsLen
  let outLen := (canonSparsifyInput H' J emb).length
  have hscB' : scratchPtr + sLen < 2 ^ w := hscB
  have houtB' : outPtr + outLen < 2 ^ w := houtB
  have hscOut' : scratchPtr + sLen ≤ outPtr ∨ outPtr + outLen ≤ scratchPtr := hscOutDisj
  let hEs := vertsOf (usedHEdges J emb)
  let exVs := vertsOf (usedHVerts H' J emb \ J.V)
  let cH := toCitedH H' J emb
  let cJ := toCitedJ J
  let cWalks := (List.range cJ.m).map (embToCited H' J emb)
  let dataLen := (cWalks.flatMap Walk.encode).length
  have hjE_iff : ∀ e, e ∈ jEs ↔ e ∈ J.E := by intro e; simp [hjE, mem_vertsOf]
  have hcJm : cJ.m = jEs.length := by simp [cJ, toCitedJ, Cited.Graph.m, hjE]
  have hcHm : cH.m = hEs.length := by simp [cH, toCitedH, Cited.Graph.m, hEdges, hEs]
  have hcH_enc : cH.encode.length = 2 + 2 * hEs.length := by rw [graph_encode_length, hcHm]
  have hcJ_enc : cJ.encode.length = 2 + 2 * jEs.length := by rw [graph_encode_length, hcJm]
  have hdata_eq : dataLen = (((List.range jEs.length).map (embToCited H' J emb)).flatMap Walk.encode).length := by
    simp [dataLen, cWalks, hcJm]
  have houtLen_eq : outLen = 7 + 2 * hEs.length + 3 * jEs.length + dataLen := by
    dsimp only [outLen, canonSparsifyInput]
    simp only [List.length_append, List.length_cons, List.length_nil, canonWalkOffsets_length]
    rw [hcH_enc, hcJ_enc, hcJm]
    simp [cWalks, dataLen, hcJm]
    omega
  rcases hScr with ⟨r0, r1, r2, r3, r4, r5, r6, r7, _, r9, r12, r14, r20, r21, hhEsAt, hexAt, hHE_le, hex_end, hfr'⟩
  dsimp only [gtForwardCoreEmitStmt]
  let hEsPtr := scratchPtr + rawEsLen
  let exVsPtr := hEsPtr + hEs.length + (jEs.length + rawEsLen) +
    (vertsOf (collectRawVsFun H' jEs jTails emb).toFinset).length
  let pJ := 5 + 2 * hEs.length
  let pEmb := pJ + (2 + 2 * jEs.length)
  let pWalks := pEmb + jEs.length
  have hhE_bound : hEsPtr + hEs.length ≤ exVsPtr := by
    dsimp only [exVsPtr, hEsPtr, hEs, rawEsLen]; omega
  have hex_bound : exVsPtr + exVs.length ≤ scratchPtr + sLen := by
    dsimp only [exVsPtr, hEsPtr, exVs, hEs, rawEsLen, sLen]; exact hex_end
  have hsc_hE : scratchPtr ≤ hEsPtr := by dsimp only [hEsPtr]; omega
  have hsc_ex : scratchPtr ≤ exVsPtr := by dsimp only [exVsPtr, hEsPtr]; omega
  have hhE_ub : hEsPtr + hEs.length ≤ scratchPtr + sLen :=
    le_trans hhE_bound (le_trans (Nat.le_add_right _ _) hex_bound)
  have hpJ_ge : 5 ≤ pJ := by dsimp only [pJ]; omega
  have hpEmb_ge : pJ + 2 ≤ pEmb := by dsimp only [pEmb]; omega
  have hpWalks_ge : pEmb ≤ pWalks := by dsimp only [pWalks]; omega
  have h_3_le_pJ : 3 ≤ pJ := by dsimp only [pJ]; omega
  have h_pJ_le_pEmb : pJ ≤ pEmb := by dsimp only [pEmb]; omega
  have h_pEmb_le_pW : pEmb ≤ pWalks := by dsimp only [pWalks]; omega
  have h_3_le_pEmb : 3 ≤ pEmb := le_trans h_3_le_pJ h_pJ_le_pEmb
  have h_3_le_pW : 3 ≤ pWalks := le_trans h_3_le_pEmb h_pEmb_le_pW
  have h_3_cH_le_pJ : 3 + (2 + 2 * hEs.length) ≤ pJ := by dsimp only [pJ]; omega
  have h_3_cH_le_pEmb : 3 + (2 + 2 * hEs.length) ≤ pEmb := le_trans h_3_cH_le_pJ h_pJ_le_pEmb
  have h_3_cH_le_pW : 3 + (2 + 2 * hEs.length) ≤ pWalks := le_trans h_3_cH_le_pEmb h_pEmb_le_pW
  have h_pJ_cJ_le_pEmb : pJ + (2 + 2 * jEs.length) ≤ pEmb := by dsimp only [pEmb]; omega
  have h_pJ_cJ_le_pW : pJ + (2 + 2 * jEs.length) ≤ pWalks := le_trans h_pJ_cJ_le_pEmb h_pEmb_le_pW
  have h_data_eq_walk : pWalks + dataLen = outLen := by
    dsimp only [pWalks, pEmb, pJ]; omega
  have h_pW_data_le_outLen : pWalks + dataLen ≤ outLen := le_of_eq h_data_eq_walk
  have h_pW_le_outLen : pWalks ≤ outLen := le_trans (Nat.le_add_right _ _) h_pW_data_le_outLen
  have h_pEmb_le_outLen : pEmb ≤ outLen := le_trans h_pEmb_le_pW h_pW_le_outLen
  have h_pJ_le_outLen : pJ ≤ outLen := le_trans h_pJ_le_pEmb h_pEmb_le_outLen
  have h_3_le_outLen : 3 ≤ outLen := le_trans h_3_le_pJ h_pJ_le_outLen
  have h_pJ_def_3 : outPtr + 3 + (2 + 2 * hEs.length) = outPtr + pJ := by
    dsimp only [pJ]; omega
  have h_pEmb_def : outPtr + pJ + (2 + 2 * jEs.length) = outPtr + pEmb := by
    dsimp only [pEmb]; omega
  have h_pW_def : outPtr + pEmb + jEs.length = outPtr + pWalks := by
    dsimp only [pWalks]; omega
  have hlt_hP : hPtr < 2 ^ w := by omega
  have hlt_nJ : jVs.length < 2 ^ w := by omega
  have hlt_mJ : jEs.length < 2 ^ w := by omega
  have hlt_jVP : jVsPtr < 2 ^ w := by omega
  have hlt_jEP : jEsPtr < 2 ^ w := by omega
  have hlt_jTP : jTailsPtr < 2 ^ w := by omega
  have hlt_jHP : jHeadsPtr < 2 ^ w := by omega
  have hlt_mEP : mEmbPtr < 2 ^ w := by omega
  have hlt_outP : outPtr < 2 ^ w := by omega
  have hlt_hEP : hEsPtr < 2 ^ w := by dsimp [hEsPtr, sLen, gtFwdCoreScratchLen] at *; omega
  have hlt_mH : hEs.length < 2 ^ w := by omega
  have hlt_exP : exVsPtr < 2 ^ w := by omega
  have hlt_nEx : exVs.length < 2 ^ w := by omega
  have h_exB_ltw : exVsPtr + exVs.length < 2 ^ w := lt_of_le_of_lt hex_bound hscB'
  have h_hEB_ltw : hEsPtr + hEs.length < 2 ^ w := lt_of_le_of_lt hhE_ub hscB'
  have h2mH_ltw : 2 * hEs.length < 2 ^ w := by omega
  have h2mJ_ltw : 2 * jEs.length < 2 ^ w := by omega
  have h2p2mJ_ltw : 2 + 2 * jEs.length < 2 ^ w := by omega
  have hpJ_ltw : pJ < 2 ^ w := by omega
  have hpEmb_ltw : pEmb < 2 ^ w := by omega
  have hpWalks_ltw : pWalks < 2 ^ w := by omega
  have hdata_ltw : dataLen < 2 ^ w := by omega
  have hres_ltw : outLen < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  have h3_lt : (3 : ℕ) < 2 ^ w := by omega
  have h5_lt : (5 : ℕ) < 2 ^ w := by omega
  have hout1_ltw : outPtr + 1 < 2 ^ w := by omega
  have hout2_ltw : outPtr + 2 < 2 ^ w := by omega
  have hout3_ltw : outPtr + 3 < 2 ^ w := by omega
  have houtJ_ltw : outPtr + pJ < 2 ^ w := by omega
  have houtEmb_ltw : outPtr + pEmb < 2 ^ w := by omega
  have houtW_ltw : outPtr + pWalks < 2 ^ w := by omega
  have houtW_data_ltw : outPtr + pWalks + dataLen < 2 ^ w := by
    rw [Nat.add_assoc, h_data_eq_walk]; exact houtB'
  have h_sc_disj_pt : ∀ {p len : ℕ}, scratchPtr ≤ p → p + len ≤ scratchPtr + sLen →
      ∀ i < len, p + i < outPtr ∨ outPtr + outLen ≤ p + i := fun hsp hpl i hi => by
    rcases hscOut' with h | h
    · exact Or.inl (lt_of_lt_of_le (lt_of_lt_of_le (Nat.add_lt_add_left hi _) hpl) h)
    · exact Or.inr (le_trans h (le_trans hsp (Nat.le_add_right _ _)))
  have h_out_ivl : ∀ {lo₁ hi₁ lo₂ hi₂ addr : ℕ}, lo₁ ≤ lo₂ → hi₂ ≤ hi₁ →
      (addr < outPtr + lo₁ ∨ outPtr + hi₁ ≤ addr) → (addr < outPtr + lo₂ ∨ outPtr + hi₂ ≤ addr) :=
    fun hlo hhi h => h.elim
      (fun h' => Or.inl (lt_of_lt_of_le h' (Nat.add_le_add_left hlo _)))
      (fun h' => Or.inr (le_trans (Nat.add_le_add_left hhi _) h'))
  have h_out_0 : ∀ {hi₁ hi₂ addr : ℕ}, hi₂ ≤ hi₁ →
      (addr < outPtr ∨ outPtr + hi₁ ≤ addr) → (addr < outPtr ∨ outPtr + hi₂ ≤ addr) :=
    fun hhi h => h_out_ivl (Nat.zero_le 0) hhi h
  have h_out_emb_pair : ∀ {addr : ℕ}, (addr < outPtr ∨ outPtr + outLen ≤ addr) →
      (addr < outPtr + pEmb ∨ outPtr + pEmb + jEs.length ≤ addr) ∧
        (addr < outPtr + pWalks ∨
          outPtr + pWalks + (((List.range jEs.length).map (embToCited H' J emb)).flatMap Walk.encode).length ≤ addr) :=
    fun h =>
      ⟨by rw [h_pW_def]; exact h_out_ivl (Nat.zero_le pEmb) h_pW_le_outLen h,
       by rw [← hdata_eq, Nat.add_assoc]; exact h_out_ivl (Nat.zero_le pWalks) h_pW_data_le_outLen h⟩
  -- 1. assign 22 := pJ, assign 23 := pEmb, assign 24 := pWalks
  have r14' : st1.regs 14 = hEs.length := r14
  have h5_2mH_ltw : 5 + 2 * hEs.length < 2 ^ w := hpJ_ltw
  have h2_2mJ_ltw : 2 + 2 * jEs.length < 2 ^ w := h2p2mJ_ltw
  have hpJ_add_ltw : pJ + (2 + 2 * jEs.length) < 2 ^ w := hpEmb_ltw
  have hpEmb_add_ltw : pEmb + jEs.length < 2 ^ w := hpWalks_ltw
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := pJ)
    (by simp only [Expr.eval, BinOp.eval, r14', h5_lt, h2_lt, h2mH_ltw, h5_2mH_ltw, ↓reduceIte]; rfl) ?_
  refine runs_seq_assign_le (v := pEmb)
    (by simp only [Expr.eval, BinOp.eval]
        simp (disch := decide) only [Function.update_of_ne, Function.update_self, r2]
        simp only [h2_lt, h2mJ_ltw, h2_2mJ_ltw, hpJ_add_ltw, ↓reduceIte]; rfl) ?_
  refine runs_seq_assign_le (v := pWalks)
    (by simp only [Expr.eval, BinOp.eval]
        simp (disch := decide) only [Function.update_of_ne, Function.update_self, r2]
        simp only [hpEmb_add_ltw, ↓reduceIte]; rfl) ?_
  -- 2. stores at outPtr, outPtr+1, outPtr+2
  refine runs_seq_store_le (x := outPtr) (v := 3)
    (by simp only [Expr.eval]; simp (disch := decide) only [Function.update_of_ne, r9])
    (by simp [Expr.eval, h3_lt]) ?_
  refine runs_seq_store_le (x := outPtr + 1) (v := pJ)
    (by simp only [Expr.eval, BinOp.eval]
        simp (disch := decide) only [Function.update_of_ne, r9]
        simp only [h1_lt, hout1_ltw, ↓reduceIte])
    (by simp only [Expr.eval]; simp (disch := decide) only [Function.update_of_ne, Function.update_self]) ?_
  refine runs_seq_store_le (x := outPtr + 2) (v := pEmb)
    (by simp only [Expr.eval, BinOp.eval]
        simp (disch := decide) only [Function.update_of_ne, r9]
        simp only [h2_lt, hout2_ltw, ↓reduceIte])
    (by simp only [Expr.eval]; simp (disch := decide) only [Function.update_of_ne, Function.update_self]) ?_
  set memH := Function.update (Function.update (Function.update st1.mem outPtr 3) (outPtr + 1) pJ)
    (outPtr + 2) pEmb
  have hmemH_out : ∀ addr, addr < scratchPtr ∨ scratchPtr + sLen ≤ addr →
      addr < outPtr ∨ outPtr + 3 ≤ addr → memH addr = mem addr := by
    intro addr hs ho
    have hne := gt_pt_ne3 ho
    dsimp only [memH]
    rw [Function.update_of_ne hne.2.2, Function.update_of_ne hne.2.1, Function.update_of_ne hne.1]
    exact hfr' addr hs
  have hhdrH : ListAt memH outPtr [3, pJ, pEmb] := fun i hi => by
    simp only [List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · simp [memH, Function.update_of_ne]
    · simp [memH, Function.update_of_ne, Function.update_self]
    · simp [memH, Function.update_self]
  have hvCap_ltw : vCap < 2 ^ w := by
    have : vCap ≤ dynGraphSize vCap eCap := by unfold dynGraphSize; omega
    omega
  have heCap_ltw : eCap < 2 ^ w := by
    have : eCap ≤ dynGraphSize vCap eCap := by unfold dynGraphSize; omega
    omega
  have hjVs_w : ∀ x ∈ jVs, x < 2 ^ w := fun x hx => by
    rw [hjV, mem_vertsOf] at hx
    exact lt_trans (hDynH.2.1 x (hemb.1 hx)) hvCap_ltw
  have hex_w : ∀ x ∈ exVs, x < 2 ^ w := fun x hx => by
    rw [mem_vertsOf] at hx
    exact lt_trans (hDynH.2.1 x (mgraph_usedHVerts_sub_HV hDynH.1 hJ hemb (Finset.mem_sdiff.mp hx).1)) hvCap_ltw
  have hhE_w : ∀ e ∈ hEs, e < 2 ^ w := fun e he => by
    rw [mem_vertsOf] at he
    exact lt_trans (hDynH.2.2.1 e (mgraph_usedEdges_in_H hemb e he)) heCap_ltw
  have hnHB : jVs.length + exVs.length < 2 ^ w := by
    have hle : jVs.length + exVs.length ≤ H'.n := by
      simpa only [← hjV] using vertsOf_usedHVerts_card_le hDynH.1 hJ hemb
    have hHle := dynGraph_n_le_vCap hDynH
    omega
  have hDynH_H : DynGraphAt memH hPtr vCap eCap H' := hDynH.of_agree fun addr ha1 ha2 => by
    have hdj := hdisjH (addr - hPtr) (Nat.sub_lt_left_of_lt_add ha1 ha2)
    rw [Nat.add_sub_cancel' ha1] at hdj
    exact hmemH_out addr hdj.1 (h_out_ivl (Nat.zero_le 0) h_3_le_outLen hdj.2)
  have hhEs_H : ListAt memH hEsPtr hEs := fun i hi => by
    have hne := gt_pt_ne3 (h_out_0 h_3_le_outLen (h_sc_disj_pt hsc_hE hhE_ub i hi))
    dsimp only [memH]; rw [Function.update_of_ne hne.2.2, Function.update_of_ne hne.2.1, Function.update_of_ne hne.1]
    exact hhEsAt i hi
  have hex_H : ListAt memH exVsPtr exVs := fun i hi => by
    have hne := gt_pt_ne3 (h_out_0 h_3_le_outLen (h_sc_disj_pt hsc_ex hex_bound i hi))
    dsimp only [memH]; rw [Function.update_of_ne hne.2.2, Function.update_of_ne hne.2.1, Function.update_of_ne hne.1]
    exact hexAt i hi
  have hjAt_H : ListAt memH jVsPtr jVs := fun i hi =>
    (hmemH_out _ (hdisjV i hi).1 (h_out_0 h_3_le_outLen (hdisjV i hi).2)).trans (hjAt i hi)
  -- 3. call 25 gtEmitCitedH
  refine runs_seq_call_le (gtEmitCitedH_meetsContract hpEmit hpOps hpGT hpSort)
    (vs := [hPtr, jVs.length, exVsPtr, exVs.length, hEsPtr, hEs.length, jVsPtr, outPtr + 3])
    (by
      simp only [evalArgs, Expr.eval, BinOp.eval]
      simp (disch := decide) only [Function.update_of_ne, r0, r1, r20, r21, r12, r14, r3, r9]
      simp only [h3_lt, hout3_ltw, ↓reduceIte]
      rfl)
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    ⟨hPtr, exVsPtr, hEsPtr, jVsPtr, outPtr + 3, rfl, hw16, hhB, hjVB,
      h_exB_ltw, h_hEB_ltw, by rw [h_pJ_def_3]; exact houtJ_ltw, hnHB,
      fun i hi => by rw [h_pJ_def_3]; exact h_out_ivl (Nat.zero_le 3) h_pJ_le_outLen (hdisjH i hi).2,
      fun i hi => by rw [h_pJ_def_3]; exact h_out_ivl (Nat.zero_le 3) h_pJ_le_outLen (hdisjV i hi).2,
      fun i hi => by rw [h_pJ_def_3]; exact h_out_ivl (Nat.zero_le 3) h_pJ_le_outLen (h_sc_disj_pt hsc_ex hex_bound i hi),
      fun i hi => by rw [h_pJ_def_3]; exact h_out_ivl (Nat.zero_le 3) h_pJ_le_outLen (h_sc_disj_pt hsc_hE hhE_ub i hi),
      hDynH_H, hjV, rfl, rfl, hjAt_H, hex_H, hhEs_H, mgraph_usedEdges_in_H hemb,
      hjVs_w, hex_w, hhE_w, mgraph_usedEdge_ends_in_usedHVerts hemb⟩
    ?_
  intro retH mem1 pos1 ⟨_, _, _, _, oH, hargsH, hretH, hcH_At, hfrH⟩
  simp only [List.cons.injEq, and_true] at hargsH
  rcases hargsH with ⟨rfl, _, rfl, _, rfl, _, rfl, rfl⟩
  have hfrH' : ∀ addr, addr < outPtr + 3 ∨ outPtr + pJ ≤ addr → mem1 addr = memH addr :=
    fun addr h => hfrH addr (by rw [h_pJ_def_3]; exact h)
  have hmem1_out : ∀ addr, addr < scratchPtr ∨ scratchPtr + sLen ≤ addr →
      addr < outPtr ∨ outPtr + pJ ≤ addr → mem1 addr = mem addr := fun addr hs ho =>
    (hfrH' addr (h_out_ivl (Nat.zero_le 3) (le_refl pJ) ho)).trans
      (hmemH_out addr hs (h_out_0 h_3_le_pJ ho))
  have hhdr1 : ListAt mem1 outPtr [3, pJ, pEmb] := fun i hi => by
    have hi3 : i < 3 := hi
    rw [hfrH' _ (Or.inl (Nat.add_lt_add_left hi3 _))]; exact hhdrH i hi
  have hjAt1 : ListAt mem1 jVsPtr jVs := fun i hi =>
    (hmem1_out _ (hdisjV i hi).1 (h_out_ivl (Nat.zero_le 0) h_pJ_le_outLen (hdisjV i hi).2)).trans (hjAt i hi)
  have hjTAt1 : ListAt mem1 jTailsPtr jTails := fun i hi =>
    (hmem1_out _ (hdisjT i (hLenT ▸ hi)).1
      (h_out_ivl (Nat.zero_le 0) h_pJ_le_outLen (hdisjT i (hLenT ▸ hi)).2)).trans (hjTAt i hi)
  have hjHAt1 : ListAt mem1 jHeadsPtr jHeads := fun i hi =>
    (hmem1_out _ (hdisjHd i (hLenHd ▸ hi)).1
      (h_out_ivl (Nat.zero_le 0) h_pJ_le_outLen (hdisjHd i (hLenHd ▸ hi)).2)).trans (hjHAt i hi)
  -- 4. call 25 gtEmitCitedJ
  refine runs_seq_call_le (gtEmitCitedJ_meetsContract hpEmit hpSort)
    (vs := [jEs.length, jVsPtr, jVs.length, jTailsPtr, jHeadsPtr, outPtr + pJ])
    (by
      simp only [evalArgs, Expr.eval, BinOp.eval]
      simp (disch := decide) only [Function.update_of_ne, Function.update_self, r2, r3, r1, r5, r6, r9]
      simp only [houtJ_ltw, ↓reduceIte])
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    ⟨jVsPtr, jTailsPtr, jHeadsPtr, outPtr + pJ, rfl, hw16, hjVB, hjTB, hjHB,
      by rw [h_pEmb_def]; exact houtEmb_ltw,
      fun i hi => by rw [h_pEmb_def]; exact h_out_ivl (Nat.zero_le pJ) h_pEmb_le_outLen (hdisjV i hi).2,
      fun i hi => by rw [h_pEmb_def]; exact h_out_ivl (Nat.zero_le pJ) h_pEmb_le_outLen (hdisjT i hi).2,
      fun i hi => by rw [h_pEmb_def]; exact h_out_ivl (Nat.zero_le pJ) h_pEmb_le_outLen (hdisjHd i hi).2,
      hJ, hjV, hjE, hLenT, hLenHd, fun i hi => hTHd i hi,
      hjAt1, hjTAt1, hjHAt1, hjVs_w⟩
    ?_
  intro retJ mem2 pos2 ⟨_, _, _, _, hargsJ, hretJ, hcJ_At, hfrJ⟩
  simp only [List.cons.injEq, and_true] at hargsJ
  rcases hargsJ with ⟨_, rfl, _, rfl, rfl, rfl⟩
  have hfrJ' : ∀ addr, addr < outPtr + pJ ∨ outPtr + pEmb ≤ addr → mem2 addr = mem1 addr :=
    fun addr h => hfrJ addr (by rw [h_pEmb_def]; exact h)
  have hmem2_out : ∀ addr, addr < scratchPtr ∨ scratchPtr + sLen ≤ addr →
      addr < outPtr ∨ outPtr + pEmb ≤ addr → mem2 addr = mem addr := fun addr hs ho =>
    (hfrJ' addr (h_out_ivl (Nat.zero_le pJ) (le_refl _) ho)).trans
      (hmem1_out addr hs (h_out_ivl (Nat.zero_le 0) h_pJ_le_pEmb ho))
  have hhdr2 : ListAt mem2 outPtr [3, pJ, pEmb] := fun i hi => by
    have hi3 : i < 3 := hi
    rw [hfrJ' _ (Or.inl (Nat.add_lt_add_left (lt_of_lt_of_le hi3 h_3_le_pJ) _))]; exact hhdr1 i hi
  have hcH_At2 : ListAt mem2 (outPtr + 3) cH.encode := fun i hi => by
    rw [hcH_enc] at hi
    rw [hfrJ' _ (Or.inl (by
      rw [Nat.add_assoc]
      exact lt_of_lt_of_le (Nat.add_lt_add_left (Nat.add_lt_add_left hi 3) outPtr)
        (Nat.add_le_add_left h_3_cH_le_pJ outPtr)))]
    exact hcH_At i (by rw [hcH_enc]; exact hi)
  have hDynH_2 : DynGraphAt mem2 hPtr vCap eCap H' := hDynH.of_agree fun addr ha1 ha2 => by
    have hdj := hdisjH (addr - hPtr) (Nat.sub_lt_left_of_lt_add ha1 ha2)
    rw [Nat.add_sub_cancel' ha1] at hdj
    exact hmem2_out addr hdj.1 (h_out_ivl (Nat.zero_le 0) h_pEmb_le_outLen hdj.2)
  have hmEmb2 : MEmbAt mem2 mEmbPtr J.E eCap emb := fun e he => by
    rcases hmEmb e he with ⟨heCap, hmw⟩
    refine ⟨heCap, ?_⟩
    rw [hmem2_out _ (hdisjME e he).1 (h_out_ivl (Nat.zero_le 0) h_pEmb_le_outLen (hdisjME e he).2)]
    intro k hk
    rw [hmem2_out _ (hdisjW e he k hk).1 (h_out_ivl (Nat.zero_le 0) h_pEmb_le_outLen (hdisjW e he k hk).2)]
    exact hmw k hk
  have hhEs2 : ListAt mem2 hEsPtr hEs := fun i hi => by
    have ho := h_sc_disj_pt hsc_hE hhE_ub i hi
    rw [hfrJ' _ (h_out_ivl (Nat.zero_le pJ) h_pEmb_le_outLen ho)]
    rw [hfrH' _ (h_out_ivl (Nat.zero_le 3) h_pJ_le_outLen ho)]
    exact hhEs_H i hi
  have hex2 : ListAt mem2 exVsPtr exVs := fun i hi => by
    have ho := h_sc_disj_pt hsc_ex hex_bound i hi
    rw [hfrJ' _ (h_out_ivl (Nat.zero_le pJ) h_pEmb_le_outLen ho)]
    rw [hfrH' _ (h_out_ivl (Nat.zero_le 3) h_pJ_le_outLen ho)]
    exact hex_H i hi
  have hjAt2 : ListAt mem2 jVsPtr jVs := fun i hi =>
    (hmem2_out _ (hdisjV i hi).1 (h_out_ivl (Nat.zero_le 0) h_pEmb_le_outLen (hdisjV i hi).2)).trans (hjAt i hi)
  have hjEAt2 : ListAt mem2 jEsPtr jEs := fun i hi =>
    (hmem2_out _ (hdisjE i hi).1 (h_out_ivl (Nat.zero_le 0) h_pEmb_le_outLen (hdisjE i hi).2)).trans (hjEAt i hi)
  have hjTAt2 : ListAt mem2 jTailsPtr jTails := fun i hi =>
    (hmem2_out _ (hdisjT i (hLenT ▸ hi)).1
      (h_out_ivl (Nat.zero_le 0) h_pEmb_le_outLen (hdisjT i (hLenT ▸ hi)).2)).trans (hjTAt i hi)
  -- 5. call 25 gtEmitEmbToCited
  refine runs_seq_call_le (gtEmitEmbToCited_meetsContract (H' := H') (J := J) (emb := emb) hpEmit hpOps hpGT hpSort)
    (vs := [hPtr, jEs.length, jEsPtr, jTailsPtr, mEmbPtr, jVsPtr, jVs.length,
      exVsPtr, exVs.length, hEsPtr, hEs.length, outPtr + pEmb, outPtr + pWalks, pWalks])
    (by
      simp only [evalArgs, Expr.eval, BinOp.eval]
      simp (disch := decide) only [Function.update_of_ne, Function.update_self,
        r0, r2, r4, r5, r7, r3, r1, r20, r21, r12, r14, r9]
      simp only [houtEmb_ltw, houtW_ltw, ↓reduceIte]
      rfl)
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    ⟨hPtr, jEsPtr, jTailsPtr, mEmbPtr, jVsPtr, exVsPtr, hEsPtr, outPtr + pEmb, outPtr + pWalks, pWalks,
      rfl, hw16, hhB, hjEB, hjTB, hmEB, hjVB, h_exB_ltw, h_hEB_ltw,
      by rw [h_pW_def]; exact houtW_ltw,
      by rw [← hdata_eq]; exact houtW_data_ltw,
      by rw [← hdata_eq]; exact lt_of_le_of_lt (Nat.add_le_add_right (Nat.le_add_left _ _) _) houtW_data_ltw,
      hnHB, Or.inl (le_of_eq h_pW_def),
      fun i hi => h_out_emb_pair (hdisjH i hi).2,
      fun i hi => h_out_emb_pair (hdisjE i hi).2,
      fun i hi => h_out_emb_pair (hdisjT i hi).2,
      fun e he => h_out_emb_pair (hdisjME e he).2,
      fun e he k hk => by
        dsimp only
        rw [hmem2_out _ (hdisjME e he).1 (h_out_ivl (Nat.zero_le 0) h_pEmb_le_outLen (hdisjME e he).2)]
        exact h_out_emb_pair (hdisjW e he k hk).2,
      fun i hi => h_out_emb_pair (hdisjV i hi).2,
      fun i hi => h_out_emb_pair (h_sc_disj_pt hsc_ex hex_bound i hi),
      fun i hi => h_out_emb_pair (h_sc_disj_pt hsc_hE hhE_ub i hi),
      hDynH_2, hJ, hemb, hjV, rfl, hjE, rfl, hLenT, fun i hi => (hTHd i hi).1,
      hmEmb2, hjEAt2, hjTAt2, hjAt2, hex2, hhEs2, hjVs_w, hex_w, hhE_w,
      fun e he => by
        dsimp only
        have hmEq : mem2 (mEmbPtr + e) = mem (mEmbPtr + e) :=
          hmem2_out _ (hdisjME e he).1 (h_out_ivl (Nat.zero_le 0) h_pEmb_le_outLen (hdisjME e he).2)
        simpa only [hmEq] using hwLens e he⟩
    ?_
  intro retW mem3 pos3 ⟨_, _, _, _, _, _, _, _, _, _, hargsW, hretW, hptrs3, hdata3, hfrW⟩
  simp only [List.cons.injEq, and_true] at hargsW
  rcases hargsW with ⟨rfl, _, rfl, rfl, rfl, rfl, _, rfl, _, rfl, _, rfl, rfl, rfl⟩
  have hfrW' : ∀ addr, (addr < outPtr + pEmb ∨ outPtr + pWalks ≤ addr) →
      (addr < outPtr + pWalks ∨ outPtr + pWalks + dataLen ≤ addr) → mem3 addr = mem2 addr :=
    fun addr h1 h2 =>
      hfrW addr
        (by rcases h1 with h | h; exact Or.inl h; exact Or.inr (by dsimp only [pWalks] at h; rw [← Nat.add_assoc] at h; exact h))
        (by rw [← hdata_eq]; exact h2)
  have hretW_eq : retW = dataLen := by rw [hretW, hdata_eq]
  have hfull : ListAt mem3 outPtr (canonSparsifyInput H' J emb) := by
    unfold canonSparsifyInput
    have hpH_eq : 3 + (2 + 2 * hEs.length) = pJ := by dsimp only [pJ]; omega
    have hpE_eq : pJ + (2 + 2 * jEs.length) = pEmb := rfl
    have hpH' : 3 + cH.encode.length = pJ := by rw [hcH_enc]; exact hpH_eq
    have hpE' : pJ + cJ.encode.length = pEmb := by rw [hcJ_enc]
    have hpW' : pEmb + cJ.m = pWalks := by rw [hcJm]
    have hcW_eq : (List.range cJ.m).map (embToCited H' J emb) =
        (List.range jEs.length).map (embToCited H' J emb) := by rw [hcJm]
    have hhdr3 : ListAt mem3 outPtr [3, pJ, pEmb] := fun i hi => by
      have hi3 : i < 3 := hi
      rw [hfrW' (outPtr + i)
        (Or.inl (Nat.add_lt_add_left (lt_of_lt_of_le hi3 h_3_le_pEmb) _))
        (Or.inl (Nat.add_lt_add_left (lt_of_lt_of_le hi3 h_3_le_pW) _))]
      exact hhdr2 i hi
    have hcH3 : ListAt mem3 (outPtr + 3) cH.encode := fun i hi => by
      rw [hcH_enc] at hi
      rw [hfrW' (outPtr + 3 + i)
        (Or.inl (by
          rw [Nat.add_assoc]
          exact lt_of_lt_of_le (Nat.add_lt_add_left (Nat.add_lt_add_left hi 3) outPtr)
            (Nat.add_le_add_left h_3_cH_le_pEmb outPtr)))
        (Or.inl (by
          rw [Nat.add_assoc]
          exact lt_of_lt_of_le (Nat.add_lt_add_left (Nat.add_lt_add_left hi 3) outPtr)
            (Nat.add_le_add_left h_3_cH_le_pW outPtr)))]
      exact hcH_At2 i (by rw [hcH_enc]; exact hi)
    have hcJ3 : ListAt mem3 (outPtr + pJ) cJ.encode := fun i hi => by
      rw [hcJ_enc] at hi
      rw [hfrW' (outPtr + pJ + i)
        (Or.inl (by
          rw [Nat.add_assoc]
          exact lt_of_lt_of_le (Nat.add_lt_add_left (Nat.add_lt_add_left hi pJ) outPtr)
            (Nat.add_le_add_left h_pJ_cJ_le_pEmb outPtr)))
        (Or.inl (by
          rw [Nat.add_assoc]
          exact lt_of_lt_of_le (Nat.add_lt_add_left (Nat.add_lt_add_left hi pJ) outPtr)
            (Nat.add_le_add_left h_pJ_cJ_le_pW outPtr)))]
      exact hcJ_At i (by rw [hcJ_enc]; exact hi)
    change ListAt mem3 outPtr ([3, 3 + cH.encode.length, 3 + cH.encode.length + cJ.encode.length] ++
      cH.encode ++ cJ.encode ++
      canonWalkOffsets (3 + cH.encode.length + cJ.encode.length + cJ.m) cWalks ++
      List.flatMap Walk.encode cWalks)
    rw [show [3, 3 + cH.encode.length, 3 + cH.encode.length + cJ.encode.length] = [3, pJ, pEmb] by
      rw [hpH', hpE'], hpH', hpE', hpW']
    have hlen1 : ([3, pJ, pEmb] ++ cH.encode).length = pJ := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [← hpH']
    have hlen2 : ([3, pJ, pEmb] ++ cH.encode ++ cJ.encode).length = pEmb := by
      simp only [List.length_append, hlen1]; exact hpE'
    have hlen3 : ([3, pJ, pEmb] ++ cH.encode ++ cJ.encode ++ canonWalkOffsets pWalks cWalks).length = pWalks := by
      simp only [List.length_append, hlen2, canonWalkOffsets_length, cWalks, List.length_map, List.length_range]
      exact hpW'
    refine listAt_append.mpr ⟨?_, by rw [hlen3]; dsimp only [cWalks]; rw [hcW_eq]; exact hdata3⟩
    refine listAt_append.mpr ⟨?_, by rw [hlen2]; dsimp only [cWalks]; rw [hcW_eq]; exact hptrs3⟩
    refine listAt_append.mpr ⟨?_, by rw [hlen1]; exact hcJ3⟩
    refine listAt_append.mpr ⟨hhdr3, by simpa using hcH3⟩
  have hfr3 : ∀ addr, (addr < scratchPtr ∨ scratchPtr + sLen ≤ addr) →
      (addr < outPtr ∨ outPtr + outLen ≤ addr) → mem3 addr = mem addr := fun addr hs ho =>
    (hfrW' addr (h_out_ivl (Nat.zero_le pEmb) h_pW_le_outLen ho)
      (by rw [Nat.add_assoc]; exact h_out_ivl (Nat.zero_le pWalks) h_pW_data_le_outLen ho)).trans
      (hmem2_out addr hs (h_out_ivl (Nat.zero_le 0) h_pEmb_le_outLen ho))
  refine runs_ret_le (v := outLen)
    (by simp only [Expr.eval, BinOp.eval, Function.update_self]
        simp (disch := decide) only [Function.update_of_ne, Function.update_self]
        rw [hretW_eq, h_data_eq_walk]
        exact ite_eq_left_iff.mpr fun h => False.elim (h hres_ltw))
    ⟨rfl, hfull, hfr3⟩
    ?_
  dsimp only [gtEmitCitedHContract, gtEmitCitedJContract, gtEmitEmbToCitedContract, argsSize, Expr.size,
    hEs, exVs]
  clear hDynH_H hDynH_2 hmEmb2 hhEs2 hex2 hjAt2 hjEAt2 hjTAt2 hhEs_H hex_H hjAt_H
    hmemH_out hmem1_out hmem2_out hhdrH hhdr1 hhdr2 hcH_At hcH_At2 hcJ_At hhEsAt hexAt
    hfr' hfrH hfrH' hfrJ hfrJ' hfrW hfrW' hptrs3 hdata3 hfull hfr3
    hdisjH hdisjV hdisjE hdisjT hdisjHd hdisjME hdisjW hDynH hJ hemb hTHd hmEmb hjAt hjEAt hjTAt hjHAt hwLens
  omega

theorem gtForwardCore_meetsContract {w vCap eCap : ℕ} {p : Program}
    {bSort bOps bGT bEmit bFwd : ℕ}
    {H' J : MGraph} {emb : MinCostFlow.Embedding} {jVs jEs jTails jHeads : List ℕ}
    (hpFwd : p.HasAt bFwd (gtForwardProcs bOps bGT bEmit bFwd))
    (hpEmit : p.HasAt bEmit (gtEmitProcs bSort bOps bGT))
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hpGT : p.HasAt bGT (gtProcs bSort bOps))
    (hpSort : p.HasAt bSort (sortProcs bSort)) :
    MeetsContract w p (bFwd + gtIdxForwardCore)
      (gtForwardCoreContract w vCap eCap H' J emb jVs jEs jTails jHeads) := by
  refine meetsContract_of_runs
    (hpFwd.get (i := gtIdxForwardCore) (by simp [gtForwardProcs, gtIdxForwardCore]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨hPtr, jVsPtr, jEsPtr, jTailsPtr, jHeadsPtr, mEmbPtr, scratchPtr, outPtr,
    rfl, hw16, hhB, hjVB, hjEB, hjTB, hjHB, hmEB, hscB, houtB, hscOutDisj,
    hdisjH, hdisjV, hdisjE, hdisjT, hdisjHd, hdisjME, hdisjW,
    hDynH, hJ, hemb, hjV, hjE, hLenT, hLenHd, hTHd, hmEmb, hjAt, hjEAt, hjTAt, hjHAt, hwLens⟩
  let rawEsLen := (collectRawEsFun jEs emb).length
  let hEs := vertsOf (usedHEdges J emb)
  let exVs := vertsOf (usedHVerts H' J emb \ J.V)
  have hjE_iff : ∀ e, e ∈ jEs ↔ e ∈ J.E := by intro e; simp [hjE, mem_vertsOf]
  have hmH_le : hEs.length ≤ rawEsLen := by
    rw [vertsOf_length]
    have hsub : usedHEdges J emb ⊆ (collectRawEsFun jEs emb).toFinset := fun x hx => by
      rw [List.mem_toFinset]; exact (collectRawEsFun_mem hjE_iff x).mpr hx
    exact (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  refine runs_start_le ?_
  dsimp only [gtForwardProcs, gtIdxForwardCore, List.getElem_cons_zero, gtForwardCoreStmt]
  refine runs_seq_triple_le
    (gtForwardCore_scratchPhase (vCap := vCap) (eCap := eCap)
      (jHeadsPtr := jHeadsPtr) (outPtr := outPtr) hpGT hpSort hpOps)
    ⟨hw16, hhB, hjVB, hjEB, hjTB, hmEB, hscB,
     fun i hi => (hdisjH i hi).1, fun i hi => (hdisjV i hi).1,
     fun i hi => (hdisjE i hi).1, fun i hi => (hdisjT i hi).1,
     fun e he => (hdisjME e he).1, fun e he k hk => (hdisjW e he k hk).1,
     hDynH, hJ, hemb, hjV, hjE, hLenT, fun i hi => (hTHd i hi).1, hmEmb, hjAt, hjEAt, hjTAt, hwLens,
     rfl, by simp [startState], by simp [startState], by simp [startState], by simp [startState],
     by simp [startState], by simp [startState], by simp [startState], by simp [startState],
     by simp [startState], by simp [startState]⟩
    ?_
  intro st1 hScr
  obtain ⟨o, st', c₂, hrun, ⟨ho, hfull, hfr3⟩, hcost2⟩ := gtForwardCore_emitPhase ω
    hpEmit hpOps hpGT hpSort hw16 hhB hjVB hjEB hjTB hjHB hmEB hscB houtB hscOutDisj
    hdisjH hdisjV hdisjE hdisjT hdisjHd hdisjME hdisjW hDynH hJ hemb hjV hjE hLenT hLenHd hTHd
    hmEmb hjAt hjEAt hjTAt hjHAt hwLens hScr
  have hval : o.value = (canonSparsifyInput H' J emb).length := by rw [ho]; rfl
  refine ⟨o, st', c₂, hrun, ⟨hPtr, jVsPtr, jEsPtr, jTailsPtr, jHeadsPtr, mEmbPtr, scratchPtr, outPtr,
      rfl, hval, hfull, hfr3⟩, ?_⟩
  have hex_le : exVs.length ≤ jEs.length + rawEsLen := by
    have hT : ∀ i (hi : i < jEs.length), jTails.getD i 0 = J.tail (jEs[i]'hi) :=
      fun i hi => (hTHd i hi).1
    have hex_eq := usedHVerts_sdiff_eq_rawVs (H' := H') (emb := emb) hLenT hjE_iff hT
    rw [show exVs = vertsOf (usedHVerts H' J emb \ J.V) from rfl, vertsOf_length, ← hex_eq]
    calc ((collectRawVsFun H' jEs jTails emb).toFinset \ J.V).card
        ≤ (collectRawVsFun H' jEs jTails emb).toFinset.card := Finset.card_le_card Finset.sdiff_subset
      _ ≤ (collectRawVsFun H' jEs jTails emb).length := List.toFinset_card_le _
      _ = jEs.length + rawEsLen := collectRawVsFun_length_eq H' jEs jTails emb
  dsimp only [gtForwardCoreContract, gtEmitCitedHContract, gtEmitCitedJContract,
    gtEmitEmbToCitedContract] at hcost2 ⊢
  have hraw_eq : (collectRawEsFun jEs emb).length = rawEsLen := rfl
  have hhEs_eq : vertsOf (usedHEdges J emb) = hEs := rfl
  have hexVs_eq : vertsOf (usedHVerts H' J emb \ J.V) = exVs := rfl
  simp only [hraw_eq, hhEs_eq, hexVs_eq] at hcost2 ⊢
  set lArg := jVs.length + 2 * rawEsLen + jEs.length + 2
  set L := Nat.log 2 lArg + 1
  have hl1 : Nat.log 2 (rawEsLen + 1) + 1 ≤ L :=
    Nat.add_le_add_right (Nat.log_mono_right (by dsimp [lArg]; omega)) 1
  have hl2 : Nat.log 2 (rawEsLen + jEs.length + 1) + 1 ≤ L :=
    Nat.add_le_add_right (Nat.log_mono_right (by dsimp [lArg]; omega)) 1
  have hl3 : Nat.log 2 (jVs.length + exVs.length + 1) + 1 ≤ L :=
    Nat.add_le_add_right (Nat.log_mono_right (by dsimp [lArg]; omega)) 1
  have hl4 : Nat.log 2 (jVs.length + 1) + 1 ≤ L :=
    Nat.add_le_add_right (Nat.log_mono_right (by dsimp [lArg]; omega)) 1
  have hl5 : Nat.log 2 (jVs.length + exVs.length + hEs.length + 2) + 1 ≤ L :=
    Nat.add_le_add_right (Nat.log_mono_right (by dsimp [lArg]; omega)) 1
  have hL1 : 500 * rawEsLen * (Nat.log 2 (rawEsLen + 1) + 1) ≤ 500 * rawEsLen * L :=
    Nat.mul_le_mul_left _ hl1
  have hL2 : 250 * (rawEsLen + jEs.length) * (Nat.log 2 (rawEsLen + jEs.length + 1) + 1) ≤
      250 * (rawEsLen + jEs.length) * L := Nat.mul_le_mul_left _ hl2
  have hL3 : 200 * hEs.length * (Nat.log 2 (jVs.length + exVs.length + 1) + 1) ≤
      200 * rawEsLen * L := by
    calc 200 * hEs.length * (Nat.log 2 (jVs.length + exVs.length + 1) + 1)
        ≤ 200 * rawEsLen * (Nat.log 2 (jVs.length + exVs.length + 1) + 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 200 hmH_le)
      _ ≤ 200 * rawEsLen * L := Nat.mul_le_mul_left _ hl3
  have hL4 : 100 * jEs.length * (Nat.log 2 (jVs.length + 1) + 1) ≤ 100 * jEs.length * L :=
    Nat.mul_le_mul_left _ hl4
  have hL5 : 230 * (rawEsLen + jEs.length) *
      (Nat.log 2 (jVs.length + exVs.length + hEs.length + 2) + 1) ≤
      230 * (rawEsLen + jEs.length) * L := Nat.mul_le_mul_left _ hl5
  have hLsum :
      500 * rawEsLen * L + 250 * (rawEsLen + jEs.length) * L + 200 * rawEsLen * L +
        100 * jEs.length * L + 230 * (rawEsLen + jEs.length) * L ≤
      1180 * (rawEsLen + jEs.length) * L := by
    have heq : 500 * rawEsLen * L + 250 * (rawEsLen + jEs.length) * L + 200 * rawEsLen * L +
        100 * jEs.length * L + 230 * (rawEsLen + jEs.length) * L =
        (1180 * rawEsLen + 580 * jEs.length) * L := by ring
    rw [heq]
    exact Nat.mul_le_mul_right L (by omega)
  have hhE_lin : 330 * hEs.length ≤ 330 * rawEsLen := by omega
  omega

theorem gtForwardDyn_meetsContract {w vCapH eCapH vCapJ eCapJ : ℕ} {p : Program}
    {bSort bOps bGT bEmit bFwd : ℕ}
    {H' J : MGraph} {emb : MinCostFlow.Embedding}
    (hpFwd : p.HasAt bFwd (gtForwardProcs bOps bGT bEmit bFwd))
    (hpEmit : p.HasAt bEmit (gtEmitProcs bSort bOps bGT))
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hpGT : p.HasAt bGT (gtProcs bSort bOps))
    (hpSort : p.HasAt bSort (sortProcs bSort)) :
    MeetsContract w p (bFwd + gtIdxForwardDyn)
      (gtForwardDynContract w vCapH eCapH vCapJ eCapJ H' J emb) := by
  refine meetsContract_of_runs
    (hpFwd.get (i := gtIdxForwardDyn) (by simp [gtForwardProcs, gtIdxForwardDyn]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨hPtr, jPtr, mEmbPtr, scratchPtr, outPtr,
    rfl, hw16, hhB, hjB, hmEB, hscB, houtB, hscOutDisj,
    hdisjH, hdisjJ, hdisjME, hdisjW, hDynH, hDynJ, hemb, hmEmb, hwLens⟩
  let jVs := vertsOf J.V
  let jEs := vertsOf J.E
  let jTails := jEs.map J.tail
  let jHeads := jEs.map J.head
  let rawEsLen := (collectRawEsFun jEs emb).length
  let sLen := gtFwdDynScratchLen J.n J.m rawEsLen
  let outLen := (canonSparsifyInput H' J emb).length
  have hscB' : scratchPtr + sLen < 2 ^ w := hscB
  have houtB' : outPtr + outLen < 2 ^ w := houtB
  have hscOut' : scratchPtr + sLen ≤ outPtr ∨ outPtr + outLen ≤ scratchPtr := hscOutDisj
  have hsLen_eq : sLen = 3 * J.n + 6 * J.m + 5 * rawEsLen := rfl
  have hjV_len : jVs.length = J.n := vertsOf_length J.V
  have hjE_len : jEs.length = J.m := vertsOf_length J.E
  have hjE_iff : ∀ e, e ∈ jEs ↔ e ∈ J.E := fun e => by simp [jEs, mem_vertsOf]
  have hvCapJ_ltw : vCapJ < 2 ^ w := by
    have : vCapJ ≤ dynGraphSize vCapJ eCapJ := by unfold dynGraphSize; omega
    omega
  have heCapJ_ltw : eCapJ < 2 ^ w := by
    have : eCapJ ≤ dynGraphSize vCapJ eCapJ := by unfold dynGraphSize; omega
    omega
  have hnJ_le : J.n ≤ vCapJ := dynGraph_n_le_vCap hDynJ
  have hmJ_le : J.m ≤ eCapJ := dynGraph_m_le_eCap hDynJ
  have hlt_hP : hPtr < 2 ^ w := hargs hPtr (by simp)
  have hlt_jP : jPtr < 2 ^ w := hargs jPtr (by simp)
  have hlt_mEP : mEmbPtr < 2 ^ w := hargs mEmbPtr (by simp)
  have hlt_scP : scratchPtr < 2 ^ w := hargs scratchPtr (by simp)
  have hlt_outP : outPtr < 2 ^ w := hargs outPtr (by simp)
  have hlt_nJ : J.n < 2 ^ w := by omega
  have hlt_mJ : J.m < 2 ^ w := by omega
  have hrawEs_ltw : rawEsLen < 2 ^ w := by
    dsimp [rawEsLen, jEs, sLen, gtFwdDynScratchLen] at hscB ⊢; omega
  let jVsPtr := scratchPtr
  let jEsPtr := jVsPtr + J.n
  let jTailsPtr := jEsPtr + J.m
  let jHeadsPtr := jTailsPtr + J.m
  let coreScratch := jHeadsPtr + J.m
  have hjVsP_ltw : jVsPtr < 2 ^ w := hlt_scP
  have hjEsP_ltw : jEsPtr < 2 ^ w := by dsimp [jEsPtr, jVsPtr, sLen, gtFwdDynScratchLen] at *; omega
  have hjTP_ltw : jTailsPtr < 2 ^ w := by dsimp [jTailsPtr, jEsPtr, jVsPtr, sLen, gtFwdDynScratchLen] at *; omega
  have hjHP_ltw : jHeadsPtr < 2 ^ w := by dsimp [jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr, sLen, gtFwdDynScratchLen] at *; omega
  have hcsP_ltw : coreScratch < 2 ^ w := by dsimp [coreScratch, jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr, sLen, gtFwdDynScratchLen] at *; omega
  have hJvalid : J.IsValid := hDynJ.1
  have hjV_eq : jVsPtr = scratchPtr := rfl
  have hjE_eq : jEsPtr = scratchPtr + J.n := rfl
  have hjT_eq : jTailsPtr = scratchPtr + J.n + J.m := rfl
  have hjH_eq : jHeadsPtr = scratchPtr + J.n + 2 * J.m := by
    dsimp only [jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr]; omega
  have hcs_eq : coreScratch = scratchPtr + J.n + 3 * J.m := by
    dsimp only [coreScratch, jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr]; omega
  have h_s_le_cs : scratchPtr ≤ coreScratch := by
    rw [hcs_eq, Nat.add_assoc]; exact Nat.le_add_right _ _
  have h_s_le_e : scratchPtr ≤ jEsPtr := by rw [hjE_eq]; exact Nat.le_add_right _ _
  have h_s_le_t : scratchPtr ≤ jTailsPtr := by rw [hjT_eq, Nat.add_assoc]; exact Nat.le_add_right _ _
  have h_s_le_h : scratchPtr ≤ jHeadsPtr := by rw [hjH_eq, Nat.add_assoc]; exact Nat.le_add_right _ _
  have h_vn_le_cs : jVsPtr + jVs.length ≤ coreScratch := by
    rw [hjV_len, hjV_eq, hcs_eq]; exact Nat.le_add_right _ _
  have h_em_le_cs : jEsPtr + jEs.length ≤ coreScratch := by
    rw [hjE_len, hjE_eq, hcs_eq]; omega
  have h_tm_le_cs : jTailsPtr + jEs.length ≤ coreScratch := by
    rw [hjE_len, hjT_eq, hcs_eq]; omega
  have h_hm_le_cs : jHeadsPtr + jEs.length ≤ coreScratch := by
    rw [hjE_len, hjH_eq, hcs_eq]; omega
  have hjVsB_lt : jVsPtr + jVs.length < 2 ^ w := by rw [hjV_len]; omega
  have hjEsB_lt : jEsPtr + jEs.length < 2 ^ w := by rw [hjE_len]; omega
  have hjTB_lt : jTailsPtr + jEs.length < 2 ^ w := by rw [hjE_len]; omega
  have hjHB_lt : jHeadsPtr + jEs.length < 2 ^ w := by rw [hjE_len]; omega
  have h_cs_core_ub : coreScratch + gtFwdCoreScratchLen jEs.length rawEsLen ≤ scratchPtr + sLen := by
    rw [hcs_eq, hjE_len]
    dsimp only [sLen, gtFwdDynScratchLen, gtFwdCoreScratchLen]
    omega
  have h_cs_ub : coreScratch ≤ scratchPtr + sLen :=
    le_trans (Nat.le_add_right _ _) h_cs_core_ub
  have hcsCore_ltw : coreScratch + gtFwdCoreScratchLen jEs.length rawEsLen < 2 ^ w :=
    lt_of_le_of_lt h_cs_core_ub hscB
  have hcsOut_disj : coreScratch + gtFwdCoreScratchLen jEs.length rawEsLen ≤ outPtr ∨
      outPtr + outLen ≤ coreScratch := by
    rcases hscOutDisj with h | h
    · exact Or.inl (le_trans h_cs_core_ub h)
    · exact Or.inr (le_trans h h_s_le_cs)
  have h_lift_scr : ∀ {addr : ℕ}, addr < scratchPtr ∨ scratchPtr + sLen ≤ addr →
      addr < coreScratch ∨ coreScratch + gtFwdCoreScratchLen jEs.length rawEsLen ≤ addr := by
    intro addr h
    rcases h with h | h
    · exact Or.inl (lt_of_lt_of_le h h_s_le_cs)
    · exact Or.inr (le_trans h_cs_core_ub h)
  have h_range_out : ∀ {p len : ℕ}, scratchPtr ≤ p → p + len ≤ coreScratch →
      ∀ i < len, p + i < outPtr ∨ outPtr + outLen ≤ p + i := fun hsp hpc i hi => by
    rcases hscOutDisj with h | h
    · exact Or.inl (lt_of_lt_of_le (lt_of_lt_of_le (Nat.add_lt_add_left hi _) (le_trans hpc h_cs_ub)) h)
    · exact Or.inr (le_trans h (le_trans hsp (Nat.le_add_right _ _)))
  have hdisjH_core : ∀ i < dynGraphSize vCapH eCapH,
      (hPtr + i < coreScratch ∨ coreScratch + gtFwdCoreScratchLen jEs.length rawEsLen ≤ hPtr + i) ∧
        (hPtr + i < outPtr ∨ outPtr + outLen ≤ hPtr + i) := fun i hi =>
    ⟨h_lift_scr (hdisjH i hi).1, (hdisjH i hi).2⟩
  have hdisjV_core : ∀ i < jVs.length,
      (jVsPtr + i < coreScratch ∨ coreScratch + gtFwdCoreScratchLen jEs.length rawEsLen ≤ jVsPtr + i) ∧
        (jVsPtr + i < outPtr ∨ outPtr + outLen ≤ jVsPtr + i) := fun i hi =>
    ⟨Or.inl (lt_of_lt_of_le (Nat.add_lt_add_left hi _) h_vn_le_cs),
      h_range_out (le_refl _) h_vn_le_cs i hi⟩
  have hdisjE_core : ∀ i < jEs.length,
      (jEsPtr + i < coreScratch ∨ coreScratch + gtFwdCoreScratchLen jEs.length rawEsLen ≤ jEsPtr + i) ∧
        (jEsPtr + i < outPtr ∨ outPtr + outLen ≤ jEsPtr + i) := fun i hi =>
    ⟨Or.inl (lt_of_lt_of_le (Nat.add_lt_add_left hi _) h_em_le_cs),
      h_range_out h_s_le_e h_em_le_cs i hi⟩
  have hdisjT_core : ∀ i < jEs.length,
      (jTailsPtr + i < coreScratch ∨ coreScratch + gtFwdCoreScratchLen jEs.length rawEsLen ≤ jTailsPtr + i) ∧
        (jTailsPtr + i < outPtr ∨ outPtr + outLen ≤ jTailsPtr + i) := fun i hi =>
    ⟨Or.inl (lt_of_lt_of_le (Nat.add_lt_add_left hi _) h_tm_le_cs),
      h_range_out h_s_le_t h_tm_le_cs i hi⟩
  have hdisjHd_core : ∀ i < jEs.length,
      (jHeadsPtr + i < coreScratch ∨ coreScratch + gtFwdCoreScratchLen jEs.length rawEsLen ≤ jHeadsPtr + i) ∧
        (jHeadsPtr + i < outPtr ∨ outPtr + outLen ≤ jHeadsPtr + i) := fun i hi =>
    ⟨Or.inl (lt_of_lt_of_le (Nat.add_lt_add_left hi _) h_hm_le_cs),
      h_range_out h_s_le_h h_hm_le_cs i hi⟩
  have hdisjME_core : ∀ e ∈ J.E,
      (mEmbPtr + e < coreScratch ∨ coreScratch + gtFwdCoreScratchLen jEs.length rawEsLen ≤ mEmbPtr + e) ∧
        (mEmbPtr + e < outPtr ∨ outPtr + outLen ≤ mEmbPtr + e) := fun e he =>
    ⟨h_lift_scr (hdisjME e he).1, (hdisjME e he).2⟩
  have hdisjW_core_mem : ∀ e ∈ J.E, ∀ k < (mWalkEncode (emb e)).length,
      (mem (mEmbPtr + e) + k < coreScratch ∨
          coreScratch + gtFwdCoreScratchLen jEs.length rawEsLen ≤ mem (mEmbPtr + e) + k) ∧
        (mem (mEmbPtr + e) + k < outPtr ∨ outPtr + outLen ≤ mem (mEmbPtr + e) + k) := fun e he k hk =>
    ⟨h_lift_scr (hdisjW e he k hk).1, (hdisjW e he k hk).2⟩
  have hst_r0 : (startState [hPtr, jPtr, mEmbPtr, scratchPtr, outPtr] mem pos).regs 0 = hPtr := by
    simp [startState]
  have hst_r1 : (startState [hPtr, jPtr, mEmbPtr, scratchPtr, outPtr] mem pos).regs 1 = jPtr := by
    simp [startState]
  have hst_r2 : (startState [hPtr, jPtr, mEmbPtr, scratchPtr, outPtr] mem pos).regs 2 = mEmbPtr := by
    simp [startState]
  have hst_r3 : (startState [hPtr, jPtr, mEmbPtr, scratchPtr, outPtr] mem pos).regs 3 = scratchPtr := by
    simp [startState]
  have hst_r4 : (startState [hPtr, jPtr, mEmbPtr, scratchPtr, outPtr] mem pos).regs 4 = outPtr := by
    simp [startState]
  dsimp only [gtForwardProcs, gtIdxForwardDyn, List.getElem_cons_succ, List.getElem_cons_zero,
    gtForwardDynStmt]
  refine runs_start_le ?_
  refine runs_seq_triple_le
    (gtForwardDyn_prepPhase (vCapJ := vCapJ) (eCapJ := eCapJ) (rawEsLen := rawEsLen)
      (J := J) hpOps hpGT hpSort)
    ⟨hw16, hlt_hP, hjB, hlt_mEP, hlt_outP, hscB, fun i hi => (hdisjJ i hi).1, hDynJ, rfl,
      hst_r0, hst_r1, hst_r2, hst_r3, hst_r4⟩
    ?_
  intro st5 ⟨hr0, hr1, hr2, hr3, hr4, hr7, hr8, hr9, hr10, hr11, hr12, hr13,
    hVAt5, hEAt5, hTAt5, hHAt5, hfr5_out⟩
  have hDynH5 : DynGraphAt st5.mem hPtr vCapH eCapH H' := by
    refine hDynH.of_agree fun addr ha1 ha2 => ?_
    have hdj := (hdisjH (addr - hPtr) (Nat.sub_lt_left_of_lt_add ha1 ha2)).1
    rw [Nat.add_sub_cancel' ha1] at hdj
    exact hfr5_out addr hdj
  have hmEmb5 : MEmbAt st5.mem mEmbPtr J.E eCapH emb := fun e he => by
    rcases hmEmb e he with ⟨heCap, hmw⟩
    refine ⟨heCap, ?_⟩
    rw [hfr5_out _ (hdisjME e he).1]
    exact fun k hk => by
      rw [hfr5_out _ (hdisjW e he k hk).1]
      exact hmw k hk
  refine runs_seq_call_le
    (gtForwardCore_meetsContract (vCap := vCapH) (eCap := eCapH)
      (H' := H') (J := J) (emb := emb) (jVs := jVs) (jEs := jEs)
      (jTails := jTails) (jHeads := jHeads) hpFwd hpEmit hpOps hpGT hpSort)
    (vs := [hPtr, jVs.length, jEs.length, jVsPtr, jEsPtr, jTailsPtr, jHeadsPtr,
      mEmbPtr, coreScratch, outPtr])
    (by simp only [evalArgs, Expr.eval, hr0, hr7, hr8, hr9, hr10, hr11, hr12, hr2, hr13, hr4,
          hjV_len, hjE_len]
        rfl)
    (by intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hlt_hP
        · rw [hjV_len]; exact hlt_nJ
        · rw [hjE_len]; exact hlt_mJ
        · exact hjVsP_ltw
        · exact hjEsP_ltw
        · exact hjTP_ltw
        · exact hjHP_ltw
        · exact hlt_mEP
        · exact hcsP_ltw
        · exact hlt_outP)
    ⟨hPtr, jVsPtr, jEsPtr, jTailsPtr, jHeadsPtr, mEmbPtr, coreScratch, outPtr,
      rfl, hw16, hhB, hjVsB_lt, hjEsB_lt, hjTB_lt, hjHB_lt, hmEB, hcsCore_ltw, houtB,
      hcsOut_disj, hdisjH_core, hdisjV_core, hdisjE_core, hdisjT_core, hdisjHd_core,
      hdisjME_core, fun e he k hk => by dsimp only; rw [hfr5_out _ (hdisjME e he).1]; exact hdisjW_core_mem e he k hk,
      hDynH5, hJvalid, hemb, rfl, rfl, by simp [jTails], by simp [jHeads],
      fun i hi => ⟨by simp [jTails, hi], by simp [jHeads, hi]⟩,
      hmEmb5, hVAt5, hEAt5, hTAt5, hHAt5,
      fun e he => by
        rw [hfr5_out _ (hdisjME e he).1]
        exact hwLens e he⟩
    ?_
  intro ret mem6 pos6 ⟨_, _, _, _, _, _, _, _, hargs6, hret6, hcanon6, hfr6⟩
  simp only [List.cons.injEq, and_true] at hargs6
  rcases hargs6 with ⟨rfl, -, -, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hfr6_out : ∀ addr, (addr < scratchPtr ∨ scratchPtr + sLen ≤ addr) →
      (addr < outPtr ∨ outPtr + outLen ≤ addr) → mem6 addr = mem addr :=
    fun addr hs ho => by
      have hs' : addr < coreScratch ∨ coreScratch + gtFwdCoreScratchLen jEs.length rawEsLen ≤ addr :=
        h_lift_scr hs
      exact (hfr6 addr hs' ho).trans (hfr5_out addr hs)
  refine runs_ret_le (v := ret)
    (by simp [Expr.eval, Function.update_self])
    ⟨hPtr, jPtr, mEmbPtr, scratchPtr, outPtr, rfl, hret6, hcanon6, hfr6_out⟩
    ?_
  dsimp only [gtForwardDynContract, gtForwardCoreContract, argsSize, Expr.size]
  have hraw_eq : (collectRawEsFun (vertsOf J.E) emb).length = rawEsLen := rfl
  have hraw_eq2 : (collectRawEsFun jEs emb).length = rawEsLen := rfl
  simp only [hraw_eq, hraw_eq2]
  set lArg := J.n + 2 * rawEsLen + J.m + 2
  set L := Nat.log 2 lArg + 1
  have hl_n : Nat.log 2 (J.n + 1) + 1 ≤ L :=
    Nat.add_le_add_right (Nat.log_mono_right (by dsimp [lArg]; omega)) 1
  have hl_m : Nat.log 2 (J.m + 1) + 1 ≤ L :=
    Nat.add_le_add_right (Nat.log_mono_right (by dsimp [lArg]; omega)) 1
  have hL_n : 250 * J.n * (Nat.log 2 (J.n + 1) + 1) ≤ 250 * J.n * L :=
    Nat.mul_le_mul_left _ hl_n
  have hL_m : 250 * J.m * (Nat.log 2 (J.m + 1) + 1) ≤ 250 * J.m * L :=
    Nat.mul_le_mul_left _ hl_m
  have hl_c : jVs.length + 2 * rawEsLen + jEs.length + 2 = lArg := by
    dsimp [lArg]; rw [hjV_len, hjE_len]
  have hL_c : 1180 * (rawEsLen + jEs.length) *
      (Nat.log 2 (jVs.length + 2 * rawEsLen + jEs.length + 2) + 1) =
      1180 * (rawEsLen + J.m) * L := by
    rw [hl_c, hjE_len]
  have hLsum : 250 * J.n * L + 250 * J.m * L + 1180 * (rawEsLen + J.m) * L ≤
      1430 * (J.n + J.m + rawEsLen) * L := by
    have heq : 250 * J.n * L + 250 * J.m * L + 1180 * (rawEsLen + J.m) * L =
        (250 * J.n + 1430 * J.m + 1180 * rawEsLen) * L := by ring
    rw [heq]
    exact Nat.mul_le_mul_right L (by omega)
  have hlin_c : 950 * (jVs.length + jEs.length + rawEsLen) = 950 * (J.n + J.m + rawEsLen) := by
    rw [hjV_len, hjE_len]
  omega

end

end MinCostFlow.DynSpanner.Program
