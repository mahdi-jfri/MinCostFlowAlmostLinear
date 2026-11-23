module

public import MinCostFlow.DynSpanner.Program.GraphTranslateEmit

/-!
# Graph Translation: Nonempty Walk Emitter Branch Helper

Verifies `gtEmitEmbToCited_nonemptyBranch` for the nonempty-walk branch of
`gtEmitEmbToCitedStmt`, split from `GraphTranslateEmitWalk` to keep module sizes bounded.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner

private lemma runs_seq_cond_true_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {e : Expr} {s₁ s₂ rest : Stmt} {v : ℕ} {k bound : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (h : ∃ o₁ st₁ c₁, Runs w p ω s₁ st o₁ st₁ c₁ ∧
      (match o₁ with
      | .returned u => Q (.returned u) st₁ ∧ k + e.size + c₁ + 2 ≤ bound
      | .normal => ∃ o₂ st₂ c₂, Runs w p ω rest st₁ o₂ st₂ c₂ ∧ Q o₂ st₂ ∧
          k + e.size + c₁ + c₂ + 2 ≤ bound)) :
    ∃ o st' c, Runs w p ω (.seq (.cond e s₁ s₂) rest) st o st' c ∧ Q o st' ∧ k + c ≤ bound := by
  rcases h with ⟨o₁, st₁, c₁, hr₁, hcont⟩
  cases o₁ with
  | returned u =>
    refine ⟨.returned u, st₁, (e.size + c₁ + 1) + 1,
      runs_seq_iff.mpr (Or.inl ⟨u, e.size + c₁ + 1,
        runs_cond_iff.mpr ⟨v, c₁, he, by simpa [hv] using hr₁, rfl⟩, rfl, rfl⟩),
      hcont.1, by omega⟩
  | normal =>
    rcases hcont with ⟨o₂, st₂, c₂, hr₂, hq, hc⟩
    refine ⟨o₂, st₂, (e.size + c₁ + 1) + c₂ + 1,
      runs_seq_iff.mpr (Or.inr ⟨st₁, e.size + c₁ + 1, c₂,
        runs_cond_iff.mpr ⟨v, c₁, he, by simpa [hv] using hr₁, rfl⟩, hr₂, rfl⟩),
      hq, by omega⟩

private lemma runs_seq_cond_false_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {e : Expr} {s₁ s₂ rest : Stmt} {k bound : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some 0)
    (h : ∃ o₁ st₁ c₁, Runs w p ω s₂ st o₁ st₁ c₁ ∧
      (match o₁ with
      | .returned u => Q (.returned u) st₁ ∧ k + e.size + c₁ + 2 ≤ bound
      | .normal => ∃ o₂ st₂ c₂, Runs w p ω rest st₁ o₂ st₂ c₂ ∧ Q o₂ st₂ ∧
          k + e.size + c₁ + c₂ + 2 ≤ bound)) :
    ∃ o st' c, Runs w p ω (.seq (.cond e s₁ s₂) rest) st o st' c ∧ Q o st' ∧ k + c ≤ bound := by
  rcases h with ⟨o₁, st₁, c₁, hr₁, hcont⟩
  cases o₁ with
  | returned u =>
    refine ⟨.returned u, st₁, (e.size + c₁ + 1) + 1,
      runs_seq_iff.mpr (Or.inl ⟨u, e.size + c₁ + 1,
        runs_cond_iff.mpr ⟨0, c₁, he, by simpa using hr₁, rfl⟩, rfl, rfl⟩),
      hcont.1, by omega⟩
  | normal =>
    rcases hcont with ⟨o₂, st₂, c₂, hr₂, hq, hc⟩
    refine ⟨o₂, st₂, (e.size + c₁ + 1) + c₂ + 1,
      runs_seq_iff.mpr (Or.inr ⟨st₁, e.size + c₁ + 1, c₂,
        runs_cond_iff.mpr ⟨0, c₁, he, by simpa using hr₁, rfl⟩, hr₂, rfl⟩),
      hq, by omega⟩


private lemma rangeCost_embLen_prefix (jEs : List ℕ) (emb : MinCostFlow.Embedding) :
    ∀ k ≤ jEs.length,
      rangeCost (fun j => (emb (jEs.getD j 0)).length) 0 k =
        ((jEs.take k).flatMap fun e => (emb e).map Prod.fst).length := by
  intro k hk
  rw [rangeCost_zero_eq_range]
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k < jEs.length := hk
    rw [List.range_succ, List.map_append, List.sum_append, ih (Nat.le_of_lt hk'),
      List.take_succ_eq_append_getElem hk', List.flatMap_append, List.length_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_map,
      List.getD_eq_getElem _ _ hk']


private lemma listAt_update_lt {mem : ℕ → ℕ} {a x v : ℕ} {L : List ℕ}
    (h : ListAt mem a L) (hx : x < a) :
    ListAt (Function.update mem x v) a L := by
  intro i hi
  rw [Function.update_of_ne (by omega)]
  exact h i hi

private lemma natLog_mono_le {a b : ℕ} (hab : a ≤ b) : Nat.log 2 a ≤ Nat.log 2 b :=
  Nat.log_mono_right hab

private lemma usedHVerts_mem_jVs_or_exVs {H' J : MGraph} {emb : MinCostFlow.Embedding}
    {jVs exVs : List ℕ}
    (hjV : jVs = vertsOf J.V)
    (hexV : exVs = vertsOf (usedHVerts H' J emb \ J.V))
    {v : ℕ} (hv : v ∈ usedHVerts H' J emb) :
    v ∈ jVs ++ exVs := by
  by_cases hJ : v ∈ J.V
  · exact List.mem_append_left _ (hjV ▸ mem_vertsOf.mpr hJ)
  · exact List.mem_append_right _ (hexV ▸ mem_vertsOf.mpr (Finset.mem_sdiff.mpr ⟨hv, hJ⟩))

private lemma walkStep_in_usedH {H' J : MGraph} {emb : MinCostFlow.Embedding}
    (hemb : emb.IsEmbedding J H') {e : ℕ} (he : e ∈ J.E)
    {t : ℕ} (ht : t < (emb e).length) :
    ((emb e)[t]'ht).1 ∈ H'.E ∧
    ((emb e)[t]'ht).1 ∈ usedHEdges J emb ∧
    H'.dst ((emb e)[t]'ht) ∈ usedHVerts H' J emb := by
  have hw := hemb.2 e he
  have hs_mem : (emb e)[t]'ht ∈ emb e := List.getElem_mem ht
  have he_H : ((emb e)[t]'ht).1 ∈ H'.E :=
    (mgraph_mem_walkVertices_src_dst hw _ hs_mem).1
  have he_used : ((emb e)[t]'ht).1 ∈ usedHEdges J emb := by
    simp only [usedHEdges, Finset.mem_biUnion, List.mem_toFinset, MinCostFlow.walkEdges,
      List.mem_map]
    exact ⟨e, he, _, hs_mem, rfl⟩
  have hv_used : H'.dst ((emb e)[t]'ht) ∈ usedHVerts H' J emb := by
    simp only [usedHVerts, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset,
      MGraph.walkVertices, List.mem_cons, List.mem_map]
    right
    exact ⟨e, he, Or.inr ⟨_, hs_mem, rfl⟩⟩
  exact ⟨he_H, he_used, hv_used⟩


public section

lemma runs_cond_true_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {e : Expr} {s t : Stmt} {v : ℕ} {k bound : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (h : ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ bound) :
    ∃ o st' c, Runs w p ω (.cond e s t) st o st' c ∧ Q o st' ∧ k + c ≤ bound := by
  rcases h with ⟨o, st', c, hr, hq, hc⟩
  exact ⟨o, st', e.size + c + 1, runs_cond_iff.mpr ⟨v, c, he, by simpa [hv] using hr, rfl⟩,
    hq, by omega⟩

lemma runs_cond_false_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {e : Expr} {s t : Stmt} {k bound : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some 0)
    (h : ∃ o st' c, Runs w p ω t st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ bound) :
    ∃ o st' c, Runs w p ω (.cond e s t) st o st' c ∧ Q o st' ∧ k + c ≤ bound := by
  rcases h with ⟨o, st', c, hr, hq, hc⟩
  exact ⟨o, st', e.size + c + 1, runs_cond_iff.mpr ⟨0, c, he, by simpa using hr, rfl⟩,
    hq, by omega⟩


lemma rangeCost_embLen_eq (jEs : List ℕ) (emb : MinCostFlow.Embedding) :
    rangeCost (fun j => (emb (jEs.getD j 0)).length) 0 jEs.length =
      (collectRawEsFun jEs emb).length := by
  simpa [collectRawEsFun] using rangeCost_embLen_prefix jEs emb jEs.length le_rfl


lemma gtEmitEmbToCited_nonemptyBranch {w vCap eCap : ℕ} {p : Program}
    {bSort bOps bGT : ℕ} {H' J : MGraph} {emb : MinCostFlow.Embedding}
    {jVs exVs jEs jTails hEs : List ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hpGT : p.HasAt bGT (gtProcs bSort bOps))
    (hpSort : p.HasAt bSort (sortProcs bSort))
    {memCond : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    {hPtr jEsPtr jTailsPtr mEmbPtr jVsPtr exVsPtr hEsPtr ptrsOut dataOut offBase : ℕ}
    {j e wPtr curLen k0 bound : ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hDynH : DynGraphAt memCond hPtr vCap eCap H')
    (hJ : J.IsValid) (hemb : emb.IsEmbedding J H')
    (hjV : jVs = vertsOf J.V) (hexV : exVs = vertsOf (usedHVerts H' J emb \ J.V))
    (hjE : jEs = vertsOf J.E) (hhE : hEs = vertsOf (usedHEdges J emb))
    (hLenT : jTails.length = jEs.length)
    (hTH : ∀ i (hi : i < jEs.length), jTails.getD i 0 = J.tail (jEs[i]'hi))
    (hjAt : ListAt memCond jVsPtr jVs) (hexAt : ListAt memCond exVsPtr exVs)
    (hhEAt : ListAt memCond hEsPtr hEs) (hjTAt : ListAt memCond jTailsPtr jTails)
    (hjw : ∀ x ∈ jVs, x < 2 ^ w) (hexw : ∀ x ∈ exVs, x < 2 ^ w) (hhew : ∀ x ∈ hEs, x < 2 ^ w)
    (hjVPair : jVs.Pairwise (· < ·)) (hexPair : exVs.Pairwise (· < ·))
    (hhEPair : hEs.Pairwise (· < ·)) (hdisj_vex : ∀ x ∈ jVs, x ∉ exVs)
    (hhB : hPtr + dynGraphSize vCap eCap < 2 ^ w)
    (hjVB : jVsPtr + jVs.length < 2 ^ w) (hexB : exVsPtr + exVs.length < 2 ^ w)
    (hhEB : hEsPtr + hEs.length < 2 ^ w) (hjTB : jTailsPtr + jEs.length < 2 ^ w)
    (hnHB : jVs.length + exVs.length < 2 ^ w)
    (hdisjH : ∀ i < dynGraphSize vCap eCap,
      hPtr + i < dataOut + curLen ∨ dataOut + curLen + (2 * (emb e).length + 3) ≤ hPtr + i)
    (hdisjJT : ∀ i < jEs.length,
      jTailsPtr + i < dataOut + curLen ∨ dataOut + curLen + (2 * (emb e).length + 3) ≤ jTailsPtr + i)
    (hdisjV : ∀ i < jVs.length,
      jVsPtr + i < dataOut + curLen ∨ dataOut + curLen + (2 * (emb e).length + 3) ≤ jVsPtr + i)
    (hdisjEx : ∀ i < exVs.length,
      exVsPtr + i < dataOut + curLen ∨ dataOut + curLen + (2 * (emb e).length + 3) ≤ exVsPtr + i)
    (hdisjHE : ∀ i < hEs.length,
      hEsPtr + i < dataOut + curLen ∨ dataOut + curLen + (2 * (emb e).length + 3) ≤ hEsPtr + i)
    (hj_lt : j < jEs.length) (he_eq : e = jEs[j]'hj_lt) (hne : (emb e).length ≠ 0)
    (hmw : MWalkAt memCond wPtr (emb e))
    (hwLenB : (emb e).length < 2 ^ w)
    (hwPtrB : wPtr + (mWalkEncode (emb e)).length < 2 ^ w)
    (hdisjW : ∀ k < (mWalkEncode (emb e)).length,
      wPtr + k < dataOut + curLen ∨ dataOut + curLen + (2 * (emb e).length + 3) ≤ wPtr + k)
    (hOutB : dataOut + curLen + (2 * (emb e).length + 3) < 2 ^ w)
    (hReg : st.mem = memCond ∧ st.regs 0 = hPtr ∧ st.regs 1 = jEs.length ∧ st.regs 2 = jEsPtr ∧
      st.regs 3 = jTailsPtr ∧ st.regs 4 = mEmbPtr ∧ st.regs 5 = jVsPtr ∧
      st.regs 6 = jVs.length ∧ st.regs 7 = exVsPtr ∧ st.regs 8 = exVs.length ∧
      st.regs 9 = hEsPtr ∧ st.regs 10 = hEs.length ∧ st.regs 11 = ptrsOut ∧
      st.regs 12 = dataOut ∧ st.regs 13 = offBase ∧ st.regs 14 = curLen ∧ st.regs 15 = j ∧
      st.regs 16 = e ∧ st.regs 17 = wPtr ∧ st.regs 18 = (emb e).length)
    (hbound : k0 +
      (90 * (Nat.log 2 (jVs.length + exVs.length + hEs.length + 2) + 1) +
       135 * (emb e).length * (Nat.log 2 (jVs.length + exVs.length + hEs.length + 2) + 1) +
       225 * (emb e).length + 140) ≤ bound) :
    let wLen := (emb e).length
    let wPtrOut := dataOut + curLen
    let branch :=
      .assign 19 (.bin .add (.reg 12) (.reg 14)) ;;
      .store (.reg 19) (.bin .add (.reg 18) (.const 1)) ;;
      .store (.bin .add (.reg 19) (.bin .add (.const 2) (.reg 18))) (.reg 18) ;;
      .assign 20 (.load (.bin .add (.reg 3) (.reg 15))) ;;
      .call 21 (bGT + gtIdxLookupHVert) [.reg 5, .reg 6, .reg 7, .reg 8, .reg 20] ;;
      .store (.bin .add (.reg 19) (.const 1)) (.reg 21) ;;
      forRange 20 (.const 0) (.reg 18)
        (.assign 21 (.load (.bin .add (.reg 17) (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 20))))) ;;
         .assign 22 (.load (.bin .add (.reg 17) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 20))))) ;;
         .cond (.bin .eq (.reg 22) (.const 1))
           (.call 23 (bOps + dgIdxGetHead) [.reg 0, .reg 21])
           (.call 23 (bOps + dgIdxGetTail) [.reg 0, .reg 21]) ;;
         .call 24 (bGT + gtIdxLookupHVert) [.reg 5, .reg 6, .reg 7, .reg 8, .reg 23] ;;
         .store (.bin .add (.reg 19) (.bin .add (.const 2) (.reg 20))) (.reg 24) ;;
         .call 24 (bSort + sortIdxBinSearch) [.reg 9, .reg 10, .reg 21] ;;
         .store (.bin .add (.reg 19) (.bin .add (.bin .add (.const 3) (.reg 18)) (.reg 20))) (.reg 24)) ;;
      .assign 14 (.bin .add (.reg 14) (.bin .add (.bin .mul (.const 2) (.reg 18)) (.const 3)))
    ∃ o st' c, Runs w p ω branch st o st' c ∧
      (o = .normal ∧
       (∀ r ≤ 13, st'.regs r = st.regs r) ∧
       st'.regs 14 = curLen + (2 * wLen + 3) ∧
       st'.regs 15 = j ∧
       ListAt st'.mem wPtrOut (Walk.encode (embToCited H' J emb j)) ∧
       ∀ addr, addr < wPtrOut ∨ wPtrOut + (2 * wLen + 3) ≤ addr → st'.mem addr = memCond addr) ∧
      k0 + c ≤ bound := by
  dsimp only
  let wLen := (emb e).length
  let wPtrOut := dataOut + curLen
  let Llog := Nat.log 2 (jVs.length + exVs.length + hEs.length + 2) + 1
  rcases hReg with ⟨hmemEq, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13,
    hr14, hr15, hr16, hr17, hr18⟩
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  have h3_lt : (3 : ℕ) < 2 ^ w := by omega
  have hlt_nJ : jVs.length < 2 ^ w := by omega
  have hlt_nEx : exVs.length < 2 ^ w := by omega
  have hlt_mH : hEs.length < 2 ^ w := by omega
  have hlt_hP : hPtr < 2 ^ w := by omega
  have hlt_jP : jVsPtr < 2 ^ w := by omega
  have hlt_exP : exVsPtr < 2 ^ w := by omega
  have hlt_hEP : hEsPtr < 2 ^ w := by omega
  have hlt_jTP : jTailsPtr < 2 ^ w := by omega
  have hlt_dO : dataOut < 2 ^ w := by omega
  have hlt_cL : curLen < 2 ^ w := by omega
  have hlt_wP : wPtr < 2 ^ w := by omega
  have hwLen1_lt : wLen + 1 < 2 ^ w := by omega
  have h2wLen_lt : 2 + wLen < 2 ^ w := by omega
  have h3wLen_lt : 3 + wLen < 2 ^ w := by omega
  have h2mulw_lt : 2 * wLen < 2 ^ w := by omega
  have h2w3_lt : 2 * wLen + 3 < 2 ^ w := by omega
  have hj_ltw : j < 2 ^ w := by omega
  have hwPtrOut_lt : wPtrOut < 2 ^ w := by omega
  have hwPtrOut1_lt : wPtrOut + 1 < 2 ^ w := by omega
  have hwPtrOut2_lt : wPtrOut + (2 + wLen) < 2 ^ w := by omega
  have heJ : e ∈ J.E := by
    have hm : e ∈ vertsOf J.E := he_eq ▸ hjE ▸ List.getElem_mem hj_lt
    rwa [mem_vertsOf] at hm
  have hP_ne : emb e ≠ [] := fun hnil => hne (by simp [hnil])
  have hjT : j < jTails.length := hLenT ▸ hj_lt
  have hTailE : jTails[j]'hjT = J.tail e := by
    have ht := hTH j hj_lt
    rw [List.getD_eq_getElem jTails 0 hjT] at ht
    rw [he_eq]; exact ht
  have hTailV_mem : J.tail e ∈ jVs := by
    rw [hjV, mem_vertsOf]; exact (hJ _ heJ).1
  have hTailV_used : J.tail e ∈ jVs ++ exVs := List.mem_append_left _ hTailV_mem
  have hTailV_ltw : J.tail e < 2 ^ w := hjw _ hTailV_mem
  have hlogHV : Nat.log 2 (jVs.length + exVs.length + 1) + 1 ≤ Llog := by
    dsimp only [Llog]
    exact Nat.add_le_add_right (natLog_mono_le (by omega)) 1
  have hlogHE : Nat.log 2 (hEs.length + 1) + 1 ≤ Llog := by
    dsimp only [Llog]
    exact Nat.add_le_add_right (natLog_mono_le (by omega)) 1
  -- Step 1: assign 19 := wPtrOut
  refine runs_seq_assign_le (v := wPtrOut)
    (by simp [Expr.eval, BinOp.eval, hr12, hr14, hwPtrOut_lt, wPtrOut]) ?_
  -- Step 2: store wPtrOut := wLen + 1
  refine runs_seq_store_le (x := wPtrOut) (v := wLen + 1)
    (by simp [Expr.eval, Function.update_self, wPtrOut])
    (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr18, h1_lt, hwLen1_lt, wLen]) ?_
  -- Step 3: store wPtrOut + (2 + wLen) := wLen
  refine runs_seq_store_le (x := wPtrOut + (2 + wLen)) (v := wLen)
    (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, Function.update_self, hr18, h2_lt,
      h2wLen_lt, hwPtrOut2_lt, wLen])
    (by simp [Expr.eval, Function.update_of_ne, hr18, wLen]) ?_
  -- Step 4: assign 20 := J.tail e
  have hT_mem1 : (Function.update (Function.update st.mem wPtrOut (wLen + 1))
      (wPtrOut + (2 + wLen)) wLen) (jTailsPtr + j) = J.tail e := by
    have hne1 : jTailsPtr + j ≠ wPtrOut := by rcases hdisjJT j hj_lt with h | h <;> omega
    have hne2 : jTailsPtr + j ≠ wPtrOut + (2 + wLen) := by
      rcases hdisjJT j hj_lt with h | h <;> omega
    rw [Function.update_of_ne hne2, Function.update_of_ne hne1, hmemEq, hjTAt j hjT, hTailE]
  refine runs_seq_assign_le
    (Expr.eval_load_of_eq (v := J.tail e)
      (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, hr3, hr15,
        show jTailsPtr + j < 2 ^ w by omega])
      hT_mem1) ?_
  -- Step 5: call 21 gtLookupHVert
  set mem2 := Function.update (Function.update st.mem wPtrOut (wLen + 1))
    (wPtrOut + (2 + wLen)) wLen
  have hjAt2 : ListAt mem2 jVsPtr jVs := fun t ht => by
    have hne1 : jVsPtr + t ≠ wPtrOut := by rcases hdisjV t ht with h | h <;> omega
    have hne2 : jVsPtr + t ≠ wPtrOut + (2 + wLen) := by rcases hdisjV t ht with h | h <;> omega
    dsimp only [mem2]
    rw [Function.update_of_ne hne2, Function.update_of_ne hne1, hmemEq]
    exact hjAt t ht
  have hexAt2 : ListAt mem2 exVsPtr exVs := fun t ht => by
    have hne1 : exVsPtr + t ≠ wPtrOut := by rcases hdisjEx t ht with h | h <;> omega
    have hne2 : exVsPtr + t ≠ wPtrOut + (2 + wLen) := by rcases hdisjEx t ht with h | h <;> omega
    dsimp only [mem2]
    rw [Function.update_of_ne hne2, Function.update_of_ne hne1, hmemEq]
    exact hexAt t ht
  have hwt0 : ∀ v ∈ [jVsPtr, jVs.length, exVsPtr, exVs.length, J.tail e], v < 2 ^ w := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_jP
    rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_nJ
    rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_exP
    rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_nEx
    rcases List.mem_cons.mp hv with rfl | hv; · exact hTailV_ltw
    cases hv
  have hpre0 : (gtLookupHVertContract w jVs exVs (J.tail e)).pre
      [jVsPtr, jVs.length, exVsPtr, exVs.length, J.tail e] mem2 :=
    ⟨jVsPtr, exVsPtr, rfl, hw16, hjVB, hexB, hTailV_ltw, hnHB, hjVPair, hexPair, hdisj_vex,
     hTailV_used, hjAt2, hexAt2, hjw, hexw⟩
  refine runs_seq_call_le (gtLookupHVert_meetsContract hpGT hpSort)
    (by simp [evalArgs, Expr.eval, Function.update_of_ne, Function.update_self,
      hr5, hr6, hr7, hr8])
    hwt0 hpre0 ?_
  rintro idx0 mem3 _ ⟨_, _, _, hmem3, hidx0, hidx0_lt⟩
  subst hmem3
  have hidx0_ltw : idx0 < 2 ^ w := by omega
  -- Step 6: store wPtrOut + 1 := idx0
  refine runs_seq_store_le (x := wPtrOut + 1) (v := idx0)
    (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, Function.update_self,
      h1_lt, hwPtrOut1_lt])
    (by simp [Expr.eval, Function.update_self]) ?_
  set mem0 := Function.update mem2 (wPtrOut + 1) idx0
  let pv : ℕ → List ℕ := fun t =>
    (List.range t).map fun s => (jVs ++ exVs).idxOf (H'.dst ((emb e)[s]!))
  let pe : ℕ → List ℕ := fun t =>
    (List.range t).map fun s => hEs.idxOf ((emb e)[s]!).1
  have hpv_len : ∀ t, (pv t).length = t := fun t => by simp [pv]
  have hpe_len : ∀ t, (pe t).length = t := fun t => by simp [pe]
  let regs0 : ℕ → ℕ := Function.update
    (Function.update
      (Function.update
        (Function.update st.regs 19 wPtrOut) 20 (J.tail e))
      21 idx0)
    21 idx0
  have hregs0_eq : ∀ r ≤ 19,
      Function.update (Function.update (Function.update st.regs 19 wPtrOut) 20 (J.tail e)) 21 idx0 r =
      (if r = 19 then wPtrOut else st.regs r) := by
    intro r hr
    by_cases h19 : r = 19
    · subst h19; simp [Function.update_of_ne]
    · simp [h19, Function.update_of_ne (by omega : r ≠ 21),
        Function.update_of_ne (by omega : r ≠ 20)]
  let bodyIn : Stmt :=
    .assign 21 (.load (.bin .add (.reg 17) (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 20))))) ;;
    .assign 22 (.load (.bin .add (.reg 17) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 20))))) ;;
    .cond (.bin .eq (.reg 22) (.const 1))
      (.call 23 (bOps + dgIdxGetHead) [.reg 0, .reg 21])
      (.call 23 (bOps + dgIdxGetTail) [.reg 0, .reg 21]) ;;
    .call 24 (bGT + gtIdxLookupHVert) [.reg 5, .reg 6, .reg 7, .reg 8, .reg 23] ;;
    .store (.bin .add (.reg 19) (.bin .add (.const 2) (.reg 20))) (.reg 24) ;;
    .call 24 (bSort + sortIdxBinSearch) [.reg 9, .reg 10, .reg 21] ;;
    .store (.bin .add (.reg 19) (.bin .add (.bin .add (.const 3) (.reg 18)) (.reg 20))) (.reg 24)
  let InvInPre : State → Prop := fun s =>
    s.regs 0 = hPtr ∧ s.regs 5 = jVsPtr ∧ s.regs 6 = jVs.length ∧
    s.regs 7 = exVsPtr ∧ s.regs 8 = exVs.length ∧ s.regs 9 = hEsPtr ∧ s.regs 10 = hEs.length ∧
    (∀ r ≤ 13, s.regs r = st.regs r) ∧
    s.regs 14 = curLen ∧ s.regs 15 = j ∧ s.regs 17 = wPtr ∧ s.regs 18 = wLen ∧
    s.regs 19 = wPtrOut ∧
    s.mem wPtrOut = wLen + 1 ∧ s.mem (wPtrOut + 1) = idx0 ∧
    s.mem (wPtrOut + (2 + wLen)) = wLen ∧
    ListAt s.mem (wPtrOut + 2) (pv 0) ∧
    ListAt s.mem (wPtrOut + (3 + wLen)) (pe 0) ∧
    ∀ addr, addr < wPtrOut ∨ wPtrOut + (2 * wLen + 3) ≤ addr → s.mem addr = memCond addr
  let InvIn : ℕ → State → Prop := fun t s =>
    s.regs 0 = hPtr ∧ s.regs 5 = jVsPtr ∧ s.regs 6 = jVs.length ∧
    s.regs 7 = exVsPtr ∧ s.regs 8 = exVs.length ∧ s.regs 9 = hEsPtr ∧ s.regs 10 = hEs.length ∧
    (∀ r ≤ 13, s.regs r = st.regs r) ∧
    s.regs 14 = curLen ∧ s.regs 15 = j ∧ s.regs 17 = wPtr ∧ s.regs 18 = wLen ∧
    s.regs 19 = wPtrOut ∧ s.regs 20 = t ∧
    s.mem wPtrOut = wLen + 1 ∧ s.mem (wPtrOut + 1) = idx0 ∧
    s.mem (wPtrOut + (2 + wLen)) = wLen ∧
    ListAt s.mem (wPtrOut + 2) (pv t) ∧
    ListAt s.mem (wPtrOut + (3 + wLen)) (pe t) ∧
    ∀ addr, addr < wPtrOut ∨ wPtrOut + (2 * wLen + 3) ≤ addr → s.mem addr = memCond addr
  let innerC := 135 * Llog + 216
  have hloop : Triple w p InvInPre (forRange 20 (.const 0) (.reg 18) bodyIn)
      (normalPost (InvIn wLen))
      (fun _ => wLen * (innerC + Expr.size (.reg 18) + 8) +
        (Expr.size (.const 0) + Expr.size (.reg 18) + 5)) := by
    refine Triple.forRange_const innerC 0 wLen (Nat.zero_le _) h1_lt (fun _ => hwLenB)
      (fun s hI => ⟨by simp [Expr.eval, h0_lt], by
        rcases hI with ⟨r0, r5, r6, r7, r8, r9, r10, rle, r14, r15, r17, r18, r19,
          hmL1, hmV0, hmL, hpv, hpe, hfr⟩
        exact ⟨by simpa [Function.update_of_ne] using r0,
          by simpa [Function.update_of_ne] using r5,
          by simpa [Function.update_of_ne] using r6,
          by simpa [Function.update_of_ne] using r7,
          by simpa [Function.update_of_ne] using r8,
          by simpa [Function.update_of_ne] using r9,
          by simpa [Function.update_of_ne] using r10,
          fun r hr => by simpa [Function.update_of_ne (by omega : r ≠ 20)] using rle r hr,
          by simpa [Function.update_of_ne] using r14,
          by simpa [Function.update_of_ne] using r15,
          by simpa [Function.update_of_ne] using r17,
          by simpa [Function.update_of_ne] using r18,
          by simpa [Function.update_of_ne] using r19,
          by simp, hmL1, hmV0, hmL, hpv, hpe, hfr⟩⟩)
      (fun t s _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      (fun t s _ _ hI => by simp [Expr.eval, hI.2.2.2.2.2.2.2.2.2.2.2.1]) ?_
    intro t _ ht_lt s ω' ⟨ir0, ir5, ir6, ir7, ir8, ir9, ir10, irle, ir14, ir15, ir17, ir18, ir19,
      ir20, ihmL1, ihmV0, ihmL, ihpv, ihpe, ihfr⟩
    set stp := (emb e)[t]'ht_lt
    have hstp_bang : (emb e)[t]! = stp := by
      dsimp only [stp]
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ht_lt, Option.getD_some]
    have ht_ltw : t < 2 ^ w := by omega
    have h12t_lt : 1 + 2 * t < 2 ^ w := by omega
    have h22t_lt : 2 + 2 * t < 2 ^ w := by omega
    have hw12t_lt : wPtr + (1 + 2 * t) < 2 ^ w := by
      have : (mWalkEncode (emb e)).length = 1 + 2 * wLen := mWalkEncode_length (emb e)
      omega
    have hw22t_lt : wPtr + (2 + 2 * t) < 2 ^ w := by
      have : (mWalkEncode (emb e)).length = 1 + 2 * wLen := mWalkEncode_length (emb e)
      omega
    have h2t_lt : 2 + t < 2 ^ w := by omega
    have h3wt_lt : 3 + wLen + t < 2 ^ w := by omega
    have haVert_lt : wPtrOut + (2 + t) < 2 ^ w := by omega
    have haEdge_lt : wPtrOut + (3 + wLen + t) < 2 ^ w := by omega
    have hStepProps := walkStep_in_usedH hemb heJ ht_lt
    have hEdgeInH : stp.1 ∈ H'.E := hStepProps.1
    have hEdgeUsed : stp.1 ∈ usedHEdges J emb := hStepProps.2.1
    have hDstUsed : H'.dst stp ∈ usedHVerts H' J emb := hStepProps.2.2
    have hEdgeInList : stp.1 ∈ hEs := by rwa [hhE, mem_vertsOf]
    have hEdge_ltw : stp.1 < 2 ^ w := hhew _ hEdgeInList
    have hDstInList : H'.dst stp ∈ jVs ++ exVs := usedHVerts_mem_jVs_or_exVs hjV hexV hDstUsed
    have hDst_ltw : H'.dst stp < 2 ^ w := by
      rcases List.mem_append.mp hDstInList with h | h
      · exact hjw _ h
      · exact hexw _ h
    have hm_edge : s.mem (wPtr + (1 + 2 * t)) = stp.1 := by
      have hk : 1 + 2 * t < (mWalkEncode (emb e)).length := by
        rw [mWalkEncode_length]; omega
      rw [ihfr _ (by rcases hdisjW _ hk with h | h <;> [left; right] <;> omega)]
      simpa [Nat.add_assoc] using MWalkAt_step_edge hmw ht_lt
    have hm_dir : s.mem (wPtr + (2 + 2 * t)) = if stp.2 then 1 else 0 := by
      have hk : 2 + 2 * t < (mWalkEncode (emb e)).length := by
        rw [mWalkEncode_length]; omega
      rw [ihfr _ (by rcases hdisjW _ hk with h | h <;> [left; right] <;> omega)]
      have hdir := MWalkAt_step_dir hmw ht_lt
      rw [show wPtr + 1 + 2 * t + 1 = wPtr + (2 + 2 * t) by omega] at hdir
      exact hdir
    have hDyn_cur : DynGraphAt s.mem hPtr vCap eCap H' := by
      refine hDynH.of_agree ?_
      intro k hk1 hk2
      rw [ihfr _ (by rcases hdisjH (k - hPtr) (by omega) with h | h <;> [left; right] <;> omega)]
    have hjAt_cur : ListAt s.mem jVsPtr jVs := fun u hu => by
      rw [ihfr _ (by rcases hdisjV u hu with h | h <;> [left; right] <;> omega)]
      exact hjAt u hu
    have hexAt_cur : ListAt s.mem exVsPtr exVs := fun u hu => by
      rw [ihfr _ (by rcases hdisjEx u hu with h | h <;> [left; right] <;> omega)]
      exact hexAt u hu
    have hhEAt_cur : ListAt s.mem hEsPtr hEs := fun u hu => by
      rw [ihfr _ (by rcases hdisjHE u hu with h | h <;> [left; right] <;> omega)]
      exact hhEAt u hu
    refine runs_start_le ?_
    dsimp only [bodyIn]
    -- Inner step 1: assign 21 := stp.1
    refine runs_seq_assign_le
      (Expr.eval_load_of_eq (v := stp.1)
        (by simp [Expr.eval, BinOp.eval, ir17, ir20, h1_lt, h2_lt, hw12t_lt,
          show 2 * t < 2 ^ w by omega, h12t_lt])
        hm_edge) ?_
    -- Inner step 2: assign 22 := (if stp.2 then 1 else 0)
    refine runs_seq_assign_le
      (Expr.eval_load_of_eq (v := if stp.2 then 1 else 0)
        (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, ir17, ir20, h2_lt, hw22t_lt,
          show 2 * t < 2 ^ w by omega, h22t_lt])
        hm_dir) ?_
    -- Inner step 3: cond on dir, calling getHead or getTail into reg 23
    have hwe : ∀ v ∈ [hPtr, stp.1], v < 2 ^ w := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_hP
      rcases List.mem_cons.mp hv with rfl | hv; · exact hEdge_ltw
      cases hv
    have hcont_dir :
        ∀ (v23 memD posD) (kCond : ℕ),
          v23 = H'.dst stp →
          memD = s.mem →
          kCond + (1 + 2 * 7 + (90 * Llog + 86) + 7 + (45 * Llog + 24) + 9 + 1) ≤ innerC →
          ∃ o₂ st₂ c₂,
            Runs w p ω'
              (.call 24 (bGT + gtIdxLookupHVert) [.reg 5, .reg 6, .reg 7, .reg 8, .reg 23] ;;
               .store (.bin .add (.reg 19) (.bin .add (.const 2) (.reg 20))) (.reg 24) ;;
               .call 24 (bSort + sortIdxBinSearch) [.reg 9, .reg 10, .reg 21] ;;
               .store (.bin .add (.reg 19) (.bin .add (.bin .add (.const 3) (.reg 18)) (.reg 20))) (.reg 24))
              { mem := memD
                regs := Function.update
                  (Function.update (Function.update s.regs 21 stp.1) 22 (if stp.2 then 1 else 0))
                  23 v23
                pos := posD } o₂ st₂ c₂ ∧
            normalPost
              (fun st₁ =>
                InvIn (t + 1) (State.mk st₁.mem (Function.update st₁.regs 20 (t + 1)) st₁.pos) ∧
                st₁.regs 20 = t)
              o₂ st₂ ∧
            kCond + c₂ ≤ innerC := by
      intro v23 memD posD kCond hv23 hmemD hkCond
      subst hmemD
      have hwtV : ∀ v ∈ [jVsPtr, jVs.length, exVsPtr, exVs.length, v23], v < 2 ^ w := by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_jP
        rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_nJ
        rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_exP
        rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_nEx
        rcases List.mem_cons.mp hv with rfl | hv; · exact hv23 ▸ hDst_ltw
        cases hv
      have hpreLT : (gtLookupHVertContract w jVs exVs v23).pre
          [jVsPtr, jVs.length, exVsPtr, exVs.length, v23] s.mem :=
        ⟨jVsPtr, exVsPtr, rfl, hw16, hjVB, hexB, hv23 ▸ hDst_ltw, hnHB,
         hjVPair, hexPair, hdisj_vex, hv23 ▸ hDstInList, hjAt_cur, hexAt_cur, hjw, hexw⟩
      refine runs_seq_call_le (gtLookupHVert_meetsContract hpGT hpSort)
        (by simp [evalArgs, Expr.eval, Function.update_of_ne, Function.update_self,
          ir5, ir6, ir7, ir8])
        hwtV hpreLT ?_
      rintro idxV memV _ ⟨_, _, _, hmemV, hidxV, hidxV_lt⟩
      subst hmemV
      have hidxV_ltw : idxV < 2 ^ w := by omega
      -- Store vertex index at wPtrOut + (2 + t)
      refine runs_seq_store_le (x := wPtrOut + (2 + t)) (v := idxV)
        (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, ir19, ir20, h2_lt, h2t_lt,
          haVert_lt])
        (by simp [Expr.eval, Function.update_self]) ?_
      set memS1 := Function.update s.mem (wPtrOut + (2 + t)) idxV
      have hhEAt_s1 : ListAt memS1 hEsPtr hEs := fun u hu => by
        have hne : hEsPtr + u ≠ wPtrOut + (2 + t) := by
          rcases hdisjHE u hu with h | h <;> omega
        dsimp only [memS1]; rw [Function.update_of_ne hne]; exact hhEAt_cur u hu
      have hweB : ∀ v ∈ [hEsPtr, hEs.length, stp.1], v < 2 ^ w := by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_hEP
        rcases List.mem_cons.mp hv with rfl | hv; · exact hlt_mH
        rcases List.mem_cons.mp hv with rfl | hv; · exact hEdge_ltw
        cases hv
      have hpreB : (binSearchContract w hEs stp.1).pre [hEsPtr, hEs.length, stp.1] memS1 :=
        ⟨hEsPtr, rfl, hw16, hhEB, hhEPair, hEdgeInList, hhEAt_s1, hhew⟩
      refine runs_seq_call_le (binSearch_meetsContract hpSort)
        (by simp [evalArgs, Expr.eval, Function.update_of_ne, Function.update_self, ir9, ir10])
        hweB hpreB ?_
      rintro idxE memE _ ⟨_, _, hmemE, hidxE, hidxE_lt⟩
      subst hmemE
      have hidxE_ltw : idxE < 2 ^ w := by omega
      refine runs_store_le (x := wPtrOut + (3 + wLen + t)) (v := idxE)
        (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, ir19, ir18, ir20, h3_lt,
          h3wLen_lt, h3wt_lt, haEdge_lt])
        (by simp [Expr.eval, Function.update_self]) ?_
        (by
          have hmul1 := Nat.mul_le_mul_left 90 hlogHV
          have hmul2 := Nat.mul_le_mul_left 45 hlogHE
          dsimp only [gtLookupHVertContract, binSearchContract, argsSize, Expr.size, innerC,
            Llog] at hmul1 hmul2 hkCond ⊢
          omega)
      have hpv_succ : pv (t + 1) = pv t ++ [idxV] := by
        dsimp only [pv]
        rw [List.range_succ, List.map_append, List.map_singleton, hstp_bang, ← hv23, hidxV]
      have hpe_succ : pe (t + 1) = pe t ++ [idxE] := by
        dsimp only [pe]
        rw [List.range_succ, List.map_append, List.map_singleton, hstp_bang, hidxE]
      refine ⟨⟨by simp [Function.update_of_ne, ir0], by simp [Function.update_of_ne, ir5],
        by simp [Function.update_of_ne, ir6], by simp [Function.update_of_ne, ir7],
        by simp [Function.update_of_ne, ir8], by simp [Function.update_of_ne, ir9],
        by simp [Function.update_of_ne, ir10],
        fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 20),
          Function.update_of_ne (by omega : r ≠ 24),
          Function.update_of_ne (by omega : r ≠ 23), Function.update_of_ne (by omega : r ≠ 22),
          Function.update_of_ne (by omega : r ≠ 21), irle r hr],
        by simp [Function.update_of_ne, ir14], by simp [Function.update_of_ne, ir15],
        by simp [Function.update_of_ne, ir17], by simp [Function.update_of_ne, ir18],
        by simp [Function.update_of_ne, ir19], by simp [Function.update_self],
        ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp [Function.update_of_ne, ir20]⟩
      · dsimp only [memS1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), ihmL1]
      · dsimp only [memS1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), ihmV0]
      · dsimp only [memS1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), ihmL]
      · rw [hpv_succ]
        have h1 : ListAt memS1 (wPtrOut + 2) (pv t) :=
          ListAt.update_ge ihpv (by rw [hpv_len]; omega)
        have h2 : ListAt (Function.update memS1 (wPtrOut + (3 + wLen + t)) idxE)
            (wPtrOut + 2) (pv t) :=
          ListAt.update_ge h1 (by rw [hpv_len]; omega)
        refine listAt_append.mpr ⟨h2, fun u hu => ?_⟩
        simp only [List.length_cons, List.length_nil] at hu
        have hu0 : u = 0 := by omega
        subst hu0
        rw [hpv_len]
        dsimp only [memS1]
        rw [Nat.add_zero, Function.update_of_ne (by omega),
          show wPtrOut + 2 + t = wPtrOut + (2 + t) by omega, Function.update_self]
        rfl
      · rw [hpe_succ]
        have h1 : ListAt memS1 (wPtrOut + (3 + wLen)) (pe t) :=
          listAt_update_lt ihpe (by omega)
        have h2 : ListAt (Function.update memS1 (wPtrOut + (3 + wLen + t)) idxE)
            (wPtrOut + (3 + wLen)) (pe t) :=
          ListAt.update_ge h1 (by rw [hpe_len]; omega)
        refine listAt_append.mpr ⟨h2, fun u hu => ?_⟩
        simp only [List.length_cons, List.length_nil] at hu
        have hu0 : u = 0 := by omega
        subst hu0
        rw [hpe_len]
        dsimp only [memS1]
        rw [Nat.add_zero,
          show wPtrOut + (3 + wLen) + t = wPtrOut + (3 + wLen + t) by omega, Function.update_self]
        rfl
      · intro addr had
        dsimp only [memS1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact ihfr addr had
    -- Dispatch on stp.2
    by_cases hdir : stp.2 = true
    · refine runs_seq_cond_true_le (v := 1)
        (by simp [Expr.eval, BinOp.eval, Function.update_self, hdir, h1_lt]) (by decide) ?_
      have hpreH : (dgGetHeadContract w vCap eCap H').pre [hPtr, stp.1] s.mem :=
        ⟨hPtr, stp.1, rfl, hw16, hhB, hEdgeInH, hDyn_cur⟩
      have hcallH := runs_call_of_meetsContract
        (args := [.reg 0, .reg 21]) (vs := [hPtr, stp.1]) (r := 23)
        (st := State.mk s.mem
          (Function.update (Function.update s.regs 21 stp.1) 22 (if stp.2 then 1 else 0))
          s.pos)
        (dgGetHead_meetsContract hpOps)
        (by
          have h0_s : (Function.update (Function.update s.regs 21 stp.1)
              22 (if stp.2 then 1 else 0)) 0 = hPtr := by
            simp [Function.update_of_ne, ir0]
          have h21_s : (Function.update (Function.update s.regs 21 stp.1)
              22 (if stp.2 then 1 else 0)) 21 = stp.1 := by
            simp [Function.update_of_ne, Function.update_self]
          eval_expr)
        hwe hpreH ω'
      rcases hcallH with ⟨st1, c1, v23, hrun1, hpost1, hr23, hother1, hc1⟩
      rcases hpost1 with ⟨_, _, heq1, hmem1, hv23⟩
      simp only [List.cons.injEq, and_true] at heq1
      have hv23_dst : v23 = H'.dst stp := by
        rw [← heq1.2] at hv23
        simp [MGraph.dst, hdir, hv23]
      have hst1_eq : st1 = State.mk st1.mem
          (Function.update
            (Function.update (Function.update s.regs 21 stp.1) 22 (if stp.2 then 1 else 0))
            23 v23)
          st1.pos := by
        cases st1
        simp only [State.mk.injEq, true_and, and_true]
        funext r'
        by_cases hr' : r' = 23
        · subst hr'; exact hr23
        · simpa [Function.update_of_ne hr'] using hother1 r' hr'
      have hrem := hcont_dir v23 st1.mem st1.pos (0 + 8 + 2 + 8 + 2 + 3 + c1 + 2) hv23_dst hmem1
        (by dsimp only [dgGetHeadContract, argsSize, Expr.size, innerC] at hc1 ⊢; omega)
      rcases hrem with ⟨o₂, st₂, c₂, hrun₂, hpost₂, hc₂⟩
      rw [← hst1_eq] at hrun₂
      exact ⟨.normal, st1, c1, hrun1, ⟨o₂, st₂, c₂, hrun₂, hpost₂,
        by dsimp only [Expr.size] at hc₂ ⊢; omega⟩⟩
    · have hdirF : stp.2 = false := Bool.eq_false_iff.mpr hdir
      refine runs_seq_cond_false_le
        (by simp [Expr.eval, BinOp.eval, Function.update_self, hdirF, h1_lt]) ?_
      have hpreT : (dgGetTailContract w vCap eCap H').pre [hPtr, stp.1] s.mem :=
        ⟨hPtr, stp.1, rfl, hw16, hhB, hEdgeInH, hDyn_cur⟩
      have hcallT := runs_call_of_meetsContract
        (args := [.reg 0, .reg 21]) (vs := [hPtr, stp.1]) (r := 23)
        (st := State.mk s.mem
          (Function.update (Function.update s.regs 21 stp.1) 22 (if stp.2 then 1 else 0))
          s.pos)
        (dgGetTail_meetsContract hpOps)
        (by
          have h0_s : (Function.update (Function.update s.regs 21 stp.1)
              22 (if stp.2 then 1 else 0)) 0 = hPtr := by
            simp [Function.update_of_ne, ir0]
          have h21_s : (Function.update (Function.update s.regs 21 stp.1)
              22 (if stp.2 then 1 else 0)) 21 = stp.1 := by
            simp [Function.update_of_ne, Function.update_self]
          eval_expr)
        hwe hpreT ω'
      rcases hcallT with ⟨st1, c1, v23, hrun1, hpost1, hr23, hother1, hc1⟩
      rcases hpost1 with ⟨_, _, heq1, hmem1, hv23⟩
      simp only [List.cons.injEq, and_true] at heq1
      have hv23_dst : v23 = H'.dst stp := by
        rw [← heq1.2] at hv23
        simp [MGraph.dst, hdirF, hv23]
      have hst1_eq : st1 = State.mk st1.mem
          (Function.update
            (Function.update (Function.update s.regs 21 stp.1) 22 (if stp.2 then 1 else 0))
            23 v23)
          st1.pos := by
        cases st1
        simp only [State.mk.injEq, true_and, and_true]
        funext r'
        by_cases hr' : r' = 23
        · subst hr'; exact hr23
        · simpa [Function.update_of_ne hr'] using hother1 r' hr'
      have hrem := hcont_dir v23 st1.mem st1.pos (0 + 8 + 2 + 8 + 2 + 3 + c1 + 2) hv23_dst hmem1
        (by dsimp only [dgGetTailContract, argsSize, Expr.size, innerC] at hc1 ⊢; omega)
      rcases hrem with ⟨o₂, st₂, c₂, hrun₂, hpost₂, hc₂⟩
      rw [← hst1_eq] at hrun₂
      exact ⟨.normal, st1, c1, hrun1, ⟨o₂, st₂, c₂, hrun₂, hpost₂,
        by dsimp only [Expr.size] at hc₂ ⊢; omega⟩⟩
  -- Supply InvInPre for the state after step 6
  refine runs_seq_triple_le hloop
    ⟨by simp [Function.update_of_ne, hr0],
     by simp [Function.update_of_ne, hr5],
     by simp [Function.update_of_ne, hr6],
     by simp [Function.update_of_ne, hr7],
     by simp [Function.update_of_ne, hr8],
     by simp [Function.update_of_ne, hr9],
     by simp [Function.update_of_ne, hr10],
     fun r hr => by
       simp only [Function.update_of_ne (by omega : r ≠ 21),
         Function.update_of_ne (by omega : r ≠ 20),
         Function.update_of_ne (by omega : r ≠ 19)],
     by simp [Function.update_of_ne, hr14],
     by simp [Function.update_of_ne, hr15],
     by simp [Function.update_of_ne, hr17],
     by simp [Function.update_of_ne, hr18, wLen],
     by simp [Function.update_of_ne],
     by dsimp only [mem0, mem2]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_self],
     by dsimp only [mem0]; exact Function.update_self _ _ _,
     by dsimp only [mem0, mem2]; rw [Function.update_of_ne (by omega), Function.update_self],
     by simp [pv, listAt_nil],
     by simp [pe, listAt_nil],
     fun addr had => by
       dsimp only [mem0, mem2]
       rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
         Function.update_of_ne (by omega), hmemEq]⟩ ?_
  intro st' ⟨_, _, _, _, _, _, _, rle', r14', r15', _, r18', _, _, hmL1', hmV0', hmL', hpv', hpe', hfr'⟩
  have he_getD' : (vertsOf J.E).getD j 0 = e := by
    rw [← hjE, List.getD_eq_getElem _ _ hj_lt, ← he_eq]
  have hhVs : hVerts H' J emb = jVs ++ exVs := by simp [hVerts, hjV, hexV]
  have hhEs : hEdges J emb = hEs := by simp [hEdges, hhE]
  -- Step 7: final assign 14 := curLen + (2 * wLen + 3)
  refine runs_assign_le (v := curLen + (2 * wLen + 3))
    (by simp [Expr.eval, BinOp.eval, r14', r18', h2_lt, h3_lt, h2mulw_lt, h2w3_lt, wLen,
      show curLen + (2 * wLen + 3) < 2 ^ w by omega])
    ⟨rfl,
     fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 14), rle' r hr],
     by simp [wLen],
     by simp [Function.update_of_ne, r15'],
     ?_, hfr'⟩ ?_
  · have hEnc : Walk.encode (embToCited H' J emb j) =
        (wLen + 1) :: idx0 :: (pv wLen ++ wLen :: pe wLen) := by
      dsimp only [embToCited]
      rw [he_getD', walkToCited_nonempty_encode _ _ _ _ _ hP_ne, hhVs, hhEs, ← hidx0]
      simp [wLen, pv, pe, List.cons_append]
    change ListAt st'.mem wPtrOut (Walk.encode (embToCited H' J emb j))
    rw [hEnc, listAt_cons, listAt_cons]
    have hmL'' : st'.mem (wPtrOut + 2 + (pv wLen).length) = wLen := by
      rw [hpv_len, show wPtrOut + 2 + wLen = wPtrOut + (2 + wLen) by omega]
      exact hmL'
    have hpe'' : ListAt st'.mem (wPtrOut + 2 + (pv wLen).length + 1) (pe wLen) := by
      rw [hpv_len, show wPtrOut + 2 + wLen + 1 = wPtrOut + (3 + wLen) by omega]
      exact hpe'
    exact ⟨hmL1', hmV0', listAt_append.mpr ⟨hpv', listAt_cons.mpr ⟨hmL'', hpe''⟩⟩⟩
  · have hmul : wLen * (innerC + 1 + 8) =
        135 * wLen * Llog + 225 * wLen := by
      dsimp only [innerC]; ring
    dsimp only [gtLookupHVertContract, argsSize, Expr.size]
    rw [hmul]
    dsimp only [wLen, Llog] at hbound ⊢
    omega


end

end MinCostFlow.DynSpanner.Program
