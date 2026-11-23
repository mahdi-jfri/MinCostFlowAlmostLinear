module

public import MinCostFlow.DynSpanner.Program.GraphTranslateEmit
import MinCostFlow.DynSpanner.Program.GraphTranslateEmitBranch

/-!
# Graph Translation: Walk Embedding Emitter Verification

Proof of `gtEmitEmbToCited_meetsContract` (`gtIdxEmitEmbToCited = 2`), verifying that
`gtEmitEmbToCitedStmt` emits `canonWalkOffsets` and flattened `Walk.encode` arrays for
`embToCited H' J emb` in time `O((rawEs.length + mJ) * (log(|V_H'| + |E_H'|) + 1))`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner

public section

theorem gtEmitEmbToCited_meetsContract {w vCap eCap : ℕ} {p : Program} {b bSort bOps bGT : ℕ}
    {H' J : MGraph} {emb : MinCostFlow.Embedding} {jVs exVs jEs jTails hEs : List ℕ}
    (hp : p.HasAt b (gtEmitProcs bSort bOps bGT))
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hpGT : p.HasAt bGT (gtProcs bSort bOps))
    (hpSort : p.HasAt bSort (sortProcs bSort)) :
    MeetsContract w p (b + gtIdxEmitEmbToCited)
      (gtEmitEmbToCitedContract w vCap eCap H' J emb jVs exVs jEs jTails hEs) := by
  refine meetsContract_of_runs
    (hp.get (i := gtIdxEmitEmbToCited) (by simp [gtEmitProcs, gtIdxEmitEmbToCited]))
    fun args mem pos _ hargs hpre => ?_
  rcases hpre with ⟨hPtr, jEsPtr, jTailsPtr, mEmbPtr, jVsPtr, exVsPtr, hEsPtr, ptrsOut, dataOut,
    offBase, rfl, hw16, hhB, hjEB, hjTB, hmEB, hjVB, hexB, hhEB, hptrsB, hdataB, hoffB, hnHB,
    hptrData, hdisjH, hdisjJE, hdisjJT, hdisjME, hdisjW, hdisjV, hdisjEx, hdisjHE,
    hDynH, hJ, hemb, hjV, hexV, hjE, hhE, hLenT, hTH, hmEmb, hjEAt, hjTAt, hjAt, hexAt, hhEAt,
    hjw, hexw, hhew, hwLens⟩
  let cWalks := (List.range jEs.length).map (embToCited H' J emb)
  let dataLen := (cWalks.flatMap Walk.encode).length
  let Llog := Nat.log 2 (jVs.length + exVs.length + hEs.length + 2) + 1
  have hdataB' : dataOut + dataLen < 2 ^ w := hdataB
  have hoffB' : offBase + dataLen < 2 ^ w := hoffB
  have hptrData' : ptrsOut + jEs.length ≤ dataOut ∨ dataOut + dataLen ≤ ptrsOut := hptrData
  have hlt_hP : hPtr < 2 ^ w := hargs hPtr (by simp)
  have hlt_mJ : jEs.length < 2 ^ w := hargs jEs.length (by simp)
  have hlt_jEP : jEsPtr < 2 ^ w := hargs jEsPtr (by simp)
  have hlt_jTP : jTailsPtr < 2 ^ w := hargs jTailsPtr (by simp)
  have hlt_mEP : mEmbPtr < 2 ^ w := hargs mEmbPtr (by simp)
  have hlt_jP : jVsPtr < 2 ^ w := hargs jVsPtr (by simp)
  have hlt_nJ : jVs.length < 2 ^ w := hargs jVs.length (by simp)
  have hlt_exP : exVsPtr < 2 ^ w := hargs exVsPtr (by simp)
  have hlt_nEx : exVs.length < 2 ^ w := hargs exVs.length (by simp)
  have hlt_hEP : hEsPtr < 2 ^ w := hargs hEsPtr (by simp)
  have hlt_mH : hEs.length < 2 ^ w := hargs hEs.length (by simp)
  have hlt_pO : ptrsOut < 2 ^ w := hargs ptrsOut (by simp)
  have hlt_dO : dataOut < 2 ^ w := hargs dataOut (by simp)
  have hlt_oB : offBase < 2 ^ w := hargs offBase (by simp)
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  have h3_lt : (3 : ℕ) < 2 ^ w := by omega
  have hjVPair : jVs.Pairwise (· < ·) := hjV ▸ vertsOf_pairwise_lt J.V
  have hexPair : exVs.Pairwise (· < ·) := hexV ▸ vertsOf_pairwise_lt (usedHVerts H' J emb \ J.V)
  have hhEPair : hEs.Pairwise (· < ·) := hhE ▸ vertsOf_pairwise_lt (usedHEdges J emb)
  have hdisj_vex : ∀ x ∈ jVs, x ∉ exVs := by
    intro x hx1 hx2
    rw [hjV, mem_vertsOf] at hx1
    rw [hexV, mem_vertsOf] at hx2
    exact (Finset.mem_sdiff.mp hx2).2 hx1
  let prefW : ℕ → List ℕ := fun k => ((List.range k).map (embToCited H' J emb)).flatMap Walk.encode
  let prefPtrs : ℕ → List ℕ := fun k => (List.range k).map fun t => offBase + (prefW t).length
  have hprefW_succ : ∀ k, prefW (k + 1) = prefW k ++ Walk.encode (embToCited H' J emb k) := by
    intro k
    simp [prefW, List.range_succ, List.map_append, List.flatMap_append]
  have hprefPtrs_succ : ∀ k, prefPtrs (k + 1) = prefPtrs k ++ [offBase + (prefW k).length] := by
    intro k
    simp [prefPtrs, List.range_succ, List.map_append]
  have hprefW_mono : ∀ k₁ k₂, k₁ ≤ k₂ → (prefW k₁).length ≤ (prefW k₂).length := by
    intro k₁ k₂ hk
    induction hk with
    | refl => exact le_rfl
    | step _ ih => rw [hprefW_succ, List.length_append]; omega
  have hprefW_end : prefW jEs.length = cWalks.flatMap Walk.encode := rfl
  have hprefPtrs_end : prefPtrs jEs.length = canonWalkOffsets offBase cWalks := by
    refine List.ext_getElem (by simp [prefPtrs, cWalks, canonWalkOffsets_length]) fun t ht1 ht2 => ?_
    simp only [prefPtrs, canonWalkOffsets_length, cWalks, List.length_map, List.length_range] at ht1 ht2
    rw [List.getElem_map, List.getElem_range, canonWalkOffsets_getElem (hj := by
      simp [cWalks]; exact ht1)]
    congr 1
    have htake : cWalks.take t = (List.range t).map (embToCited H' J emb) := by
      refine List.ext_getElem (by simp [cWalks, Nat.le_of_lt ht1]) fun u hu1 hu2 => by
        simp [cWalks]
    simp only [prefW, htake]
  refine runs_start_le ?_
  dsimp only [gtEmitProcs, gtIdxEmitEmbToCited, List.getElem_cons_succ, List.getElem_cons_zero,
    gtEmitEmbToCitedStmt]
  -- Initial assign 14 := 0
  refine runs_seq_assign_le (v := 0) (by simp [Expr.eval, h0_lt]) ?_
  let bodyOut : Stmt :=
    .store (.bin .add (.reg 11) (.reg 15)) (.bin .add (.reg 13) (.reg 14)) ;;
    .assign 16 (.load (.bin .add (.reg 2) (.reg 15))) ;;
    .assign 17 (.load (.bin .add (.reg 4) (.reg 16))) ;;
    .assign 18 (.load (.reg 17)) ;;
    .cond (.bin .eq (.reg 18) (.const 0))
      (.store (.bin .add (.reg 12) (.reg 14)) (.const 0) ;;
       .store (.bin .add (.reg 12) (.bin .add (.reg 14) (.const 1))) (.const 0) ;;
       .assign 14 (.bin .add (.reg 14) (.const 2)))
      (.assign 19 (.bin .add (.reg 12) (.reg 14)) ;;
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
       .assign 14 (.bin .add (.reg 14) (.bin .add (.bin .mul (.const 2) (.reg 18)) (.const 3))))
  let InvOutPre : State → Prop := fun s =>
    s.regs 0 = hPtr ∧ s.regs 1 = jEs.length ∧ s.regs 2 = jEsPtr ∧
    s.regs 3 = jTailsPtr ∧ s.regs 4 = mEmbPtr ∧ s.regs 5 = jVsPtr ∧
    s.regs 6 = jVs.length ∧ s.regs 7 = exVsPtr ∧ s.regs 8 = exVs.length ∧
    s.regs 9 = hEsPtr ∧ s.regs 10 = hEs.length ∧ s.regs 11 = ptrsOut ∧
    s.regs 12 = dataOut ∧ s.regs 13 = offBase ∧
    s.regs 14 = (prefW 0).length ∧
    ListAt s.mem ptrsOut (prefPtrs 0) ∧
    ListAt s.mem dataOut (prefW 0) ∧
    ∀ addr, (addr < ptrsOut ∨ ptrsOut ≤ addr) → (addr < dataOut ∨ dataOut + (prefW 0).length ≤ addr) →
      s.mem addr = mem addr
  let InvOut : ℕ → State → Prop := fun k s =>
    s.regs 0 = hPtr ∧ s.regs 1 = jEs.length ∧ s.regs 2 = jEsPtr ∧
    s.regs 3 = jTailsPtr ∧ s.regs 4 = mEmbPtr ∧ s.regs 5 = jVsPtr ∧
    s.regs 6 = jVs.length ∧ s.regs 7 = exVsPtr ∧ s.regs 8 = exVs.length ∧
    s.regs 9 = hEsPtr ∧ s.regs 10 = hEs.length ∧ s.regs 11 = ptrsOut ∧
    s.regs 12 = dataOut ∧ s.regs 13 = offBase ∧
    s.regs 14 = (prefW k).length ∧ s.regs 15 = k ∧
    ListAt s.mem ptrsOut (prefPtrs k) ∧
    ListAt s.mem dataOut (prefW k) ∧
    ∀ addr, (addr < ptrsOut ∨ ptrsOut + k ≤ addr) →
      (addr < dataOut ∨ dataOut + (prefW k).length ≤ addr) → s.mem addr = mem addr
  let stepCost : ℕ → ℕ := fun k =>
    230 * ((emb (jEs.getD k 0)).length + 1) * Llog + 350 * ((emb (jEs.getD k 0)).length + 1)
  have hloopOut : Triple w p InvOutPre (forRange 15 (.const 0) (.reg 1) bodyOut)
      (normalPost (InvOut jEs.length))
      (fun _ => rangeCost stepCost 0 jEs.length + (jEs.length - 0) * (Expr.size (.reg 1) + 8) +
        (Expr.size (.const 0) + Expr.size (.reg 1) + 5)) := by
    refine Triple.forRange_le stepCost 0 jEs.length (Nat.zero_le _) h1_lt (fun _ => hlt_mJ)
      (fun s hI => ⟨by simp [Expr.eval, h0_lt], by
        rcases hI with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14,
          hp, hd, hfr⟩
        exact ⟨by simpa [Function.update_of_ne] using r0, by simpa [Function.update_of_ne] using r1,
          by simpa [Function.update_of_ne] using r2, by simpa [Function.update_of_ne] using r3,
          by simpa [Function.update_of_ne] using r4, by simpa [Function.update_of_ne] using r5,
          by simpa [Function.update_of_ne] using r6, by simpa [Function.update_of_ne] using r7,
          by simpa [Function.update_of_ne] using r8, by simpa [Function.update_of_ne] using r9,
          by simpa [Function.update_of_ne] using r10, by simpa [Function.update_of_ne] using r11,
          by simpa [Function.update_of_ne] using r12, by simpa [Function.update_of_ne] using r13,
          by simpa [Function.update_of_ne] using r14, by simp, hp, hd, by simpa using hfr⟩⟩)
      (fun k s _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      (fun k s _ _ hI => by simp [Expr.eval, hI.2.1]) ?_
    intro j _ hj_lt s ω' ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15,
      hptrs, hdata, hfr⟩
    set e := jEs[j]'hj_lt
    have heJ : e ∈ J.E := by
      have hm : e ∈ vertsOf J.E := hjE ▸ List.getElem_mem hj_lt
      rwa [mem_vertsOf] at hm
    have he_getD : jEs.getD j 0 = e := List.getD_eq_getElem _ _ hj_lt
    have he_getD' : (vertsOf J.E).getD j 0 = e := by rw [← hjE, he_getD]
    have he_ltw : e < 2 ^ w := by
      have hm := hmEB
      have := (hmEmb e heJ).1
      omega
    have hm_j : (prefW j).length ≤ dataLen := hprefW_mono j jEs.length (Nat.le_of_lt hj_lt)
    have hm_j1 : (prefW (j + 1)).length ≤ dataLen := hprefW_mono (j + 1) jEs.length hj_lt
    have hj_ltw : j < 2 ^ w := by omega
    have hcur_ltw : (prefW j).length < 2 ^ w := by omega
    have hoffCur_ltw : offBase + (prefW j).length < 2 ^ w := by omega
    have hpOutJ_ltw : ptrsOut + j < 2 ^ w := by omega
    have hjEP_ltw : jEsPtr + j < 2 ^ w := by omega
    have hmE_ltw : mEmbPtr + e < 2 ^ w := by
      have := (hmEmb e heJ).1; omega
    have hwPtrB : mem (mEmbPtr + e) + (mWalkEncode (emb e)).length < 2 ^ w := (hwLens e heJ).2
    have hwLenB : (emb e).length < 2 ^ w := (hwLens e heJ).1
    have hwPtr_ltw : mem (mEmbPtr + e) < 2 ^ w := by
      have : (mWalkEncode (emb e)).length ≥ 1 := by simp [mWalkEncode_length]
      omega
    have hmw : MWalkAt mem (mem (mEmbPtr + e)) (emb e) := (hmEmb e heJ).2
    -- Disjointness helpers from initial memory
    have hcur_disj : ∀ addr,
        ((addr < ptrsOut ∨ ptrsOut + jEs.length ≤ addr) ∧
         (addr < dataOut ∨ dataOut + dataLen ≤ addr)) → s.mem addr = mem addr := by
      intro addr ⟨h1, h2⟩
      exact hfr addr (by rcases h1 with h | h <;> [left; right] <;> omega)
        (by rcases h2 with h | h <;> [left; right] <;> omega)
    have hm_e : s.mem (jEsPtr + j) = e := by
      rw [hcur_disj _ (hdisjJE j hj_lt), hjEAt j hj_lt]
    have hm_wPtr : s.mem (mEmbPtr + e) = mem (mEmbPtr + e) :=
      hcur_disj _ (hdisjME e heJ)
    refine runs_start_le ?_
    dsimp only [bodyOut]
    -- 1. Store ptrsOut + j := offBase + (prefW j).length
    refine runs_seq_store_le (x := ptrsOut + j) (v := offBase + (prefW j).length)
      (by simp [Expr.eval, BinOp.eval, r11, r15, hpOutJ_ltw])
      (by simp [Expr.eval, BinOp.eval, r13, r14, hoffCur_ltw]) ?_
    set memP := Function.update s.mem (ptrsOut + j) (offBase + (prefW j).length)
    have hptrs_j1 : ListAt memP ptrsOut (prefPtrs (j + 1)) := by
      rw [hprefPtrs_succ]
      refine listAt_append.mpr ⟨ListAt.update_ge hptrs (by simp [prefPtrs]), fun u hu => ?_⟩
      simp only [List.length_cons, List.length_nil] at hu
      have hu0 : u = 0 := by omega
      subst hu0
      simp only [prefPtrs, List.length_map, List.length_range, Nat.add_zero, memP,
        Function.update_self, List.getElem_cons_zero]
    have hdata_j : ListAt memP dataOut (prefW j) := fun u hu => by
      have hne : dataOut + u ≠ ptrsOut + j := by rcases hptrData' with h | h <;> omega
      dsimp only [memP]; rw [Function.update_of_ne hne]; exact hdata u hu
    have hmemP_agree : ∀ addr,
        ((addr < ptrsOut ∨ ptrsOut + jEs.length ≤ addr) ∧
         (addr < dataOut ∨ dataOut + dataLen ≤ addr)) → memP addr = mem addr := by
      intro addr had
      dsimp only [memP]
      rw [Function.update_of_ne (by rcases had.1 with h | h <;> omega)]
      exact hcur_disj addr had
    -- 2. assign 16 := e
    have hm_eP : memP (jEsPtr + j) = e := by
      rw [hmemP_agree _ (hdisjJE j hj_lt), hjEAt j hj_lt]
    refine runs_seq_assign_le
      (Expr.eval_load_of_eq (v := e)
        (by simp [Expr.eval, BinOp.eval, r2, r15, hjEP_ltw]) hm_eP) ?_
    -- 3. assign 17 := wPtr
    have hm_wPtrP : memP (mEmbPtr + e) = mem (mEmbPtr + e) :=
      hmemP_agree _ (hdisjME e heJ)
    refine runs_seq_assign_le
      (Expr.eval_load_of_eq (v := mem (mEmbPtr + e))
        (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, Function.update_self,
          r4, hmE_ltw]) hm_wPtrP) ?_
    -- 4. assign 18 := wLen
    have hm_wLenP : memP (mem (mEmbPtr + e)) = (emb e).length := by
      have h0len : 0 < (mWalkEncode (emb e)).length := by simp [mWalkEncode_length]
      have hd := hdisjW e heJ 0 h0len
      simp only [Nat.add_zero] at hd
      rw [hmemP_agree _ hd]
      exact MWalkAt_head hmw
    refine runs_seq_assign_le
      (Expr.eval_load_of_eq (v := (emb e).length)
        (by simp [Expr.eval, Function.update_self]) hm_wLenP) ?_
    -- 5. Cond on wLen = 0
    by_cases hwZero : (emb e).length = 0
    · have hP_nil : emb e = [] := List.length_eq_zero_iff.mp hwZero
      have hwEnc_nil : Walk.encode (embToCited H' J emb j) = [0, 0] := by
        dsimp only [embToCited]
        rw [he_getD', hP_nil, walkToCited_empty_encode]
      have hlen_j1 : (prefW (j + 1)).length = (prefW j).length + 2 := by
        rw [hprefW_succ, List.length_append, hwEnc_nil]; simp
      have hdO1_ltw : dataOut + (prefW j).length < 2 ^ w := by omega
      have hdO2_ltw : dataOut + ((prefW j).length + 1) < 2 ^ w := by omega
      refine runs_cond_true_le (v := 1)
        (by simp [Expr.eval, BinOp.eval, Function.update_self, hwZero, h1_lt]) (by decide) ?_
      refine runs_seq_store_le (x := dataOut + (prefW j).length) (v := 0) ?_ ?_ ?_
      · simp [Expr.eval, BinOp.eval, r12, r14, hdO1_ltw]
      · simp [Expr.eval, h0_lt]
      refine runs_seq_store_le (x := dataOut + ((prefW j).length + 1)) (v := 0)
        (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, r12, r14, h1_lt,
          show (prefW j).length + 1 < 2 ^ w by omega, hdO2_ltw])
        (by simp [Expr.eval, h0_lt]) ?_
      refine runs_assign_le (v := (prefW j).length + 2)
        (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, r14, h2_lt,
          show (prefW j).length + 2 < 2 ^ w by omega])
        ⟨⟨by simp [Function.update_of_ne, r0], by simp [Function.update_of_ne, r1],
          by simp [Function.update_of_ne, r2], by simp [Function.update_of_ne, r3],
          by simp [Function.update_of_ne, r4], by simp [Function.update_of_ne, r5],
          by simp [Function.update_of_ne, r6], by simp [Function.update_of_ne, r7],
          by simp [Function.update_of_ne, r8], by simp [Function.update_of_ne, r9],
          by simp [Function.update_of_ne, r10], by simp [Function.update_of_ne, r11],
          by simp [Function.update_of_ne, r12], by simp [Function.update_of_ne, r13],
          by simp [Function.update_self, hlen_j1],
          by simp,
          ?_, ?_, ?_⟩, r15⟩ ?_
      · intro u hu
        have hu_lt : u < jEs.length := by
          have hpl : (prefPtrs (j + 1)).length = j + 1 := by simp [prefPtrs]
          omega
        have hne1 : ptrsOut + u ≠ dataOut + (prefW j).length := by rcases hptrData' with h | h <;> omega
        have hne2 : ptrsOut + u ≠ dataOut + ((prefW j).length + 1) := by rcases hptrData' with h | h <;> omega
        dsimp only
        rw [Function.update_of_ne hne2, Function.update_of_ne hne1]
        exact hptrs_j1 u hu
      · rw [hprefW_succ, hwEnc_nil]
        have h1 : ListAt (Function.update memP (dataOut + (prefW j).length) 0) dataOut (prefW j) :=
          ListAt.update_ge hdata_j le_rfl
        have h2 : ListAt (Function.update (Function.update memP (dataOut + (prefW j).length) 0)
            (dataOut + ((prefW j).length + 1)) 0) dataOut (prefW j) :=
          ListAt.update_ge h1 (by omega)
        refine listAt_append.mpr ⟨h2, fun u hu => ?_⟩
        simp only [List.length_cons, List.length_nil] at hu
        rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl
        · dsimp only
          rw [show dataOut + (prefW j).length + 0 = dataOut + (prefW j).length by omega,
            Function.update_of_ne (by omega), Function.update_self]
          rfl
        · dsimp only
          rw [show dataOut + (prefW j).length + 1 = dataOut + ((prefW j).length + 1) by omega,
            Function.update_self]
          rfl
      · intro addr hp1 hp2
        dsimp only [memP]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by rcases hp1 with h | h <;> omega)]
        exact hfr addr (by rcases hp1 with h | h <;> [left; right] <;> omega)
          (by rcases hp2 with h | h <;> [left; right] <;> omega)
      · dsimp only [stepCost, Expr.size]; rw [he_getD, hwZero]; omega
    · have hEnc_len : (Walk.encode (embToCited H' J emb j)).length = 2 * (emb e).length + 3 := by
        dsimp only [embToCited]
        rw [he_getD', walkToCited_nonempty_encode _ _ _ _ _ (fun hn => hwZero (by simp [hn]))]
        simp [List.length_cons, List.length_append]
        omega
      have hlen_j1 : (prefW (j + 1)).length = (prefW j).length + (2 * (emb e).length + 3) := by
        rw [hprefW_succ, List.length_append, hEnc_len]
      have hOutB_j : dataOut + (prefW j).length + (2 * (emb e).length + 3) < 2 ^ w := by omega
      have hDynP : DynGraphAt memP hPtr vCap eCap H' := by
        refine hDynH.of_agree ?_
        intro k hk1 hk2
        have h := hdisjH (k - hPtr) (by omega)
        rw [show hPtr + (k - hPtr) = k by omega] at h
        exact hmemP_agree k h
      have hjAtP : ListAt memP jVsPtr jVs := fun t ht => by
        rw [hmemP_agree _ (hdisjV t ht)]; exact hjAt t ht
      have hexAtP : ListAt memP exVsPtr exVs := fun t ht => by
        rw [hmemP_agree _ (hdisjEx t ht)]; exact hexAt t ht
      have hhEAtP : ListAt memP hEsPtr hEs := fun t ht => by
        rw [hmemP_agree _ (hdisjHE t ht)]; exact hhEAt t ht
      have hjTAtP : ListAt memP jTailsPtr jTails := fun t ht => by
        rw [hmemP_agree _ (hdisjJT t (hLenT ▸ ht))]; exact hjTAt t ht
      have hmwP : MWalkAt memP (mem (mEmbPtr + e)) (emb e) := by
        refine hmw.of_agree ?_
        intro k hk1 hk2
        have hd := hdisjW e heJ (k - mem (mEmbPtr + e)) (by rw [mWalkEncode_length]; omega)
        rw [show mem (mEmbPtr + e) + (k - mem (mEmbPtr + e)) = k by omega] at hd
        exact hmemP_agree k hd
      have hdisjSpan : ∀ addr,
          ((addr < ptrsOut ∨ ptrsOut + jEs.length ≤ addr) ∧
           (addr < dataOut ∨ dataOut + dataLen ≤ addr)) →
          addr < dataOut + (prefW j).length ∨
          dataOut + (prefW j).length + (2 * (emb e).length + 3) ≤ addr := by
        intro addr had
        rcases had.2 with h | h <;> [left; right] <;> omega
      refine runs_cond_false_le
        (by simp [Expr.eval, BinOp.eval, Function.update_self, hwZero, h0_lt]) ?_
      have hBr := gtEmitEmbToCited_nonemptyBranch (w := w) (p := p) (ω := ω')
        (bSort := bSort) (bOps := bOps) (bGT := bGT)
        (H' := H') (J := J) (emb := emb)
        (jVs := jVs) (exVs := exVs) (jEs := jEs) (jTails := jTails) (hEs := hEs)
        (hPtr := hPtr) (jEsPtr := jEsPtr) (jTailsPtr := jTailsPtr) (mEmbPtr := mEmbPtr)
        (jVsPtr := jVsPtr) (exVsPtr := exVsPtr) (hEsPtr := hEsPtr)
        (ptrsOut := ptrsOut) (dataOut := dataOut) (offBase := offBase)
        (j := j) (e := e) (wPtr := mem (mEmbPtr + e)) (curLen := (prefW j).length)
        (st := State.mk memP
          (Function.update
            (Function.update (Function.update s.regs 16 e) 17 (mem (mEmbPtr + e)))
            18 (emb e).length)
          s.pos)
        hpOps hpGT hpSort hw16 hDynP hJ hemb hjV hexV hjE hhE hLenT hTH
        hjAtP hexAtP hhEAtP hjTAtP hjw hexw hhew hjVPair hexPair hhEPair hdisj_vex
        hhB hjVB hexB hhEB hjTB hnHB
        (fun i hi => hdisjSpan _ (hdisjH i hi))
        (fun i hi => hdisjSpan _ (hdisjJT i hi))
        (fun i hi => hdisjSpan _ (hdisjV i hi))
        (fun i hi => hdisjSpan _ (hdisjEx i hi))
        (fun i hi => hdisjSpan _ (hdisjHE i hi))
        hj_lt rfl hwZero hmwP hwLenB hwPtrB
        (fun k hk => hdisjSpan _ (hdisjW e heJ k hk))
        hOutB_j
        ⟨rfl, by simp [Function.update_of_ne, r0], by simp [Function.update_of_ne, r1],
          by simp [Function.update_of_ne, r2], by simp [Function.update_of_ne, r3],
          by simp [Function.update_of_ne, r4], by simp [Function.update_of_ne, r5],
          by simp [Function.update_of_ne, r6], by simp [Function.update_of_ne, r7],
          by simp [Function.update_of_ne, r8], by simp [Function.update_of_ne, r9],
          by simp [Function.update_of_ne, r10], by simp [Function.update_of_ne, r11],
          by simp [Function.update_of_ne, r12], by simp [Function.update_of_ne, r13],
          by simp [Function.update_of_ne, r14], by simp [Function.update_of_ne, r15],
          by simp [Function.update_of_ne], by simp [Function.update_of_ne], by simp⟩
        (k0 := 28)
        (bound := stepCost j)
        (by
          dsimp only [stepCost, Llog]
          rw [he_getD]
          have h90 : 90 * (Nat.log 2 (jVs.length + exVs.length + hEs.length + 2) + 1) ≤
              90 * (emb e).length * (Nat.log 2 (jVs.length + exVs.length + hEs.length + 2) + 1) :=
            Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right 90 (Nat.pos_of_ne_zero hwZero))
          have hsum : 90 * (emb e).length * (Nat.log 2 (jVs.length + exVs.length + hEs.length + 2) + 1) +
              135 * (emb e).length * (Nat.log 2 (jVs.length + exVs.length + hEs.length + 2) + 1) =
              225 * (emb e).length * (Nat.log 2 (jVs.length + exVs.length + hEs.length + 2) + 1) := by
            ring
          have h230 : 225 * (emb e).length * (Nat.log 2 (jVs.length + exVs.length + hEs.length + 2) + 1) ≤
              230 * ((emb e).length + 1) * (Nat.log 2 (jVs.length + exVs.length + hEs.length + 2) + 1) :=
            Nat.mul_le_mul_right _ (by omega)
          omega)
      rcases hBr with ⟨oB, stB, cB, hrunB, ⟨rfl, hrB_le13, hrB14, hrB15, hWalkB, hfrB⟩, hcB⟩
      refine ⟨.normal, stB, cB, hrunB, ⟨⟨by simpa [Function.update_of_ne, r0] using hrB_le13 0 (by omega),
        by simpa [Function.update_of_ne, r1] using hrB_le13 1 (by omega),
        by simpa [Function.update_of_ne, r2] using hrB_le13 2 (by omega),
        by simpa [Function.update_of_ne, r3] using hrB_le13 3 (by omega),
        by simpa [Function.update_of_ne, r4] using hrB_le13 4 (by omega),
        by simpa [Function.update_of_ne, r5] using hrB_le13 5 (by omega),
        by simpa [Function.update_of_ne, r6] using hrB_le13 6 (by omega),
        by simpa [Function.update_of_ne, r7] using hrB_le13 7 (by omega),
        by simpa [Function.update_of_ne, r8] using hrB_le13 8 (by omega),
        by simpa [Function.update_of_ne, r9] using hrB_le13 9 (by omega),
        by simpa [Function.update_of_ne, r10] using hrB_le13 10 (by omega),
        by simpa [Function.update_of_ne, r11] using hrB_le13 11 (by omega),
        by simpa [Function.update_of_ne, r12] using hrB_le13 12 (by omega),
        by simpa [Function.update_of_ne, r13] using hrB_le13 13 (by omega),
        by simp [Function.update_of_ne, hrB14, hlen_j1], by simp, ?_, ?_, ?_⟩, hrB15⟩,
        Nat.le_trans (Nat.add_le_add_right (m := 28) (by decide) cB) hcB⟩
      · intro u hu
        have hu_lt : u < jEs.length := by
          have hpl : (prefPtrs (j + 1)).length = j + 1 := by simp [prefPtrs]
          omega
        have had : ptrsOut + u < dataOut + (prefW j).length ∨
            dataOut + (prefW j).length + (2 * (emb e).length + 3) ≤ ptrsOut + u := by
          rcases hptrData' with h | h <;> [left; right] <;> omega
        rw [hfrB _ had]
        exact hptrs_j1 u hu
      · rw [hprefW_succ]
        refine listAt_append.mpr ⟨fun u hu => ?_, hWalkB⟩
        rw [hfrB _ (Or.inl (by omega))]
        exact hdata_j u hu
      · intro addr hp1 hp2
        have hadW : addr < dataOut + (prefW j).length ∨
            dataOut + (prefW j).length + (2 * (emb e).length + 3) ≤ addr := by
          rcases hp2 with h | h <;> [left; right] <;> omega
        rw [hfrB _ hadW]
        by_cases hpj : addr < ptrsOut ∨ ptrsOut + j ≤ addr
        · dsimp only [memP]
          rw [Function.update_of_ne (by omega)]
          exact hfr addr hpj (by rcases hp2 with h | h <;> [left; right] <;> omega)
        · exfalso
          rcases hp1 with h | h <;> omega
  refine runs_seq_triple_le hloopOut
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
     by simp [startState], by simp [startState], by simp [startState], by simp [startState],
     by simp [startState], by simp [startState], by simp [startState], by simp [startState],
     by simp [startState], by simp [startState], by simp [prefW],
     by simp [prefPtrs, listAt_nil], by simp [prefW, listAt_nil],
     fun addr _ _ => rfl⟩ ?_
  intro st' ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hr14', _, hptrs', hdata', hfr'⟩
  have hdataLen_ltw : dataLen < 2 ^ w := by omega
  have hr14_end : st'.regs 14 = dataLen := hr14'.trans (congrArg List.length hprefW_end)
  have hptrs_end : ListAt st'.mem ptrsOut (canonWalkOffsets offBase cWalks) :=
    hprefPtrs_end ▸ hptrs'
  have hdata_end : ListAt st'.mem dataOut (cWalks.flatMap Walk.encode) :=
    hprefW_end ▸ hdata'
  refine runs_ret_le (v := dataLen)
    (by simp [Expr.eval, hr14_end])
    ⟨hPtr, jEsPtr, jTailsPtr, mEmbPtr, jVsPtr, exVsPtr, hEsPtr, ptrsOut, dataOut, offBase,
      rfl, rfl, hptrs_end, hdata_end, hfr'⟩ ?_
  · have hrc : rangeCost stepCost 0 jEs.length =
        230 * ((collectRawEsFun jEs emb).length + jEs.length) * Llog +
        350 * ((collectRawEsFun jEs emb).length + jEs.length) := by
      have haux : ∀ m ≤ jEs.length,
          rangeCost stepCost 0 m =
            230 * (rangeCost (fun k => (emb (jEs.getD k 0)).length) 0 m + m) * Llog +
            350 * (rangeCost (fun k => (emb (jEs.getD k 0)).length) 0 m + m) := by
        intro m hm
        rw [rangeCost_zero_eq_range, rangeCost_zero_eq_range]
        induction m with
        | zero => simp
        | succ m ih =>
          rw [List.range_succ, List.map_append, List.sum_append,
            List.map_append, List.sum_append, ih (Nat.le_of_lt hm)]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
            stepCost]
          ring
      have hmain := haux jEs.length le_rfl
      rw [rangeCost_embLen_eq] at hmain
      exact hmain
    dsimp only [gtEmitEmbToCitedContract, Llog, Expr.size] at hrc ⊢
    omega

end

end MinCostFlow.DynSpanner.Program
