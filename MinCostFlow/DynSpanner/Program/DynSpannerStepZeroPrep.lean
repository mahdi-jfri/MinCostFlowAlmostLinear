module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepZeroClearPost
import WordRAM.Tactic

/-!
# Phase 1 verification for `dsStepZeroStmt` (`DynSpannerStepZeroPrep`)

Verifies Phase 1 (`dsStepZeroClearBody = dsStepZeroClearA ;; dsStepZeroClearB`) of
`dsStepZeroStmt` in two small halves:
* `stepZero_clearA_triple`: executes `dsUpdateLen`, `dsStepPrefix`, copies `oldHEdges`, bumps
  `gen` to `gOld`, and stamps `eStamp` on `oldHEdges`.
* `stepZero_clearB_triple`: executes `clearAuxGraph`, `dsClearBuckets`, `dsClearAbove`,
  increments `t`, sets `r27 := heapInit`, and establishes `StepZeroClearPost`.
* `stepZero_clear_triple`: chains both halves for `dsStepZeroClearBody`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

@[expose] public section

/-- Postcondition of Phase 1 (`dsStepZeroClearBody`): registers `r0..r27` are populated,
`dsInitCoreContract.pre [b, heapInit]` holds, `oldHEdges` and `restrictUpdate u st.H` are saved
on the heap, `eStamp` records `H_mid_union.E` at `gOld`, higher levels and `S` are cleared, and
caller memory below `heapStep` outside `metaFoot b x` is preserved. -/
def StepZeroClearPost (G₀ : MGraph) (impl : SparsifyImpl) (mMax w L q vCap eCap b k : ℕ)
    (us : List Update) (u : Update) (len updPtr heapStep : ℕ) (mem0 : ℕ → ℕ)
    (x : DynSpannerMeta L) (st1 : State) : Prop :=
  let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
  let G' := st.G.applyUpdate u
  let H_mid := st.H.applyBatch (restrictUpdate u st.H)
  let gOld := mem0 (b + dsGenOff) + 1
  let heapInit := heapStep + 5 + len + H_mid.m
  ∃ prefWords oldHEdges,
    StepZeroPrepRegs b updPtr heapStep L vCap eCap st1.regs ∧
    st1.regs 20 = len ∧ st1.regs 21 = heapStep + 5 ∧ st1.regs 22 = prefWords ∧
    st1.regs 23 = H_mid.m ∧ st1.regs 24 = heapStep + 5 + len ∧
    st1.regs 26 = gOld ∧ st1.regs 27 = heapInit ∧
    prefWords ≤ len ∧
    (dsInitCoreContract impl mMax w L vCap eCap b G').pre [b, heapInit] st1.mem ∧
    BatchBodyAt st1.mem (heapStep + 5) st.H (restrictUpdate u st.H) prefWords ∧
    oldHEdges.Nodup ∧ (∀ e, e ∈ oldHEdges ↔ e ∈ H_mid.E) ∧ oldHEdges.length = H_mid.m ∧
    ListAt st1.mem (heapStep + 5 + len) oldHEdges ∧
    st1.mem (b + dsQOff) = q ∧ st1.mem (b + dsTOff) = k + 1 ∧ st1.mem (b + dsGenOff) = gOld ∧
    (∀ i : Fin (L + 1), 0 < i.1 →
      IsDoublyLinkedList st1.mem (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
        (dsHHeadBase b vCap eCap + i.1) eCap [] ∧
      st1.mem (dsHDegDummyBase b L vCap eCap + i.1) = 0 ∧
      st1.mem (dsDomGenBase b L vCap eCap + i.1) = 0 ∧
      (∀ e < eCap, st1.mem (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) ≤ gOld) ∧
      (∀ v < vCap, st1.mem (dsRevGenBase b L vCap eCap + i.1 * vCap + v) ≤ gOld)) ∧
    (∀ i : Fin (L + 1), st1.mem (dsSGenBase b L vCap eCap + i.1) = 0 ∧
      ∀ v < vCap, st1.mem (dsVSGenBase b L vCap eCap + i.1 * vCap + v) ≤ gOld) ∧
    (∀ v < vCap, st1.mem (dsSBitBase b L vCap eCap + v) = 0) ∧
    (∀ e < eCap, st1.mem (dsEStampBase b L vCap eCap + e) ≤ gOld ∧
      (st1.mem (dsEStampBase b L vCap eCap + e) = gOld ↔ e ∈ H_mid.E) ∧
      st1.mem (dsKeptStampBase b L vCap eCap + e) ≤ gOld) ∧
    (∀ a < heapStep, ¬ metaFoot b x a → st1.mem a = mem0 a)

end

/-- Intermediate state invariant between `dsStepZeroClearA` and `dsStepZeroClearB`. -/
private def StepZeroClearMid (G₀ : MGraph) (impl : SparsifyImpl) (L q vCap eCap b k : ℕ)
    (us : List Update) (u : Update) (len updPtr heapStep : ℕ) (mem0 : ℕ → ℕ)
    (x : DynSpannerMeta L) (stM : State) : Prop :=
  let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
  let G' := st.G.applyUpdate u
  let H_mid := st.H.applyBatch (restrictUpdate u st.H)
  let gOld := mem0 (b + dsGenOff) + 1
  ∃ prefWords oldHEdges mem1 mem2,
    StepZeroPrepRegs b updPtr heapStep L vCap eCap stM.regs ∧
    stM.regs 20 = len ∧ stM.regs 21 = heapStep + 5 ∧ stM.regs 22 = prefWords ∧
    stM.regs 23 = H_mid.m ∧ stM.regs 24 = heapStep + 5 + len ∧ stM.regs 26 = gOld ∧
    prefWords ≤ len ∧
    BatchBodyAt mem1 (heapStep + 5) st.H (restrictUpdate u st.H) prefWords ∧
    DynGraphAt mem1 (dsGPtr b) vCap eCap G' ∧
    DynGraphAt stM.mem (dsHPtr b vCap eCap) vCap eCap H_mid ∧
    BucketsAt mem1 L vCap eCap b (fun i => delErase u (if hi : i < L + 1 then x.hBuckets ⟨i, hi⟩ else [])) ∧
    (∀ e < eCap, mem1 (dsMinHBase b vCap eCap + e) = minHAfter u (mem0 (dsMinHBase b vCap eCap + e)) e) ∧
    (∀ a, a < heapStep + 5 ∨ heapStep + 5 + len ≤ a →
      (a < dsGPtr b ∨ (dsAuxPtr b vCap eCap ≤ a ∧ a < dsMinHBase b vCap eCap) ∨
        dsDomGenBase b L vCap eCap ≤ a) → mem1 a = mem0 a) ∧
    oldHEdges.Nodup ∧ (∀ e, e ∈ oldHEdges ↔ e ∈ H_mid.E) ∧ oldHEdges.length = H_mid.m ∧
    ListAt mem2 (heapStep + 5 + len) oldHEdges ∧
    (∀ a, a < heapStep + 5 + len ∨ heapStep + 5 + len + H_mid.m ≤ a → mem2 a = mem1 a) ∧
    stM.mem (b + dsGenOff) = gOld ∧
    (∀ e ∈ oldHEdges, stM.mem (dsEStampBase b L vCap eCap + e) = gOld) ∧
    (∀ a, a ≠ b + dsGenOff → (∀ e ∈ oldHEdges, a ≠ dsEStampBase b L vCap eCap + e) →
      stM.mem a = mem2 a)

/-- First half of Phase 1 (`dsStepZeroClearA`). -/
private theorem stepZero_clearA_triple {G₀ : MGraph} {impl : SparsifyImpl}
    {mMax w L q vCap eCap b k : ℕ} {us : List Update} {u : Update}
    {len updPtr heapStep : ℕ} {mem0 : ℕ → ℕ} {x : DynSpannerMeta L} {p : Program}
    {bs : StepZeroBases}
    (hps : HasStepZeroProcs impl p bs)
    (hw16 : 16 ≤ 2 ^ w) (hq : 1 ≤ q) (hVG₀ : G₀.IsValid) (hBV : G₀.BatchIsValid us)
    (hds : ∀ u' ∈ us, isDelOrSplit u') (hu_some : us[k]? = some u)
    (hPref : ∀ s ≤ k, SnapInv G₀ L q mMax (canonicalSparsifyParams impl mMax).absorbTime
      (canonicalSparsify impl) us s)
    (hState : DynSpannerStateAt L vCap eCap b mem0 x
      (runState (L := L) G₀ q (canonicalSparsify impl) us k))
    (hfix : b + dsFixedSize L vCap eCap ≤ heapStep)
    (hsp :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let G' := st.G.applyUpdate u
      let H₀ := (initCore G' (canonicalSparsify impl)).1
      heapStep + dsStepZeroSpace impl mMax vCap eCap G' st.H H₀ len < 2 ^ w)
    (hgen_w :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      mem0 (b + dsGenOff) + 2 + (st.G.applyUpdate u).m < 2 ^ w)
    (hupd_le : updPtr + len ≤ heapStep)
    (hupd_foot : ∀ i < len, ¬ metaFoot b x (updPtr + i))
    (hupd_w : ∀ i < len, mem0 (updPtr + i) < 2 ^ w)
    (hupd_at : UpdateAt mem0 updPtr (runState (L := L) G₀ q (canonicalSparsify impl) us k).G u len)
    (hupd_cap : UpdateWithinCaps vCap eCap u) :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let H_mid := st.H.applyBatch (restrictUpdate u st.H)
    Triple w p
      (fun st0 => st0.mem = mem0 ∧ StepZeroPrepRegs b updPtr heapStep L vCap eCap st0.regs)
      (dsStepZeroClearA bs.bAux bs.bZAux bs.bPref)
      (normalPost (StepZeroClearMid G₀ impl L q vCap eCap b k us u len updPtr heapStep mem0 x))
      (fun _ => 1320 * len + 65 * H_mid.m + 750) := by
  intro st H_mid st0 ω ⟨hm0, hR⟩
  rcases st0 with ⟨mem_s, regs0, pos0⟩
  dsimp only at hm0 hR ⊢
  subst mem_s
  set G' := st.G.applyUpdate u
  set gOld := mem0 (b + dsGenOff) + 1
  obtain ⟨_, _, hU_k⟩ := batchIsValid_take us G₀ k hBV hds
  obtain ⟨_, hdu⟩ := hU_k u hu_some
  have hBnd := stepZero_clear_bounds b L vCap eCap
  have hgo : b + dsGenOff < dsGPtr b := hBnd.1
  have hG_le_H : dsGPtr b ≤ dsHPtr b vCap eCap := hBnd.2.1 ▸ Nat.le_add_right _ _
  have hH_top : dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ dsAuxPtr b vCap eCap := hBnd.2.2.1 ▸ le_rfl
  have hAux_le_min : dsAuxPtr b vCap eCap ≤ dsMinHBase b vCap eCap := hBnd.2.2.2.1 ▸ Nat.le_add_right _ _
  have hAux_le_eSt : dsAuxPtr b vCap eCap ≤ dsEStampBase b L vCap eCap := by
    have := hBnd; omega
  have heSt_top : dsEStampBase b L vCap eCap + eCap ≤ b + dsFixedSize L vCap eCap := by
    have := hBnd; omega
  have hmin_le_fix : dsMinHBase b vCap eCap ≤ b + dsFixedSize L vCap eCap := by
    have := hBnd; omega
  have hHm_lt : dsHPtr b vCap eCap + dgMOff < dsAuxPtr b vCap eCap := hBnd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hPr_le : dgEPresBase (dsHPtr b vCap eCap) vCap + eCap ≤ dsAuxPtr b vCap eCap := hBnd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hEL_le : dgEListBase (dsHPtr b vCap eCap) vCap eCap + eCap ≤ dsAuxPtr b vCap eCap := hBnd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hBnd
  have hHmid_m_le : H_mid.m ≤ st.H.m := by
    have hE := mid_E_delSet hdu st.H
    have hsub : H_mid.E ⊆ st.H.E := by
      rw [hE]; cases u with
      | insert _ _ _ => exact hdu.elim
      | delete _ => exact Finset.erase_subset _ _
      | split _ _ _ _ => exact Finset.Subset.rfl
    exact Finset.card_le_card hsub
  have hsp' : heapStep + dsStepZeroSpace impl mMax vCap eCap G' st.H
      (initCore G' (canonicalSparsify impl)).1 len < 2 ^ w := hsp
  have hfix_w : b + dsFixedSize L vCap eCap < 2 ^ w := by
    dsimp only [dsStepZeroSpace] at hsp'; omega
  have hHm_ec : H_mid.m ≤ eCap := by
    have hsub : H_mid.E ⊆ Finset.range eCap := fun e he => Finset.mem_range.mpr (by
      have hE := mid_E_delSet hdu st.H
      have hsub0 : H_mid.E ⊆ st.H.E := by
        rw [hE]; cases u with
        | insert _ _ _ => exact hdu.elim
        | delete _ => exact Finset.erase_subset _ _
        | split _ _ _ _ => exact Finset.Subset.rfl
      exact hState.2.2.2.2.2.2.2.2.2.2.1 e (hState.2.2.2.2.2.2.2.1 (hsub0 he)))
    simpa [MGraph.m] using Finset.card_le_card hsub
  have hheapInit_w : heapStep + 5 + len + H_mid.m < 2 ^ w := by
    dsimp only [dsStepZeroSpace] at hsp'; omega
  have r0 := hR.1; have r1 := hR.2.1; have r2 := hR.2.2.1
  have r8 := hR.2.2.2.2.2.2.2.2.1; have r9 := hR.2.2.2.2.2.2.2.2.2.1
  have r11 := hR.2.2.2.2.2.2.2.2.2.2.2.1; have r17 := hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have r18 := hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have r19 := hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  dsimp only [dsStepZeroClearA]
  refine runs_start_le ?_
  -- Call 1: `dsUpdateLen [updPtr]`
  refine runs_seq_call_le (vs := [updPtr])
    (dsUpdateLen_meetsContract (w := w) (G := st.G) (u := u) (len := len) hps.hpAux)
    (by simp [evalArgs, Expr.eval, r1])
    (fun z hz => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; subst hz; omega)
    ⟨updPtr, rfl, hw16, by omega, hupd_at⟩ ?_
  rintro ret_len mem_u _ ⟨hret_len, hmem_u⟩
  subst mem_u
  -- Assign `r21 := heapStep + 5`
  refine runs_seq_assign_le (v := heapStep + 5)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r2])) (Expr.eval_const (by omega)) (by omega)) ?_
  -- Call 2: `dsStepPrefix`
  have hPrePref := stepZero_prefix_pre hVG₀ hq hBV hds hu_some hPref hw16 hState hfix (by omega)
    hupd_le hupd_foot hupd_w hupd_at hupd_cap
  refine runs_seq_call_le (vs := [dsGPtr b, dsHPtr b vCap eCap, b, dsMinHBase b vCap eCap,
      updPtr, dgEPresBase (dsHPtr b vCap eCap) vCap, heapStep + 5])
    (dsStepPrefix_meetsContract hps.hpBatch hps.hpEdge hps.hpSplit hps.hpOps hps.hpPhase hps.hpD
      hps.hpU hps.hpF hps.hpR hps.hpPref)
    (by simp [evalArgs, Expr.eval, r0, r1, r8, r9, r11, r18])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    hPrePref ?_
  rintro prefWords mem1 _ ⟨hpref_le, hPrefBat1, hG1, hH1, hB1, hmin1, hfr1⟩
  have hm1_H : mem1 (dsHPtr b vCap eCap + dgMOff) = H_mid.m := hH1.2.2.2.2.2.2.1
  have hdgm_off : dgMOff = 3 := rfl
  refine runs_seq_assign_le (v := H_mid.m)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r9]))
      (Expr.eval_const (by rw [hdgm_off]; omega)) (by omega)) hm1_H) ?_
  refine runs_seq_assign_le (v := heapStep + 5 + len)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp [hret_len])) (by omega)) ?_
  -- Call 3: `dsCopyWords [hEList, oldEListPtr, oldHM]`
  rcases hH1.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨oldHEdges, hold_len, hold_nd, hold_mem, hold_at, _⟩
  refine runs_seq_call_le (vs := [dgEListBase (dsHPtr b vCap eCap) vCap eCap, heapStep + 5 + len, H_mid.m])
    (dsCopyWords_meetsContract (w := w) (n := H_mid.m) hps.hpAux)
    (by simp [evalArgs, Expr.eval, r19])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> omega)
    ⟨dgEListBase (dsHPtr b vCap eCap) vCap eCap, heapStep + 5 + len, rfl, hw16, by omega,
      by omega, by unfold IvlDisj; omega⟩ ?_
  rintro _ mem2 _ ⟨_, _, hEqC1, _, hcp1, hfr2⟩
  simp only [List.cons.injEq, and_true] at hEqC1
  rcases hEqC1 with ⟨rfl, rfl⟩
  have hold_at2 : ListAt mem2 (heapStep + 5 + len) oldHEdges := fun i hi =>
    (hcp1 i (hold_len ▸ hi)).trans (hold_at i hi)
  -- Assign `gOld := mem2[b + dsGenOff] + 1` and store at `b + dsGenOff`
  have hgen2 : mem2 (b + dsGenOff) = mem0 (b + dsGenOff) :=
    (hfr2 _ (Or.inl (by omega))).trans (hfr1 _ (Or.inl (by omega)) (Or.inl hgo))
  have hgen_off : dsGenOff = 5 := rfl
  have hgen_w' : mem0 (b + dsGenOff) + 2 + G'.m < 2 ^ w := hgen_w
  refine runs_seq_assign_le (v := gOld)
    (Expr.eval_add
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r0]))
        (Expr.eval_const (by rw [hgen_off]; omega)) (by omega)) hgen2)
      (Expr.eval_const (by omega)) (by omega)) ?_
  refine runs_seq_store_le (x := b + dsGenOff) (v := gOld)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r0]))
      (Expr.eval_const (by rw [hgen_off]; omega)) (by omega))
    (Expr.eval_reg_of_eq (by simp)) ?_
  set mem3 := Function.update mem2 (b + dsGenOff) gOld
  have hfr3 : ∀ addr, addr ≠ b + dsGenOff → mem3 addr = mem2 addr := fun a h =>
    Function.update_of_ne h _ _
  -- Call 4: `dsStampList [eStamp, oldEListPtr, oldHM, gOld]`
  have hold_ec : ∀ e ∈ oldHEdges, e < eCap := fun e he => hH1.2.2.1 e ((hold_mem e).mp he)
  refine runs_call_le (vs := [dsEStampBase b L vCap eCap, heapStep + 5 + len, H_mid.m, gOld])
    (dsStampList_meetsContract (w := w) (cap := eCap) (es := oldHEdges) (stampVal := gOld) hps.hpZAux)
    (by simp [evalArgs, Expr.eval, r17])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> omega)
    ⟨dsEStampBase b L vCap eCap, heapStep + 5 + len, by simp [hold_len]; rfl, hw16, by omega,
      by rw [hold_len]; exact hheapInit_w,
      by omega, by unfold IvlDisj; omega,
      hold_at2.congr fun a h1 _ => hfr3 a (by omega), hold_ec⟩ ?_
  rintro _ mem4 _ ⟨_, _, hEq4, _, hst4, hfr4⟩
  simp only [List.cons.injEq, and_true] at hEq4
  rcases hEq4 with ⟨rfl, rfl, _⟩
  refine ⟨?_, ?_⟩
  · have hH4 : DynGraphAt mem4 (dsHPtr b vCap eCap) vCap eCap H_mid :=
      dynGraphAt_of_agree hH1 fun a h1 h2 =>
        (hfr4 a fun e he => by have := hold_ec e he; omega).trans
          ((hfr3 a (by omega)).trans (hfr2 a (Or.inl (by omega))))
    exact ⟨prefWords, oldHEdges, mem1, mem2,
      stepZeroPrepRegs_of_agree hR (fun i hi => by
        repeat (first | rw [Function.update_of_ne (by omega)] | dsimp only)),
      by repeat (first | rw [Function.update_of_ne (by decide)] | dsimp only)
         rw [Function.update_self]; exact hret_len,
      by repeat (first | rw [Function.update_of_ne (by decide)] | dsimp only)
         rw [Function.update_self],
      by repeat (first | rw [Function.update_of_ne (by decide)] | dsimp only)
         rw [Function.update_self],
      by repeat (first | rw [Function.update_of_ne (by decide)] | dsimp only)
         rw [Function.update_self],
      by repeat (first | rw [Function.update_of_ne (by decide)] | dsimp only)
         rw [Function.update_self],
      by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self],
      hpref_le, hPrefBat1, hG1, hH4,
      hB1, hmin1, hfr1, hold_nd, hold_mem, hold_len, hold_at2, hfr2,
      (hfr4 _ fun e he => by have := hold_ec e he; omega).trans (by simp [mem3]; rfl),
      hst4, fun a hne hnes => (hfr4 a hnes).trans (hfr3 a hne)⟩
  · have hlen_m : oldHEdges.length = H_mid.m := hold_len
    simp only [dsUpdateLenContract, dsStepPrefixContract, dsCopyWordsContract, dsStampListContract,
      hlen_m, Expr.size, argsSize]
    dsimp only [H_mid, st]; omega

/-- Tail of `dsStepZeroClearB`: `dsClearAbove`, increment `t`, assign `r27 := heapInit`, and
assemble `StepZeroClearPost`. -/
private theorem stepZero_clearB_tail {G₀ : MGraph} {impl : SparsifyImpl}
    {mMax w L q vCap eCap b k : ℕ} {us : List Update} {u : Update}
    {len updPtr heapStep prefWords : ℕ} {oldHEdges : List ℕ}
    {mem0 mem1 mem2 mem4 mem5 mem6 : ℕ → ℕ} {x : DynSpannerMeta L} {p : Program}
    {bs : StepZeroBases}
    (hps : HasStepZeroProcs impl p bs)
    (hw16 : 16 ≤ 2 ^ w) (hVG₀ : G₀.IsValid) (hGm₀ : G₀.m ≤ mMax) (hBV : G₀.BatchIsValid us)
    (hds : ∀ u' ∈ us, isDelOrSplit u') (hu_some : us[k]? = some u)
    (hPref : ∀ s ≤ k, SnapInv G₀ L q mMax (canonicalSparsifyParams impl mMax).absorbTime
      (canonicalSparsify impl) us s)
    (hState : DynSpannerStateAt L vCap eCap b mem0 x
      (runState (L := L) G₀ q (canonicalSparsify impl) us k))
    (hfix : b + dsFixedSize L vCap eCap ≤ heapStep) (hz0 : ZeroFrom mem0 heapStep)
    (hsp_lt :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let G' := st.G.applyUpdate u
      let H_mid := st.H.applyBatch (restrictUpdate u st.H)
      heapStep + 5 + len + H_mid.m + dsInitCoreSpaceBound impl mMax vCap eCap G' < 2 ^ w)
    (hgen_w :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      mem0 (b + dsGenOff) + 2 + (st.G.applyUpdate u).m < 2 ^ w)
    (hk_w : k + 1 < 2 ^ w)
    (hw'_le :
      let G' := (runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u
      G'.E.Nonempty →
        wordSize impl.cw (canonSparsifyInput (activeSubgraph G') (activeSubgraph G') idEmb) ≤ w)
    (hupd_cap : UpdateWithinCaps vCap eCap u)
    (hpref_le : prefWords ≤ len)
    (hPrefBat1 : BatchBodyAt mem1 (heapStep + 5)
      (runState (L := L) G₀ q (canonicalSparsify impl) us k).H
      (restrictUpdate u (runState (L := L) G₀ q (canonicalSparsify impl) us k).H) prefWords)
    (hG1 : DynGraphAt mem1 (dsGPtr b) vCap eCap
      ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u))
    (hH5 : DynGraphAt mem5 (dsHPtr b vCap eCap) vCap eCap emptyMGraph)
    (hold_nd : oldHEdges.Nodup)
    (hold_mem : ∀ e, e ∈ oldHEdges ↔
      e ∈ ((runState (L := L) G₀ q (canonicalSparsify impl) us k).H.applyBatch
        (restrictUpdate u (runState (L := L) G₀ q (canonicalSparsify impl) us k).H)).E)
    (hold_len : oldHEdges.length =
      ((runState (L := L) G₀ q (canonicalSparsify impl) us k).H.applyBatch
        (restrictUpdate u (runState (L := L) G₀ q (canonicalSparsify impl) us k).H)).m)
    (hold_ec : ∀ e ∈ oldHEdges, e < eCap)
    (hold_at2 : ListAt mem2 (heapStep + 5 + len) oldHEdges)
    (hmin6 : ∀ e < eCap, mem6 (dsMinHBase b vCap eCap + e) = 0)
    (hbuck6 : ∀ i : Fin (L + 1),
      IsDoublyLinkedList mem6 (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
        (dsHHeadBase b vCap eCap + i.1) eCap [] ∧
      mem6 (dsHDegDummyBase b L vCap eCap + i.1) = 0)
    (hgen4 : mem4 (b + dsGenOff) = mem0 (b + dsGenOff) + 1)
    (hst4 : ∀ e ∈ oldHEdges, mem4 (dsEStampBase b L vCap eCap + e) = mem0 (b + dsGenOff) + 1)
    (hfr1 : ∀ a, a < heapStep + 5 ∨ heapStep + 5 + len ≤ a →
      (a < dsGPtr b ∨ (dsAuxPtr b vCap eCap ≤ a ∧ a < dsMinHBase b vCap eCap) ∨
        dsDomGenBase b L vCap eCap ≤ a) → mem1 a = mem0 a)
    (hfr2 : ∀ a, a < heapStep + 5 + len ∨
      heapStep + 5 + len + ((runState (L := L) G₀ q (canonicalSparsify impl) us k).H.applyBatch
        (restrictUpdate u (runState (L := L) G₀ q (canonicalSparsify impl) us k).H)).m ≤ a →
      mem2 a = mem1 a)
    (hfr4 : ∀ a, a ≠ b + dsGenOff → (∀ e ∈ oldHEdges, a ≠ dsEStampBase b L vCap eCap + e) →
      mem4 a = mem2 a)
    (hfr5 : ∀ a, a < dsHPtr b vCap eCap ∨ dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ a →
      mem5 a = mem4 a)
    (hfr6 : ∀ a, a < dsMinHBase b vCap eCap ∨ dsDomGenBase b L vCap eCap ≤ a → mem6 a = mem5 a) :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let H_mid := st.H.applyBatch (restrictUpdate u st.H)
    Triple w p
      (fun st6 => st6.mem = mem6 ∧ StepZeroPrepRegs b updPtr heapStep L vCap eCap st6.regs ∧
        st6.regs 20 = len ∧ st6.regs 21 = heapStep + 5 ∧ st6.regs 22 = prefWords ∧
        st6.regs 23 = H_mid.m ∧ st6.regs 24 = heapStep + 5 + len ∧
        st6.regs 26 = mem0 (b + dsGenOff) + 1)
      (.call 25 (bs.bClrA + clearAboveIdx) [.reg 15, .reg 16, .const 1, .const 0, .reg 6] ;;
       .store (.bin .add (.reg 0) (.const dsTOff))
         (.bin .add (.load (.bin .add (.reg 0) (.const dsTOff))) (.const 1)) ;;
       .assign 27 (.bin .add (.reg 24) (.reg 23)))
      (normalPost (StepZeroClearPost G₀ impl mMax w L q vCap eCap b k us u len updPtr heapStep mem0 x))
      (fun _ => 30 * (L + 1) + 120) := by
  intro st H_mid st6 ω ⟨hm6, hR, r20, r21, r22, r23, r24, r26⟩
  rcases st6 with ⟨mem_s, regs6, pos6⟩
  dsimp only at hm6 hR r20 r21 r22 r23 r24 r26 ⊢
  subst mem_s
  set heapInit := heapStep + 5 + len + H_mid.m
  have hk_inv := hPref k le_rfl
  have hBnd := stepZero_clear_bounds b L vCap eCap
  have hgo : b + dsGenOff < dsGPtr b := hBnd.1
  have hG_le_H : dsGPtr b ≤ dsHPtr b vCap eCap := hBnd.2.1 ▸ Nat.le_add_right _ _
  have hH_le_min : dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ dsMinHBase b vCap eCap := by
    have := hBnd.2.2.1; have := hBnd.2.2.2.1; omega
  have hmin_le_dom : dsMinHBase b vCap eCap ≤ dsDomGenBase b L vCap eCap := by have := hBnd; omega
  have hdom_le_s : dsDomGenBase b L vCap eCap + (L + 1) ≤ dsSGenBase b L vCap eCap := by have := hBnd; omega
  have hs_le_eSt : dsSGenBase b L vCap eCap + (L + 1) ≤ dsEStampBase b L vCap eCap := by have := hBnd; omega
  have heSt_le_fix : dsEStampBase b L vCap eCap + eCap ≤ b + dsFixedSize L vCap eCap := by have := hBnd; omega
  clear hBnd
  have r0 := hR.1; have r6 := hR.2.2.2.2.2.2.1
  have r15 := hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have r16 := hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine runs_start_le ?_
  refine runs_seq_call_le (vs := [dsDomGenBase b L vCap eCap, dsSGenBase b L vCap eCap, 1, 0, L + 1])
    (dsClearAbove_meetsContract (w := w) (dBase := dsDomGenBase b L vCap eCap)
      (sBase := dsSGenBase b L vCap eCap) (dLo := 1) (sLo := 0) (hi := L + 1) hps.hpZ hps.hpClrA)
    (by simp [evalArgs, Expr.eval, r15, r16, r6, show (0 : ℕ) < 2 ^ w by omega,
      show (1 : ℕ) < 2 ^ w by omega])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨rfl, by omega, Nat.zero_le _, by omega, by omega, by omega⟩ ?_
  rintro _ mem7 _ ⟨hzD7, hzS7, hfr7⟩
  have ht7 : mem7 (b + dsTOff) = k := by
    have ha : b + dsTOff < dsGPtr b := by simp [dsTOff, dsGPtr, dsHdrSize]
    have hne : b + dsTOff ≠ b + dsGenOff := by simp [dsTOff, dsGenOff]
    rw [hfr7 _ (Or.inl (by omega)) (Or.inl (by omega))]
    dsimp only
    rw [hfr6 _ (Or.inl (by omega)), hfr5 _ (Or.inl (by omega)),
      hfr4 _ hne (fun e he => by have := hold_ec e he; omega),
      hfr2 _ (Or.inl (by omega)), hfr1 _ (Or.inl (by omega)) (Or.inl ha),
      hState.2.2.2.2.2.2.2.2.2.2.2.2.1, hk_inv.t_eq]
  have ht_off : dsTOff = 1 := rfl
  refine runs_seq_store_le (x := b + dsTOff) (v := k + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide)]; exact r0))
      (Expr.eval_const (by rw [ht_off]; omega)) (by rw [ht_off]; omega))
    (Expr.eval_add
      (Expr.eval_load_of_eq (Expr.eval_add
        (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide)]; exact r0))
        (Expr.eval_const (by rw [ht_off]; omega)) (by rw [ht_off]; omega)) ht7)
      (Expr.eval_const (by omega)) hk_w) ?_
  have hheap_w : heapStep + 5 + len + H_mid.m < 2 ^ w := by
    have hsp' : heapStep + 5 + len + H_mid.m +
        dsInitCoreSpaceBound impl mMax vCap eCap (st.G.applyUpdate u) < 2 ^ w := hsp_lt
    omega
  refine runs_assign_le (v := heapInit)
    (Expr.eval_add
      (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide)]; exact r24))
      (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide)]; exact r23))
      hheap_w) ?_ ?_
  · set mem8 := Function.update mem7 (b + dsTOff) (k + 1)
    have hmemPost := stepZero_clear_post_mem (mem8 := mem8) hw16 hVG₀ hGm₀ hBV hds hu_some hPref
      hState hupd_cap hfix hz0 hsp_lt hgen_w hw'_le hpref_le hPrefBat1 hG1 hH5
      hold_nd hold_mem hold_len hold_ec hold_at2 hmin6 hbuck6 hzD7 hzS7 hgen4 hst4
      hfr1 hfr2 hfr4 hfr5 hfr6 hfr7 (fun a h => Function.update_of_ne h _ _)
      (Function.update_self _ _ _)
    exact ⟨prefWords, oldHEdges,
      stepZeroPrepRegs_of_agree hR (fun i hi => by
        dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]),
      by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact r20,
      by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact r21,
      by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact r22,
      by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact r23,
      by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact r24,
      by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact r26,
      by dsimp only; rw [Function.update_self], hpref_le, hmemPost⟩
  · simp only [dsClearAboveContract, Expr.size, argsSize]; omega

/-- Second half of Phase 1 (`dsStepZeroClearB`). -/
private theorem stepZero_clearB_triple {G₀ : MGraph} {impl : SparsifyImpl}
    {mMax w L q vCap eCap b k : ℕ} {us : List Update} {u : Update}
    {len updPtr heapStep : ℕ} {mem0 : ℕ → ℕ} {x : DynSpannerMeta L} {p : Program}
    {bs : StepZeroBases}
    (hps : HasStepZeroProcs impl p bs)
    (hw16 : 16 ≤ 2 ^ w) (hVG₀ : G₀.IsValid) (hGm₀ : G₀.m ≤ mMax) (hBV : G₀.BatchIsValid us)
    (hds : ∀ u' ∈ us, isDelOrSplit u') (hu_some : us[k]? = some u)
    (hPref : ∀ s ≤ k, SnapInv G₀ L q mMax (canonicalSparsifyParams impl mMax).absorbTime
      (canonicalSparsify impl) us s)
    (hState : DynSpannerStateAt L vCap eCap b mem0 x
      (runState (L := L) G₀ q (canonicalSparsify impl) us k))
    (hfix : b + dsFixedSize L vCap eCap ≤ heapStep) (hz0 : ZeroFrom mem0 heapStep)
    (hsp :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let G' := st.G.applyUpdate u
      let H₀ := (initCore G' (canonicalSparsify impl)).1
      heapStep + dsStepZeroSpace impl mMax vCap eCap G' st.H H₀ len < 2 ^ w)
    (hgen_w :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      mem0 (b + dsGenOff) + 2 + (st.G.applyUpdate u).m < 2 ^ w)
    (hk_w : k + 1 < 2 ^ w)
    (hw'_le :
      let G' := (runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u
      G'.E.Nonempty →
        wordSize impl.cw (canonSparsifyInput (activeSubgraph G') (activeSubgraph G') idEmb) ≤ w)
    (hupd_cap : UpdateWithinCaps vCap eCap u) :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let G' := st.G.applyUpdate u
    let H_mid := st.H.applyBatch (restrictUpdate u st.H)
    Triple w p
      (StepZeroClearMid G₀ impl L q vCap eCap b k us u len updPtr heapStep mem0 x)
      (dsStepZeroClearB bs.bPhase bs.bCB bs.bClrA)
      (normalPost (StepZeroClearPost G₀ impl mMax w L q vCap eCap b k us u len updPtr heapStep mem0 x))
      (fun _ => 540 * H_mid.m + 30 * G'.n + 90 * (L + 1) + 270) := by
  intro st G' H_mid stM ω ⟨prefWords, oldHEdges, mem1, mem2, hR, r20, r21, r22, r23, r24, r26,
    hpref_le, hPrefBat1, hG1, hH4, hB1, hmin1, hfr1, hold_nd, hold_mem, hold_len, hold_at2,
    hfr2, hgen4, hst4, hfr4⟩
  set mem4 := stM.mem
  set gOld := mem0 (b + dsGenOff) + 1
  set heapInit := heapStep + 5 + len + H_mid.m
  have hk_inv := hPref k le_rfl
  obtain ⟨_, _, hU_k⟩ := batchIsValid_take us G₀ k hBV hds
  obtain ⟨hu_val, hdu⟩ := hU_k u hu_some
  have hBnd := stepZero_clear_bounds b L vCap eCap
  have hgo : b + dsGenOff < dsGPtr b := hBnd.1
  have hgh : dsGPtr b + dynGraphSize vCap eCap = dsHPtr b vCap eCap := hBnd.2.1
  have hha : dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap := hBnd.2.2.1
  have ham : dsAuxPtr b vCap eCap + dynGraphSize vCap eCap = dsMinHBase b vCap eCap := hBnd.2.2.2.1
  have hmin_le_hn : dsMinHBase b vCap eCap + eCap ≤ dsHNextBase b vCap eCap := hBnd.2.2.2.2.1
  have hhn_le_hh : dsHNextBase b vCap eCap ≤ dsHHeadBase b vCap eCap := hBnd.2.2.2.2.2.1
  have hhh_hd : dsHHeadBase b vCap eCap + (L + 1) = dsHDegDummyBase b L vCap eCap := hBnd.2.2.2.2.2.2.1
  have hhd_dm : dsHDegDummyBase b L vCap eCap + (L + 1) = dsDomGenBase b L vCap eCap := hBnd.2.2.2.2.2.2.2.1
  have hdm_s : dsDomGenBase b L vCap eCap + (L + 1) ≤ dsSGenBase b L vCap eCap := by have := hBnd; omega
  have hs_eSt : dsSGenBase b L vCap eCap + (L + 1) ≤ dsEStampBase b L vCap eCap := by have := hBnd; omega
  have heSt_fix : dsEStampBase b L vCap eCap + eCap ≤ b + dsFixedSize L vCap eCap := by have := hBnd; omega
  clear hBnd
  have hHmid_m_le : H_mid.m ≤ st.H.m := by
    have hE := mid_E_delSet hdu st.H
    have hsub : H_mid.E ⊆ st.H.E := by
      rw [hE]; cases u with
      | insert _ _ _ => exact hdu.elim
      | delete _ => exact Finset.erase_subset _ _
      | split _ _ _ _ => exact Finset.Subset.rfl
    exact Finset.card_le_card hsub
  have hHmid_n : H_mid.n = G'.n := by
    have hr := isSubgraph_restrictUpdate
      ⟨hState.2.2.2.2.2.2.1.subset, hState.2.2.2.2.2.2.2.1, hState.2.2.2.2.2.2.2.2.1⟩
      hState.2.2.2.2.2.2.1 (hk_inv.G_eq ▸ hu_val) hdu
    exact congrArg Finset.card hr.2.2.1
  have hsp' : heapStep + dsStepZeroSpace impl mMax vCap eCap G' st.H
      (initCore G' (canonicalSparsify impl)).1 len < 2 ^ w := hsp
  have hfix_w : b + dsFixedSize L vCap eCap < 2 ^ w := by
    dsimp only [dsStepZeroSpace] at hsp'; omega
  have hsp_lt : heapInit + dsInitCoreSpaceBound impl mMax vCap eCap G' < 2 ^ w := by
    dsimp only [dsStepZeroSpace, heapInit] at hsp' ⊢; omega
  have hold_ec : ∀ e ∈ oldHEdges, e < eCap := fun e he => hH4.2.2.1 e ((hold_mem e).mp he)
  have r0 := hR.1; have r6 := hR.2.2.2.2.2.2.1
  have r9 := hR.2.2.2.2.2.2.2.2.2.1; have r11 := hR.2.2.2.2.2.2.2.2.2.2.2.1
  have r12 := hR.2.2.2.2.2.2.2.2.2.2.2.2.1; have r13 := hR.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have r14 := hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; have r15 := hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have r16 := hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  dsimp only [dsStepZeroClearB]
  refine runs_start_le ?_
  -- Call 5: `clearAuxGraph [hPtr]`
  refine runs_seq_call_le (vs := [dsHPtr b vCap eCap])
    (clearAuxGraph_meetsContract (w := w) (vCap := vCap) (eCap := eCap) (A := H_mid) hps.hpPhase hps.hpEdge hps.hpOps)
    (by simp [evalArgs, Expr.eval, r9])
    (fun z hz => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hz; subst hz; omega)
    ⟨dsHPtr b vCap eCap, rfl, hw16, by omega, hH4⟩ ?_
  rintro _ mem5 _ ⟨_, hEq5, _, hH5, hfr5⟩
  simp only [List.cons.injEq, and_true] at hEq5
  subst hEq5
  -- Call 6: `dsClearBuckets [hNext, hHead, hDeg, 0, L + 1, minH]`
  have hag5_buck : ∀ addr, dsMinHBase b vCap eCap ≤ addr → addr < dsDomGenBase b L vCap eCap →
      mem5 addr = mem1 addr := fun a h1 h2 =>
    (hfr5 a (Or.inr (by omega))).trans
      ((hfr4 a (by omega) fun e he => by have := hold_ec e he; omega).trans (hfr2 a (Or.inl (by omega))))
  obtain ⟨cb, hcbW, hcbE, hcbB, hcbLo, hcbHi, _, hcbNext, hcbHead, hcbDeg, hcbMin, hcbMem,
    hcbLen, _, hcbPost⟩ :=
    stepZero_clearBuckets_ctx hBV hds hu_some hPref hw16 hState hfix_w hB1 hmin1 hag5_buck
  have hcbM : MeetsContract w p (bs.bCB + clearBucketsIdx) (dsClearBucketsContract cb) := by
    rw [← hcbW]; exact dsClearBuckets_meetsContract cb hps.hpCB
  refine runs_seq_call_le (vs := [dsHNextBase b vCap eCap, dsHHeadBase b vCap eCap,
      dsHDegDummyBase b L vCap eCap, 0, L + 1, dsMinHBase b vCap eCap])
    hcbM
    (by simp [evalArgs, Expr.eval, r12, r13, r14, r6, r11, show (0 : ℕ) < 2 ^ w by omega])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨by simp [hcbNext, hcbHead, hcbDeg, hcbLo, hcbHi, hcbMin], hcbMem.symm⟩ ?_
  rintro _ mem6 _ hCB6
  have hCB6' : CBMem cb (bucketsCat (fun i => delErase u (if hi : i < L + 1 then x.hBuckets ⟨i, hi⟩ else [])) 0 (L + 1)) (L + 1) mem6 := by
    simpa only [dsClearBucketsContract, hcbB, hcbLo, hcbHi, Nat.sub_zero] using hCB6
  obtain ⟨hmin6, hbuck6⟩ := hcbPost mem6 hCB6'
  have hfr6 : ∀ addr, (addr < dsMinHBase b vCap eCap ∨ dsDomGenBase b L vCap eCap ≤ addr) →
      mem6 addr = mem5 addr := by
    intro addr h
    refine (hCB6.2.2 addr (fun x hx => ?_) (fun i' h1 h2 => ?_)).trans (congrFun hcbMem addr)
    · rw [hcbMin]
      have hxC : x < eCap := by
        have := cb.cat_lt (le_refl cb.hi)
        rw [hcbE] at this
        exact this x hx
      omega
    · rw [hcbHi] at h2; rw [hcbHead, hcbDeg]; omega
  -- Call 7 + store + assign via `stepZero_clearB_tail`
  refine runs_triple_le (stepZero_clearB_tail hps hw16 hVG₀ hGm₀ hBV hds hu_some hPref hState
      hfix hz0 hsp_lt hgen_w hk_w hw'_le hupd_cap hpref_le hPrefBat1 hG1 hH5
      hold_nd hold_mem hold_len hold_ec hold_at2 hmin6 hbuck6 hgen4 hst4
      hfr1 hfr2 hfr4 hfr5 hfr6)
    ⟨rfl,
      stepZeroPrepRegs_of_agree hR (fun i hi => by
        dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]),
      by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact r20,
      by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact r21,
      by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact r22,
      by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact r23,
      by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact r24,
      by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact r26⟩
    (fun _ _ h => h) ?_
  have hcbLen' : (bucketsCat (fun i => delErase u (if hi : i < L + 1 then x.hBuckets ⟨i, hi⟩ else [])) 0 (L + 1)).length = H_mid.m := hcbLen
  simp only [clearAuxGraphContract, dsClearBucketsContract,
    hcbLo, hcbHi, hcbB, Nat.sub_zero, hcbLen', hHmid_n, Expr.size, argsSize]
  omega

public section

/-- Execute Phase 1 (`dsStepZeroClearBody`), establishing `StepZeroClearPost`. -/
theorem stepZero_clear_triple {G₀ : MGraph} {impl : SparsifyImpl} {mMax w L q vCap eCap b k : ℕ}
    {us : List Update} {u : Update} {len updPtr heapStep : ℕ} {mem0 : ℕ → ℕ}
    {x : DynSpannerMeta L} {p : Program} {bs : StepZeroBases}
    (hps : HasStepZeroProcs impl p bs)
    (hw16 : 16 ≤ 2 ^ w) (hq : 1 ≤ q)
    (hVG₀ : G₀.IsValid) (hGm₀ : G₀.m ≤ mMax) (hBV : G₀.BatchIsValid us)
    (hds : ∀ u' ∈ us, isDelOrSplit u') (hu_some : us[k]? = some u)
    (hPref : ∀ s ≤ k, SnapInv G₀ L q mMax (canonicalSparsifyParams impl mMax).absorbTime
      (canonicalSparsify impl) us s)
    (hState : DynSpannerStateAt L vCap eCap b mem0 x
      (runState (L := L) G₀ q (canonicalSparsify impl) us k))
    (hfix : b + dsFixedSize L vCap eCap ≤ heapStep) (hz0 : ZeroFrom mem0 heapStep)
    (hsp :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let G' := st.G.applyUpdate u
      let H₀ := (initCore G' (canonicalSparsify impl)).1
      heapStep + dsStepZeroSpace impl mMax vCap eCap G' st.H H₀ len < 2 ^ w)
    (hgen_w :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      mem0 (b + dsGenOff) + 2 + (st.G.applyUpdate u).m < 2 ^ w)
    (hk_w : k + 1 < 2 ^ w)
    (hw'_le :
      let G' := (runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u
      G'.E.Nonempty →
        wordSize impl.cw (canonSparsifyInput (activeSubgraph G') (activeSubgraph G') idEmb) ≤ w)
    (hupd_le : updPtr + len ≤ heapStep)
    (hupd_foot : ∀ i < len, ¬ metaFoot b x (updPtr + i))
    (hupd_w : ∀ i < len, mem0 (updPtr + i) < 2 ^ w)
    (hupd_at : UpdateAt mem0 updPtr (runState (L := L) G₀ q (canonicalSparsify impl) us k).G u len)
    (hupd_cap : UpdateWithinCaps vCap eCap u) :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let G' := st.G.applyUpdate u
    let H_mid := st.H.applyBatch (restrictUpdate u st.H)
    Triple w p
      (fun st0 => st0.mem = mem0 ∧ StepZeroPrepRegs b updPtr heapStep L vCap eCap st0.regs)
      (dsStepZeroClearBody bs.bAux bs.bZAux bs.bPref bs.bPhase bs.bCB bs.bClrA)
      (normalPost (StepZeroClearPost G₀ impl mMax w L q vCap eCap b k us u len updPtr heapStep mem0 x))
      (fun _ => 1320 * len + 605 * H_mid.m + 30 * G'.n + 90 * (L + 1) + 1030) := by
  intro st G' H_mid st0 ω hpre
  dsimp only [dsStepZeroClearBody]
  refine runs_start_le ?_
  refine runs_seq_triple_le (stepZero_clearA_triple hps hw16 hq hVG₀ hBV hds hu_some hPref
    hState hfix hsp hgen_w hupd_le hupd_foot hupd_w hupd_at hupd_cap) hpre ?_
  intro stM hM
  refine runs_triple_le (stepZero_clearB_triple hps hw16 hVG₀ hGm₀ hBV hds hu_some hPref
    hState hfix hz0 hsp hgen_w hk_w hw'_le hupd_cap) hM (fun _ _ h => h) (by
      dsimp only [H_mid, G', st]; omega)

end

end MinCostFlow.DynSpanner.Program
