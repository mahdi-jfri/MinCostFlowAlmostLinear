module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepZeroPrep
import WordRAM.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Verification of the `j = 0` restart branch (`DynSpannerStepZero`)

Completes the verification of `dsStepZeroStmt` (the level-0 full-restart branch of Algorithm 6,
Theorem 8.2, page 64):

* `stepZero_emit_triple`: executes Phase 3 (`dsStepZeroEmitBody`), writing `D = E(H₀)`,
  `U_H = uhPref ++ uhDel' ++ uhIns'`, and the 5-word step header at `heapStep`, and returning
  `retFinal`.
* `dsStepZero_meetsContract`: chains Phases 0, 1, `dsInitCoreStmt`, and Phase 3 to prove
  `MeetsContract w p (bs.bSZ + stepZeroIdx) (dsStepZeroContract …)` with postcondition
  `StepOutPost` plus heap-growth and generation-growth bounds.
* `dsStepZero_costBound`: paper-shape asymptotic cost corollary via `dsInitCore_initCostBound`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

private lemma idx_lt_mul_e {i n e m : ℕ} (hi : i < n) (he : e < m) : i * m + e < n * m :=
  calc i * m + e < i * m + m := Nat.add_lt_add_left he _
    _ = (i + 1) * m := by ring
    _ ≤ n * m := Nat.mul_le_mul_right _ hi

/-- Execute Phase 3 (`dsStepZeroEmitBody`) starting from `memCore`, emitting `D`, `U_H`, and the
5-word step header at `heapStep`, and returning `retFinal` with `dsStepZeroContract.post`. -/
private theorem stepZero_emit_triple {G₀ : MGraph} {impl : SparsifyImpl}
    {mMax w L q vCap eCap b k : ℕ} {us : List Update} {u : Update}
    {len updPtr heapStep prefWords retInit gOld : ℕ}
    {oldHEdges buck0 : List ℕ} {rev0 : ℕ → List ℕ}
    {mem0 memCore : ℕ → ℕ} {x : DynSpannerMeta L} {p : Program} {bs : StepZeroBases}
    (hps : HasStepZeroProcs impl p bs)
    (hw16 : 16 ≤ 2 ^ w) (hL1 : 1 ≤ L) (hq : 1 ≤ q)
    (hVG₀ : G₀.IsValid) (hGm₀ : G₀.m ≤ mMax) (hBV : G₀.BatchIsValid us)
    (hds : ∀ u' ∈ us, isDelOrSplit u') (hu_some : us[k]? = some u)
    (hPref : ∀ s ≤ k, SnapInv G₀ L q mMax (canonicalSparsifyParams impl mMax).absorbTime
      (canonicalSparsify impl) us s)
    (hj0 : chooseLevel L q (k + 1) = 0)
    (hState : DynSpannerStateAt L vCap eCap b mem0 x
      (runState (L := L) G₀ q (canonicalSparsify impl) us k))
    (hupd_cap : UpdateWithinCaps vCap eCap u)
    (hfix : b + dsFixedSize L vCap eCap ≤ heapStep)
    (hsp :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let G' := st.G.applyUpdate u
      let H₀ := (initCore G' (canonicalSparsify impl)).1
      heapStep + dsStepZeroSpace impl mMax vCap eCap G' st.H H₀ len < 2 ^ w)
    (hgen_rel : gOld = mem0 (b + dsGenOff) + 1)
    (hpref_le : prefWords ≤ len)
    (hret_ge : heapStep + 5 + len + oldHEdges.length ≤ retInit)
    (hret_le :
      let G' := (runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u
      retInit ≤ heapStep + 5 + len + oldHEdges.length +
        dsInitCoreSpaceBound impl mMax vCap eCap G')
    (hzCore : ZeroFrom memCore retInit)
    (hHdrCore :
      memCore (b + dsQOff) = q ∧ memCore (b + dsTOff) = k + 1 ∧
      memCore (b + dsLOff) = L ∧ memCore (b + dsVCapOff) = vCap ∧ memCore (b + dsECapOff) = eCap ∧
      memCore (b + dsGenOff) = gOld + 1 +
        ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u).m ∧
      memCore (dsDomGenBase b L vCap eCap) = gOld + 1)
    (hGraphsCore :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let G' := st.G.applyUpdate u
      let H₀ := (initCore G' (canonicalSparsify impl)).1
      DynGraphAt memCore (dsGPtr b) vCap eCap G' ∧
      DynGraphAt memCore (dsHPtr b vCap eCap) vCap eCap H₀ ∧
      DynGraphAt memCore (dsAuxPtr b vCap eCap) vCap eCap emptyMGraph)
    (hCoreArrays :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let G' := st.G.applyUpdate u
      let core := initCore G' (canonicalSparsify impl)
      let H₀ := core.1
      let Pi₀ := core.2.1
      let heapInit := heapStep + 5 + len + oldHEdges.length
      (∀ e < eCap, (memCore (dsMinHBase b vCap eCap + e) = 0 ↔ e ∉ H₀.E) ∧
        (e ∈ H₀.E → memCore (dsMinHBase b vCap eCap + e) = 1)) ∧
      IsDoublyLinkedList memCore (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
        (dsHHeadBase b vCap eCap) eCap buck0 ∧
      memCore (dsHDegDummyBase b L vCap eCap) = buck0.length ∧
      (∀ e, e ∈ buck0 ↔ e ∈ H₀.E) ∧
      (∀ i : Fin (L + 1), 0 < i.1 →
        IsDoublyLinkedList memCore (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
          (dsHHeadBase b vCap eCap + i.1) eCap [] ∧
        memCore (dsHDegDummyBase b L vCap eCap + i.1) = 0 ∧
        memCore (dsDomGenBase b L vCap eCap + i.1) = 0 ∧
        (∀ e < eCap, memCore (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) ≤ memCore (b + dsGenOff)) ∧
        (∀ v < vCap, memCore (dsRevGenBase b L vCap eCap + i.1 * vCap + v) ≤ memCore (b + dsGenOff))) ∧
      (∀ e < eCap, memCore (dsEdgeDomGenBase b L vCap eCap + e) ≤ memCore (b + dsGenOff)) ∧
      (∀ e < eCap, (0 < memCore (dsDomGenBase b L vCap eCap) ∧
        memCore (dsEdgeDomGenBase b L vCap eCap + e) = memCore (dsDomGenBase b L vCap eCap)) ↔
          e ∈ G'.E) ∧
      (∀ e ∈ G'.E, let ptr := memCore (dsPiPtrBase b L vCap eCap + e)
        MWalkAt memCore ptr (Pi₀ e) ∧ heapInit ≤ ptr ∧ ptr + (mWalkEncode (Pi₀ e)).length ≤ retInit) ∧
      (∀ v < vCap, memCore (dsRevGenBase b L vCap eCap + v) ≤ memCore (b + dsGenOff) ∧
        (rev0 v).Nodup ∧ (∀ e, e ∈ rev0 v ↔ e ∈ G'.E ∧ v ∈ H₀.walkVertices (G'.tail e) (Pi₀ e)) ∧
        (if 0 < memCore (dsDomGenBase b L vCap eCap) ∧
            memCore (dsRevGenBase b L vCap eCap + v) = memCore (dsDomGenBase b L vCap eCap)
         then LinkedListIn (fun a => heapInit ≤ a ∧ a < retInit) memCore
                (memCore (dsRevHeadBase b L vCap eCap + v)) (rev0 v)
         else rev0 v = [])) ∧
      (∀ i : Fin (L + 1), memCore (dsSGenBase b L vCap eCap + i.1) = 0 ∧
        ∀ v < vCap, memCore (dsVSGenBase b L vCap eCap + i.1 * vCap + v) ≤ memCore (b + dsGenOff)) ∧
      (∀ v < vCap, memCore (dsSBitBase b L vCap eCap + v) = 0 ∧
        memCore (dsVStampBase b L vCap eCap + v) ≤ memCore (b + dsGenOff)) ∧
      (∀ e < eCap, memCore (dsEStampBase b L vCap eCap + e) ≤ memCore (b + dsGenOff) ∧
        memCore (dsKeptStampBase b L vCap eCap + e) ≤ memCore (b + dsGenOff)))
    (hOldE :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let H_mid := st.H.applyBatch (restrictUpdate u st.H)
      oldHEdges.Nodup ∧ (∀ e, e ∈ oldHEdges ↔ e ∈ H_mid.E) ∧ oldHEdges.length = H_mid.m ∧
      ListAt memCore (heapStep + 5 + len) oldHEdges)
    (hPrefBatC :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      BatchBodyAt memCore (heapStep + 5) st.H (restrictUpdate u st.H) prefWords)
    (hEStampC :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let H_mid := st.H.applyBatch (restrictUpdate u st.H)
      ∀ e < eCap, memCore (dsEStampBase b L vCap eCap + e) = gOld ↔ e ∈ H_mid.E)
    (hFrameC : ∀ a < heapStep, ¬ metaFoot b x a → memCore a = mem0 a)
    (hgOld_w : gOld < 2 ^ w) :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let G' := st.G.applyUpdate u
    let H_mid := st.H.applyBatch (restrictUpdate u st.H)
    let H₀ := (initCore G' (canonicalSparsify impl)).1
    Triple w p
      (fun stC => stC.mem = memCore ∧ StepZeroPrepRegs b updPtr heapStep L vCap eCap stC.regs ∧
        stC.regs 20 = len ∧ stC.regs 21 = heapStep + 5 ∧ stC.regs 22 = prefWords ∧
        stC.regs 23 = H_mid.m ∧ stC.regs 24 = heapStep + 5 + len ∧
        stC.regs 26 = gOld ∧ stC.regs 28 = retInit)
      (dsStepZeroEmitBody bs.bAux bs.bZAux)
      (fun o st' => ∃ ret, o = .returned ret ∧
        StepOutPost G₀ L q vCap eCap b k impl us u mem0 x heapStep st'.mem ret ∧
        heapStep + 5 ≤ ret ∧
        ret ≤ heapStep + dsStepZeroSpace impl mMax vCap eCap G' st.H H₀ len ∧
        st'.mem (b + dsGenOff) ≤ mem0 (b + dsGenOff) + 2 + G'.m ∧
        st'.mem (heapStep + 2) ≤ len + 4 * (step st u (canonicalSparsify impl)).UH.length)
      (fun _ => 30 * len + 70 * H_mid.m + 250 * H₀.m + 250) := by
  intro st G' H_mid H₀ stC ω ⟨hmC, hR, r20, r21, r22, r23, r24, r26, r28⟩
  rcases stC with ⟨mem_s, regsC, posC⟩
  dsimp only at hmC hR r20 r21 r22 r23 r24 r26 r28 ⊢
  subst mem_s
  obtain ⟨_, _, hU_k⟩ := batchIsValid_take us G₀ k hBV hds
  obtain ⟨_, hdu⟩ := hU_k u hu_some
  have hltF := stepZero_fixed_lt b L vCap eCap
  have hG_top : dsGPtr b + dynGraphSize vCap eCap ≤ b + dsFixedSize L vCap eCap := hltF.2.1.2
  have hH_top : dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ b + dsFixedSize L vCap eCap := hltF.2.2.1.2
  have hES_top : dsEStampBase b L vCap eCap + eCap ≤ b + dsFixedSize L vCap eCap := by
    have := (stepZero_fixed_order b L vCap eCap).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    exact (this.1.symm ▸ (this.2.1 ▸ Nat.le_add_right _ _)).trans (this.2.2 ▸ Nat.le_add_right _ _)
  have hGen_lt : b + dsGenOff < b + dsFixedSize L vCap eCap := (hltF.1 dsGenOff (by decide)).2
  have hHmid_m_le : H_mid.m ≤ st.H.m := by
    have hE := mid_E_delSet hdu st.H
    have hsub : H_mid.E ⊆ st.H.E := by
      rw [hE]; cases u with
      | insert _ _ _ => exact hdu.elim
      | delete _ => exact Finset.erase_subset _ _
      | split _ _ _ _ => exact Finset.Subset.rfl
    exact Finset.card_le_card hsub
  have hsp' : heapStep + dsStepZeroSpace impl mMax vCap eCap G' st.H H₀ len < 2 ^ w := hsp
  have hret_le' : retInit ≤ heapStep + 5 + len + oldHEdges.length +
      dsInitCoreSpaceBound impl mMax vCap eCap G' := hret_le
  have hfix_w : b + dsFixedSize L vCap eCap < 2 ^ w := by
    dsimp only [dsStepZeroSpace] at hsp'; omega
  have hret_bound : retInit + H₀.m + len + 2 * H_mid.m + 4 * H₀.m < 2 ^ w := by
    have hold_len' : oldHEdges.length = H_mid.m := hOldE.2.2.1
    dsimp only [dsStepZeroSpace] at hsp'; omega
  have r2 := hR.2.2.1; have r8 := hR.2.2.2.2.2.2.2.2.1; have r9 := hR.2.2.2.2.2.2.2.2.2.1
  have r17 := hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have r18 := hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have r19 := hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  clear hR
  rcases hGraphsCore with ⟨hGC, hHC, hAuxC⟩
  rcases hOldE with ⟨hold_nd, hold_mem, hold_len, hold_at⟩
  rcases hHC.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨dL, hdL_len, hdL_nd, hdL_mem, hdL_at, _⟩
  have hold_len' : oldHEdges.length = H_mid.m := hold_len
  have hdL_len' : dL.length = H₀.m := hdL_len
  have hH₀_ec : H₀.m ≤ eCap := by
    have hsub : H₀.E ⊆ Finset.range eCap := fun e he => Finset.mem_range.mpr (hHC.2.2.1 e he)
    simpa [MGraph.m] using Finset.card_le_card hsub
  have hhEList_top : dgEListBase (dsHPtr b vCap eCap) vCap eCap + eCap ≤ b + dsFixedSize L vCap eCap := by
    have : dgEListBase (dsHPtr b vCap eCap) vCap eCap + eCap ≤ dsHPtr b vCap eCap + dynGraphSize vCap eCap := by
      simp only [dgEListBase, dynGraphSize]; omega
    exact this.trans hH_top
  have hhPres_top : dgEPresBase (dsHPtr b vCap eCap) vCap + eCap ≤ b + dsFixedSize L vCap eCap := by
    have : dgEPresBase (dsHPtr b vCap eCap) vCap + eCap ≤ dsHPtr b vCap eCap + dynGraphSize vCap eCap := by
      simp only [dgEPresBase, dynGraphSize]; omega
    exact this.trans hH_top
  have hhEList_lt : dgEListBase (dsHPtr b vCap eCap) vCap eCap + H₀.m < 2 ^ w := by omega
  have hhPres_lt : dgEPresBase (dsHPtr b vCap eCap) vCap + eCap < 2 ^ w := by omega
  have hdgm_off : dgMOff = 3 := rfl
  have hhM_lt : dsHPtr b vCap eCap + dgMOff < b + dsFixedSize L vCap eCap := by
    have : dsHPtr b vCap eCap + dgMOff < dsHPtr b vCap eCap + dynGraphSize vCap eCap := by
      simp only [dgMOff, dynGraphSize]; omega
    exact lt_of_lt_of_le this hH_top
  dsimp only [dsStepZeroEmitBody]
  refine runs_start_le ?_
  -- 1. `r29 := memCore[hPtr + dgMOff] = H₀.m`
  refine runs_seq_assign_le (v := H₀.m)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r9)
      (Expr.eval_const (by rw [hdgm_off]; omega)) (by omega))
      hHC.2.2.2.2.2.2.1) ?_
  -- 2. Copy `dL` from `hEList` to `dPtr = retInit`
  refine runs_seq_call_le (vs := [dgEListBase (dsHPtr b vCap eCap) vCap eCap, retInit, H₀.m])
    (dsCopyWords_meetsContract (w := w) (n := H₀.m) hps.hpAux)
    (by simp [evalArgs, Expr.eval, r19, r28])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> omega)
    ⟨dgEListBase (dsHPtr b vCap eCap) vCap eCap, retInit, rfl, hw16, hhEList_lt, by omega,
      by unfold IvlDisj; omega⟩ ?_
  rintro _ memE1 _ ⟨_, _, hEqC1, _, hcpD, hfrE1⟩
  simp only [List.cons.injEq, and_true] at hEqC1
  rcases hEqC1 with ⟨rfl, rfl⟩
  -- 3. `uhPtr := retInit + H₀.m`, copy `prefWords` from `heapStep + 5` to `uhPtr`
  set uhPtr := retInit + H₀.m
  refine runs_seq_assign_le (v := uhPtr)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r28])) (Expr.eval_reg_of_eq (by simp)) (by omega)) ?_
  refine runs_seq_call_le (vs := [heapStep + 5, uhPtr, prefWords])
    (dsCopyWords_meetsContract (w := w) (n := prefWords) hps.hpAux)
    (by simp [evalArgs, Expr.eval, r21, r22])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> omega)
    ⟨heapStep + 5, uhPtr, rfl, hw16, by omega, by omega, by unfold IvlDisj; omega⟩ ?_
  rintro _ memE2 _ ⟨_, _, hEqC2, _, hcpP, hfrE2⟩
  simp only [List.cons.injEq, and_true] at hEqC2
  rcases hEqC2 with ⟨rfl, rfl⟩
  -- 4. `r32 := uhPtr + prefWords`, call `dsListDelRecs`
  refine runs_seq_assign_le (v := uhPtr + prefWords)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp [r22])) (by omega)) ?_
  have hold_at2 : ListAt memE2 (heapStep + 5 + len) oldHEdges :=
    hold_at.congr fun a h1 h2 =>
      (hfrE2 a (Or.inl (by omega))).trans (hfrE1 a (Or.inl (by omega)))
  have hold_ec : ∀ e ∈ oldHEdges, e < eCap := fun e he => by
    have hE := mid_E_delSet hdu st.H
    have heH : e ∈ st.H.E := by
      have heM := (hold_mem e).mp he
      rw [hE] at heM
      cases u with
      | insert _ _ _ => exact hdu.elim
      | delete _ => exact Finset.mem_of_mem_erase heM
      | split _ _ _ _ => exact heM
    exact hState.2.2.2.2.2.2.2.2.2.2.1 e (hState.2.2.2.2.2.2.2.1 heH)
  let cDel : LDRCtx :=
    { w := w, eCap := eCap, X := H₀.E, es := oldHEdges, listPtr := heapStep + 5 + len,
      pres := dgEPresBase (dsHPtr b vCap eCap) vCap, out := uhPtr + prefWords, mem0 := memE2,
      hw16 := hw16, hlB := by omega, hpB := hhPres_lt, hoB := by omega,
      dOL := by unfold IvlDisj; omega,
      dOP := by unfold IvlDisj; omega,
      hes := hold_at2, hesC := hold_ec,
      hpres := fun e he => by
        rw [hfrE2 _ (Or.inl (by omega))]; dsimp only
        rw [hfrE1 _ (Or.inl (by omega))]
        exact hHC.2.2.2.2.2.2.2.2.2.2.2.1 e he }
  refine runs_seq_call_le (vs := [heapStep + 5 + len, H_mid.m, dgEPresBase (dsHPtr b vCap eCap) vCap,
      uhPtr + prefWords])
    (dsListDelRecs_meetsContract cDel hps.hpZAux)
    (by simp [evalArgs, Expr.eval, r24, r23, r18])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> omega)
    ⟨by simp [cDel, hold_len'], rfl⟩ ?_
  rintro delCnt memE3 _ ⟨hdelCnt, hDelWords3, hfrE3⟩
  have hdel_le : delCnt ≤ H_mid.m := by
    rw [hdelCnt]; exact hold_len' ▸ delList_length_le H₀.E oldHEdges
  -- 5. `r34 := uhPtr + prefWords + 2 * delCnt`, call `dsStampInsRecs`
  refine runs_seq_assign_le (v := uhPtr + prefWords + 2 * delCnt)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega))
      (by omega)) ?_
  have hdL_at3 : ListAt memE3 retInit dL := fun i hi =>
    (hfrE3 _ (Or.inl (by dsimp only [cDel]; omega))).trans
      ((hfrE2 _ (Or.inl (by omega))).trans ((hcpD i (hdL_len' ▸ hi)).trans (hdL_at i hi)))
  have hG3 : DynGraphAt memE3 (dsGPtr b) vCap eCap G' :=
    dynGraphAt_of_agree hGC fun a h1 h2 =>
      (hfrE3 a (Or.inl (by dsimp only [cDel]; omega))).trans
        ((hfrE2 a (Or.inl (by omega))).trans (hfrE1 a (Or.inl (by omega))))
  have hH₀_sub_G' : H₀.E ⊆ G'.E := by
    have hG'val : G'.IsValid := by
      have hk := hPref k le_rfl
      obtain ⟨_, _, hUk⟩ := batchIsValid_take us G₀ k hBV hds
      exact isValid_applyUpdate_of_delOrSplit hState.2.2.2.2.1 (hk.G_eq ▸ (hUk u hu_some).1) hdu
    have hG'm : G'.m ≤ mMax := by
      have hk := hPref k le_rfl
      obtain ⟨hBVk, hdsk, _⟩ := batchIsValid_take us G₀ k hBV hds
      exact le_trans (Finset.card_le_card (Finset.Subset.trans (E_applyUpdate_subset hdu)
        (hk.G_eq ▸ (batch_delOrSplit_invariants (us.take k) G₀ hVG₀ hBVk hdsk).2.1))) hGm₀
    exact (initCore_spec (canonicalSparsify_spec_absorb impl mMax) hG'val hG'm).2.1.2.1
  let cIns : SIRCtx :=
    { w := w, vCap := vCap, eCap := eCap, G := G', X := H_mid.E, es := dL,
      listPtr := retInit, stampBase := dsEStampBase b L vCap eCap, stampVal := gOld,
      gPtr := dsGPtr b, out := uhPtr + prefWords + 2 * delCnt, mem0 := memE3,
      hw16 := hw16, hlB := by omega, hsB := by omega, hsvB := hgOld_w, hgB := by omega,
      hoB := by omega,
      dOL := by unfold IvlDisj; omega,
      dOS := by unfold IvlDisj; omega,
      dOG := by unfold IvlDisj; omega,
      hes := hdL_at3, hesG := fun e he => hH₀_sub_G' ((hdL_mem e).mp he),
      hG := hG3,
      hstamp := fun e he => by
        rw [hfrE3 _ (Or.inl (by dsimp only [cDel]; omega))]; dsimp only
        rw [hfrE2 _ (Or.inl (by omega))]; dsimp only
        rw [hfrE1 _ (Or.inl (by omega))]
        exact hEStampC e he }
  refine runs_seq_call_le (vs := [retInit, H₀.m, dsEStampBase b L vCap eCap, gOld, dsGPtr b,
      uhPtr + prefWords + 2 * delCnt])
    (dsStampInsRecs_meetsContract cIns hps.hpOps hps.hpZAux)
    (by simp [evalArgs, Expr.eval, r28, r17, r26, r8])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨by simp [cIns, hdL_len'], rfl⟩ ?_
  rintro insCnt memE4 _ ⟨hinsCnt, hInsWords4, hfrE4⟩
  have hins_le : insCnt ≤ H₀.m := by
    rw [hinsCnt]; exact hdL_len' ▸ insList_length_le H_mid.E dL
  -- 6. Compute `prefCnt`, `uhLen`, `uhWords`, `retFinal`, store 5-word header, return `retFinal`
  set prefCnt := if prefWords = 0 then 0 else 1
  have hpc_le : prefCnt ≤ prefWords := by dsimp only [prefCnt]; split_ifs <;> omega
  set uhLen := prefCnt + delCnt + insCnt
  set uhWords := prefWords + 2 * delCnt + 4 * insCnt
  set retFinal := uhPtr + uhWords
  have hfrE4' : ∀ a, a < uhPtr + prefWords + 2 * delCnt ∨ retFinal ≤ a → memE4 a = memE3 a :=
    fun a ha => hfrE4 a (ha.imp id fun h => by dsimp only [cIns, retFinal, uhWords] at h ⊢; omega)
  have hfrE3' : ∀ a, a < uhPtr + prefWords ∨ uhPtr + prefWords + 2 * delCnt ≤ a → memE3 a = memE2 a :=
    fun a ha => hfrE3 a (ha.imp id fun h => by dsimp only [cDel]; exact h)
  have hfrE2' : ∀ a, a < uhPtr ∨ uhPtr + prefWords ≤ a → memE2 a = memE1 a := hfrE2
  have hfrE1' : ∀ a, a < retInit ∨ uhPtr ≤ a → memE1 a = memCore a := hfrE1
  have hF_from_E4 : ∀ memFinal : ℕ → ℕ,
      (∀ a, a < heapStep ∨ heapStep + 5 ≤ a → memFinal a = memE4 a) →
      (memFinal heapStep = uhPtr ∧ memFinal (heapStep + 1) = uhLen ∧
        memFinal (heapStep + 2) = uhWords ∧ memFinal (heapStep + 3) = retInit ∧
        memFinal (heapStep + 4) = H₀.m) →
      StepOutPost G₀ L q vCap eCap b k impl us u mem0 x heapStep memFinal retFinal ∧
      heapStep + 5 ≤ retFinal ∧
      retFinal ≤ heapStep + dsStepZeroSpace impl mMax vCap eCap G' st.H H₀ len ∧
      memFinal (b + dsGenOff) ≤ mem0 (b + dsGenOff) + 2 + G'.m ∧
      memFinal (heapStep + 2) ≤ len + 4 * (step st u (canonicalSparsify impl)).UH.length := by
    intro memFinal hF_ne hHdrF
    have hF_lt_ret : ∀ a < retInit, a < heapStep ∨ heapStep + 5 ≤ a → memFinal a = memCore a :=
      fun a ha1 ha2 => (hF_ne a ha2).trans
        ((hfrE4' a (Or.inl (by omega))).trans
          ((hfrE3' a (Or.inl (by omega))).trans
            ((hfrE2' a (Or.inl (by omega))).trans (hfrE1' a (Or.inl ha1)))))
    have hzFinal : ZeroFrom memFinal retFinal := fun a ha => by
      rw [hF_ne a (Or.inr (by omega)), hfrE4' a (Or.inr ha), hfrE3' a (Or.inr (by omega)),
        hfrE2' a (Or.inr (by omega)), hfrE1' a (Or.inr (by omega))]
      exact hzCore a (by omega)
    have hPrefBatF : BatchBodyAt memFinal uhPtr st.H (restrictUpdate u st.H) prefWords :=
      hPrefBatC.copy fun i hi => by
        rw [hF_ne _ (Or.inr (by omega)), hfrE4' _ (Or.inl (by omega)),
          hfrE3' _ (Or.inl (by omega)), hcpP i hi]; dsimp only
        rw [hfrE1' _ (Or.inl (by omega))]
    have hDelWordsF : ListAt memFinal (uhPtr + prefWords) (delWords H₀.E oldHEdges) :=
      hDelWords3.congr fun a h1 h2 => by
        dsimp only [cDel] at h1 h2
        have hdw := delWords_length H₀.E oldHEdges
        have hdc : delCnt = (delList H₀.E oldHEdges).length := hdelCnt
        rw [hF_ne a (Or.inr (by omega)), hfrE4' a (Or.inl (by omega))]
    have hInsWordsF : ListAt memFinal (uhPtr + prefWords + 2 * delCnt) (insWords G' H_mid.E dL) :=
      hInsWords4.congr fun a h1 _ => by
        dsimp only [cIns] at h1
        exact hF_ne a (Or.inr (by omega))
    have hdL_atF : ListAt memFinal retInit dL :=
      hdL_at3.congr fun a h1 h2 =>
        (hF_ne a (Or.inr (by omega))).trans (hfrE4' a (Or.inl (by omega)))
    exact stepZero_rebuild_post hVG₀ hL1 hq hGm₀ hBV hds hu_some hPref hj0
      hState hupd_cap hfix
      ⟨by omega, hret_ge, rfl, by rw [hdL_len'], rfl, rfl, rfl, hret_le, rfl, hpref_le⟩
      ⟨(hF_lt_ret _ (by omega) (Or.inl (by omega))).trans hHdrCore.2.2.2.2.2.1, hgen_rel⟩
      ⟨hHdrF.1, hHdrF.2.1, hHdrF.2.2.1, hHdrF.2.2.2.1, hdL_len'.symm ▸ hHdrF.2.2.2.2⟩
      (fun a ha1 ha2 => hF_lt_ret a (by omega) (Or.inl (by omega)))
      (fun a ha1 ha2 => hF_lt_ret a ha2 (Or.inr (by omega)))
      (fun a ha hnf => (hF_lt_ret a (by omega) (Or.inl ha)).trans (hFrameC a ha hnf))
      hzFinal hHdrCore ⟨hGC, hHC, hAuxC⟩ hCoreArrays
      ⟨hold_nd, hold_mem, hold_len⟩ ⟨hdL_nd, hdL_mem, hdL_len, hdL_atF⟩
      ⟨hPrefBatF, hdelCnt, hDelWordsF, hinsCnt, hInsWordsF⟩
  have hcond_step : ∀ st4 : State,
      st4.mem = memE4 → st4.regs 2 = heapStep → st4.regs 22 = prefWords →
      st4.regs 28 = retInit → st4.regs 29 = H₀.m → st4.regs 31 = uhPtr →
      st4.regs 33 = delCnt → st4.regs 35 = insCnt →
      ∃ o st' c, Runs w p ω
        (.cond (.reg 22) (.assign 36 (.const 1)) (.assign 36 (.const 0)) ;;
         .assign 37 (.bin .add (.bin .add (.reg 36) (.reg 33)) (.reg 35)) ;;
         .assign 38 (.bin .add (.bin .add (.reg 22) (.bin .mul (.const 2) (.reg 33)))
           (.bin .mul (.const 4) (.reg 35))) ;;
         .assign 39 (.bin .add (.reg 31) (.reg 38)) ;;
         .store (.reg 2) (.reg 31) ;;
         .store (.bin .add (.reg 2) (.const 1)) (.reg 37) ;;
         .store (.bin .add (.reg 2) (.const 2)) (.reg 38) ;;
         .store (.bin .add (.reg 2) (.const 3)) (.reg 28) ;;
         .store (.bin .add (.reg 2) (.const 4)) (.reg 29) ;;
         .ret (.reg 39)) st4 o st' c ∧
        (∃ ret, o = .returned ret ∧
          StepOutPost G₀ L q vCap eCap b k impl us u mem0 x heapStep st'.mem ret ∧
          heapStep + 5 ≤ ret ∧
          ret ≤ heapStep + dsStepZeroSpace impl mMax vCap eCap G' st.H H₀ len ∧
          st'.mem (b + dsGenOff) ≤ mem0 (b + dsGenOff) + 2 + G'.m ∧
          st'.mem (heapStep + 2) ≤ len + 4 * (step st u (canonicalSparsify impl)).UH.length) ∧ c ≤ 80 := by
    intro st4 hm4 q2 q22 q28 q29 q31 q33 q35
    have hpc_tr : Triple w p (fun s => s = st4)
        (.cond (.reg 22) (.assign 36 (.const 1)) (.assign 36 (.const 0)))
        (normalPost fun s => s.mem = memE4 ∧ s.regs 2 = heapStep ∧ s.regs 22 = prefWords ∧
          s.regs 28 = retInit ∧ s.regs 29 = H₀.m ∧ s.regs 31 = uhPtr ∧
          s.regs 33 = delCnt ∧ s.regs 35 = insCnt ∧ s.regs 36 = prefCnt)
        (fun _ => 10) := by
      intro s ω' hs; subst hs
      refine runs_start_le ?_
      refine runs_cond_le (Expr.eval_reg_of_eq q22) (fun hne => ?_) (fun hz => ?_)
      · refine runs_assign_le (v := 1) (Expr.eval_const (by omega))
          ⟨hm4, by simp [q2], by simp [q22], by simp [q28], by simp [q29], by simp [q31],
            by simp [q33], by simp [q35], by simp [prefCnt, hne]⟩ (by simp [Expr.size])
      · refine runs_assign_le (v := 0) (Expr.eval_const (by omega))
          ⟨hm4, by simp [q2], by simp [q22], by simp [q28], by simp [q29], by simp [q31],
            by simp [q33], by simp [q35], by simp [prefCnt, hz]⟩ (by simp [Expr.size])
    refine runs_start_le ?_
    refine runs_seq_triple_le hpc_tr rfl ?_
    rintro st5 ⟨hm5, s2, s22, s28, s29, s31, s33, s35, s36⟩
    refine runs_seq_assign_le (v := uhLen)
      (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq s36) (Expr.eval_reg_of_eq s33)
          (by omega))
        (Expr.eval_reg_of_eq s35) (by omega)) ?_
    refine runs_seq_assign_le (v := uhWords)
      (Expr.eval_add
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [s22]))
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [s33])) (by omega))
          (by omega))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [s35])) (by omega))
        (by omega)) ?_
    refine runs_seq_assign_le (v := retFinal)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [s31])) (Expr.eval_reg_of_eq (by simp))
        (by omega)) ?_
    refine runs_seq_store_le (x := heapStep) (v := uhPtr)
      (Expr.eval_reg_of_eq (by simp [s2])) (Expr.eval_reg_of_eq (by simp [s31])) ?_
    refine runs_seq_store_le (x := heapStep + 1) (v := uhLen)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [s2])) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq (by simp)) ?_
    refine runs_seq_store_le (x := heapStep + 2) (v := uhWords)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [s2])) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq (by simp)) ?_
    refine runs_seq_store_le (x := heapStep + 3) (v := retInit)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [s2])) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq (by simp [s28])) ?_
    refine runs_seq_store_le (x := heapStep + 4) (v := H₀.m)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [s2])) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq (by simp [s29])) ?_
    set memFinal := Function.update (Function.update (Function.update (Function.update
      (Function.update st5.mem heapStep uhPtr) (heapStep + 1) uhLen)
      (heapStep + 2) uhWords) (heapStep + 3) retInit) (heapStep + 4) H₀.m
    have hF_ne : ∀ a, a < heapStep ∨ heapStep + 5 ≤ a → memFinal a = memE4 a := fun a ha => by
      dsimp only [memFinal]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), hm5]
    have hHdrF : memFinal heapStep = uhPtr ∧ memFinal (heapStep + 1) = uhLen ∧
        memFinal (heapStep + 2) = uhWords ∧ memFinal (heapStep + 3) = retInit ∧
        memFinal (heapStep + 4) = H₀.m := by
      dsimp only [memFinal]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; simp
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]; simp
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; simp
      · rw [Function.update_of_ne (by omega)]; simp
      · simp
    refine runs_ret_le (v := retFinal) (Expr.eval_reg_of_eq (by simp))
      ⟨retFinal, rfl, hF_from_E4 memFinal hF_ne hHdrF⟩ ?_
    simp only [Expr.size_const, Expr.size_reg, Expr.size_bin]; omega
  refine (fun ⟨o, st', c', hrun, hpost, hc'⟩ => ⟨o, st', c', hrun, hpost, ?_⟩)
    (hcond_step _ rfl (by simp [r2]) (by simp [r22]) (by simp [r28])
      (by simp) (by simp) (by simp) (by simp))
  simp only [dsCopyWordsContract, dsListDelRecsContract, dsStampInsRecsContract, cDel, cIns,
    hold_len', hdL_len', Expr.size, argsSize]
  omega

public section

/-- `dsStepZeroStmt` meets `dsStepZeroContract`: the level-0 restart branch of Algorithm 6
(Theorem 8.2, page 64) establishes `StepOutPost`, bounds the allocated heap by
`dsStepZeroSpace`, bounds the generation counter growth by `2 + G'.m`, and runs within
`dsStepZeroCost` steps. -/
theorem dsStepZero_meetsContract {G₀ : MGraph} {impl : SparsifyImpl}
    {mMax w L q vCap eCap b k : ℕ} {us : List Update} {u : Update} {len : ℕ}
    {x : DynSpannerMeta L} {p : Program} {bs : StepZeroBases}
    (hps : HasStepZeroProcs impl p bs) :
    MeetsContract w p (bs.bSZ + stepZeroIdx)
      (dsStepZeroContract G₀ impl mMax w L q vCap eCap b k us u len x) := by
  refine meetsContract_of_runs
    (hps.hpSZ.get (i := stepZeroIdx) (by simp [stepZeroProcs, stepZeroIdx])) ?_
  rintro args mem0 pos ω _ ⟨updPtr, heapStep, rfl, hw16, hL1, hq1, hVG₀, hGm₀, hBV, hds, hu_some,
    hj0, hPref, hState, hfix, hfoot_lt, hz0, hsp, hgen_w, hk_w, hw'_le, hupd_le, hupd_foot,
    hupd_w, hupd_at, hupd_cap⟩
  set st := runState (L := L) G₀ q (canonicalSparsify impl) us k
  set G' := st.G.applyUpdate u
  set H_mid := st.H.applyBatch (restrictUpdate u st.H)
  set H₀ := (initCore G' (canonicalSparsify impl)).1
  set gOld := mem0 (b + dsGenOff) + 1
  have hsp' : heapStep + dsStepZeroSpace impl mMax vCap eCap G' st.H H₀ len < 2 ^ w := hsp
  have hfix_w : b + dsFixedSize L vCap eCap < 2 ^ w := by
    dsimp only [dsStepZeroSpace] at hsp'; omega
  have hHmid_m_le : H_mid.m ≤ st.H.m := by
    obtain ⟨_, _, hUk⟩ := batchIsValid_take us G₀ k hBV hds
    have hdu := (hUk u hu_some).2
    have hE := mid_E_delSet hdu st.H
    have hsub : H_mid.E ⊆ st.H.E := by
      rw [hE]; cases u with
      | insert _ _ _ => exact hdu.elim
      | delete _ => exact Finset.erase_subset _ _
      | split _ _ _ _ => exact Finset.Subset.rfl
    exact Finset.card_le_card hsub
  simp only [stepZeroProcs, stepZeroIdx, List.getElem_cons_zero]
  dsimp only [dsStepZeroStmt]
  refine runs_start_le ?_
  -- Phase 0: `dsStepZeroPrepStmt`
  refine runs_seq_triple_le (stepZero_prep_triple (updPtr := updPtr) (heapStep := heapStep)
      hw16 hfix_w hState.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    ⟨rfl, by simp [startState], by simp [startState], by simp [startState]⟩ ?_
  rintro st0 ⟨hm0, hR0⟩
  -- Phase 1: `dsStepZeroClearBody`
  refine runs_seq_triple_le (stepZero_clear_triple hps hw16 hq1 hVG₀ hGm₀ hBV hds hu_some
      hPref hState hfix hz0 hsp hgen_w hk_w hw'_le hupd_le hupd_foot hupd_w hupd_at hupd_cap)
    ⟨hm0, hR0⟩ ?_
  rintro st1 ⟨prefWords, oldHEdges, hR1, r20, r21, r22, r23, r24, r26, r27, hpref_le, hPreCore,
    hPrefBat1, hold_nd, hold_mem, hold_len, hold_at1, hQ1, hT1, hgen1, hPos1, hS1, hSBit1, hES1,
    hFr1⟩
  -- Phase 2: `dsInitCoreStmt [b, heapInit]`
  set heapInit := heapStep + 5 + len + H_mid.m
  have hheapInit_w : heapInit < 2 ^ w := by dsimp only [dsStepZeroSpace] at hsp'; omega
  refine runs_seq_call_le (vs := [b, heapInit])
    (dsInitCore_meetsContract hps.hpInit hps.hpOps hps.hpPhase hps.hpLW hps.hpRev hps.hpSpDyn
      hps.hpGuest hps.hpFwd hps.hpEmit hps.hpRevDyn hps.hpRevCore hps.hpRevPrim hps.hpBatch
      hps.hpEdge hps.hpGT hps.hpSort)
    (by simp [evalArgs, Expr.eval, hR1.1, r27])
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl <;> omega)
    hPreCore ?_
  rintro retInit memCore _ ⟨_, hEqCore, hret_ge, hret_le, hzCore, hgenC, hdomC, hvstC, hedLeC,
    hHC, hAuxC, hminC, ⟨buck0, hdll0C, hdeg0C, hbuck0C⟩, hedC, hpiC, ⟨rev0, hrevC⟩, hfrC⟩
  simp only [List.cons.injEq, and_true] at hEqCore
  rcases hEqCore with ⟨_, rfl⟩
  rw [hgen1] at hgenC hdomC
  obtain ⟨hGC, hHdrC, hPosC, hSC, hvSC, heSC, hEStampC, hFrameC⟩ :=
    stepZero_core_transfer hState.1 hState.2.1 hfix (by omega)
      hPreCore.choose_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hPreCore.choose_spec.2.2.2.2.2.2.2.1
      hPreCore.choose_spec.2.2.2.2.2.2.2.2.1
      hPreCore.choose_spec.2.2.2.2.2.2.2.2.2.1
      hQ1 hT1 hgenC hdomC hvstC hPos1 hS1 hSBit1 hES1 hFr1 hfrC
  have hhi_eq : heapInit = heapStep + 5 + len + oldHEdges.length := by
    dsimp only [heapInit]; rw [← hold_len]
  -- Phase 3: `dsStepZeroEmitBody`
  refine runs_triple_le (stepZero_emit_triple (w := w) hps hw16 hL1 hq1 hVG₀ hGm₀ hBV hds hu_some
      hPref hj0 hState hupd_cap hfix hsp rfl hpref_le (hhi_eq ▸ hret_ge) (hhi_eq ▸ hret_le)
      hzCore hHdrC ⟨hGC, hHC, hAuxC⟩
      ⟨hminC, hdll0C, hdeg0C, hbuck0C, hPosC, hedLeC, hedC, hhi_eq ▸ hpiC, hhi_eq ▸ hrevC,
        hSC, hvSC, heSC⟩
      ⟨hold_nd, hold_mem, hold_len, hold_at1.congr fun a h1 h2 =>
        hfrC a (initCore_frame_of_heap_lt (by omega) (by rw [hhi_eq]; exact h2))⟩
      (hPrefBat1.of_agree fun i hi => hfrC _ (initCore_frame_of_heap_lt (by omega) (by omega)))
      hEStampC hFrameC (by omega))
    ⟨rfl, stepZeroPrepRegs_of_agree hR1 (fun i hi => by dsimp only; rw [Function.update_of_ne (by omega)]),
      by simp [r20], by simp [r21], by simp [r22], by simp [r23], by simp [r24], by simp [r26],
      by simp⟩
    (fun o st' ⟨ret, hret, hP1, hP2, hP3, hP4, hP5⟩ => by
      rw [hret]; exact ⟨updPtr, heapStep, rfl, hP1, hP2, hP3, hP4, hP5⟩) ?_
  dsimp only [dsStepZeroContract, dsStepZeroCost, dsInitCoreContract, Expr.size, argsSize,
    st, G', H_mid, H₀] at hHmid_m_le ⊢
  omega

/-- Paper-shape cost bound for `dsStepZeroStmt` (Algorithm 6, level-0 restart, Theorem 8.2):
the explicit Word-RAM cost `dsStepZeroCost` is bounded by `(dsInitCostFactor impl + 1500)` times
the paper's initialization work plus `|E(H_old)| + len`. -/
theorem dsStepZero_costBound (impl : SparsifyImpl) (mMax L q : ℕ)
    {G' H_old : MGraph} (len : ℕ) (hG' : G'.IsValid) (hG'm : G'.m ≤ mMax) :
    let P := canonicalSparsifyParams impl mMax
    let H₀ := (initCore G' (canonicalSparsify impl)).1
    ((dsStepZeroCost impl mMax L G' H_old H₀ len : ℕ) : ℝ) ≤
      ((dsInitCostFactor impl + 1500 : ℕ) : ℝ) *
        (P.K_t * P.γ_t * (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) * P.γ_ℓ ^ 2) *
            (1 + Real.log (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2)) ^ max P.p_t 1 +
          (G'.n : ℝ) + (G'.m : ℝ) + (H_old.m : ℝ) + (H₀.m : ℝ) + (G'.m : ℝ) * P.γ_ℓ +
          (L : ℝ) + (len : ℝ) + 1) := by
  intro P H₀
  have hInit := dsInitCore_initCostBound impl mMax L q hG' hG'm
  dsimp only at hInit
  have hH_eq : (init G' L q (canonicalSparsify impl)).state.H.m = H₀.m := rfl
  rw [hH_eq] at hInit
  have hK1 : 0 ≤ P.K_t * P.γ_t * (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) * P.γ_ℓ ^ 2) *
      (1 + Real.log (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2)) ^ max P.p_t 1 := by
    have hK : 0 ≤ P.K_t := by dsimp only [P, canonicalSparsifyParams]; linarith [impl.hK_t]
    have hgt : 0 ≤ P.γ_t := le_trans zero_le_one (impl.hγ_t mMax)
    have hlog : (1 : ℝ) ≤ ((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2 := by
      linarith [Nat.cast_nonneg (α := ℝ) (activeSubgraph G').n, Nat.cast_nonneg (α := ℝ) G'.m]
    have hΛ : 0 ≤ (1 + Real.log (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2)) ^ max P.p_t 1 :=
      pow_nonneg (by linarith [Real.log_nonneg hlog]) _
    exact mul_nonneg (mul_nonneg (mul_nonneg hK hgt)
      (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))) hΛ
  have hgm_gl : 0 ≤ (G'.m : ℝ) * P.γ_ℓ :=
    mul_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one (impl.hγ_ℓ mMax))
  have hfac : (0 : ℝ) ≤ (dsInitCostFactor impl : ℝ) := Nat.cast_nonneg _
  dsimp only [dsStepZeroCost]
  push_cast at hInit ⊢
  nlinarith [Nat.cast_nonneg (α := ℝ) G'.n, Nat.cast_nonneg (α := ℝ) G'.m,
    Nat.cast_nonneg (α := ℝ) H_old.m, Nat.cast_nonneg (α := ℝ) H₀.m,
    Nat.cast_nonneg (α := ℝ) L, Nat.cast_nonneg (α := ℝ) len]

end

end MinCostFlow.DynSpanner.Program
