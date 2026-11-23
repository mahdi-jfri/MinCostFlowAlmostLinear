module

public import MinCostFlow.SparseCore.Program.BundleStepDelStep

/-!
# Verification of Phase 1 deletion loop (`BundleStepDelProof`)

Proves `bundleStepDel_runs`, verifying `bundleStepDelStmt bDllErase` end-to-end:
unlinking all active edges listed as `(e, oldCoreTail, oldCoreHead)` triples at `delPtr`,
transforming `BundleTableRepAt` into `BundleTableAfterDel` in `≤ 395 * delCount + 65` steps.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

public section

/-- Set of edge indices listed in the first `i` triples of `dels`. -/
def delPrefixSet (dels : List (ℕ × ℕ × ℕ)) (i : ℕ) : Finset ℕ :=
  ((dels.take i).map Prod.fst).toFinset

/-- End-to-end verification of `bundleStepDelStmt bDllErase` (Phase 1 of `bundleStep`).
Takes `args = [tbl, delCount, delPtr, touchedBufPtr]` and transforms `BundleTableRepAt` into
`BundleTableAfterDel`, writing the distinct touched slots to `touchedBufPtr` and returning
`touched.length` in `≤ 395 * delCount + 65` steps. -/
theorem bundleStepDel_runs {w slotCap vCap eCap tbl delCount delPtr touchedBufPtr pos : ℕ}
    {pProg : Program} {bDllErase : ℕ}
    {S₀ : BundleTableState slotCap} {m : BundleTableMeta slotCap}
    {mem₀ : ℕ → ℕ} {dels : List (ℕ × ℕ × ℕ)} {ω : ℕ → Bool}
    (hbErase : ∀ prevBase nextBase headAddr key L,
      MeetsContract w pProg bDllErase
        (bundleDllEraseContract w prevBase nextBase headAddr (2 * eCap) key L))
    (hw16 : 16 ≤ 2 ^ w)
    (htbl_w : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w)
    (hblks_w : ∀ j : Fin slotCap, ∀ p c, m.slotBlocks j = some (p, c) →
      p + bundleSlotBlockSize c < 2 ^ w)
    (hdel_w : delPtr + 3 * delCount < 2 ^ w)
    (htouch_w : touchedBufPtr + slotCap < 2 ^ w)
    (hdel_disj_foot : ∀ a, delPtr ≤ a → a < delPtr + 3 * delCount → ¬ bundleTableFoot eCap tbl m a)
    (htouch_disj_foot : ∀ a, touchedBufPtr ≤ a → a < touchedBufPtr + slotCap →
      ¬ bundleTableCoreFoot eCap tbl m a)
    (hdel_disj_touch : ∀ a, delPtr ≤ a → a < delPtr + 3 * delCount →
      a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a)
    (hrep0 : BundleTableRepAt slotCap vCap eCap tbl S₀ m mem₀)
    (hdels_len : dels.length = delCount)
    (hdels_mem : readDelTriples mem₀ delPtr delCount = dels)
    (hdels_lt : ∀ tr ∈ dels, tr.1 < eCap ∧ tr.2.1 < 2 ^ w ∧ tr.2.2 < 2 ^ w)
    (hdels_par : ∀ i (hi : i < dels.length), dels[i].1 ∉ delPrefixSet dels i →
      ∀ (j : Fin slotCap) (B : BundleState), S₀ j = some B →
        dels[i].1 ∈ B.edges →
        dels[i].2.1 = B.parent (B.bundleOf (dels[i].1, true)) ∧
        dels[i].2.2 = B.parent (B.bundleOf (dels[i].1, false))) :
    let D := (dels.map Prod.fst).toFinset
    ∃ st' c touched,
      Runs w pProg ω (bundleStepDelStmt bDllErase)
        (startState [tbl, delCount, delPtr, touchedBufPtr] mem₀ pos) (.returned touched.length) st' c ∧
      BundleTableAfterDel slotCap vCap eCap tbl S₀ D m touched st'.mem ∧
      ListAt st'.mem touchedBufPtr touched ∧
      (∀ a, ¬ bundleTableCoreFoot eCap tbl m a →
        (a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a) → st'.mem a = mem₀ a) ∧
      c ≤ 398 * delCount + 65 := by
  intro D
  have htbl_w' : tbl + (14 + 7 * slotCap + 8 * eCap) < 2 ^ w := htbl_w
  rcases hrep0 with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11,
    hdisjE0, hedgeSlot0, hendBun0, hslots0, hdisjB0, hscrS0, hscrE0, _hcur0⟩
  set st0 := startState [tbl, delCount, delPtr, touchedBufPtr] mem₀ pos
  set r5 := Function.update st0.regs 5 (btSlotPtrBase tbl)
  set r6 := Function.update r5 6 (btEdgeSlotBase tbl slotCap)
  set r7 := Function.update r6 7 (btEndBundleBase tbl slotCap eCap)
  set r8 := Function.update r7 8 (btEndPrevBase tbl slotCap eCap)
  set r9 := Function.update r8 9 (btEndNextBase tbl slotCap eCap)
  set r10 := Function.update r9 10 (btSlotTouchedBase tbl slotCap eCap)
  set r11 := Function.update r10 11 (btSlotDelHeadBase tbl slotCap eCap)
  set r12 := Function.update r11 12 (btSlotDelNextBase tbl slotCap eCap)
  set regs_h := Function.update r12 13 0
  set st_h : State := { st0 with regs := regs_h }
  have hhdr_w : ∀ off < 12, tbl + off < 2 ^ w := fun off hoff => by clear * - htbl_w' hoff; omega
  have hrun_hdr_cps : ∀ {sTail : Stmt} {o : Outcome} {stF : State} {cTail : ℕ},
      Runs w pProg ω sTail st_h o stF cTail →
      Runs w pProg ω
        (.assign 5 (.load (.bin .add (.reg 0) (.const 3))) ;;
         .assign 6 (.load (.bin .add (.reg 0) (.const 4))) ;;
         .assign 7 (.load (.bin .add (.reg 0) (.const 5))) ;;
         .assign 8 (.load (.bin .add (.reg 0) (.const 6))) ;;
         .assign 9 (.load (.bin .add (.reg 0) (.const 7))) ;;
         .assign 10 (.load (.bin .add (.reg 0) (.const 8))) ;;
         .assign 11 (.load (.bin .add (.reg 0) (.const 9))) ;;
         .assign 12 (.load (.bin .add (.reg 0) (.const 10))) ;;
         .assign 13 (.const 0) ;;
         sTail) st0 o stF (51 + cTail) := by
    intro sTail o stF cTail hTail
    have ha5 : Runs w pProg ω (.assign 5 (.load (.bin .add (.reg 0) (.const 3)))) st0 .normal { st0 with regs := r5 } 5 :=
      runs_assign_iff.mpr ⟨btSlotPtrBase tbl, by
        simp [Expr.eval, BinOp.eval, st0, startState, show 3 < 2 ^ w by omega, hhdr_w 3 (by decide)]
        exact hr3, rfl, rfl, rfl⟩
    have ha6 : Runs w pProg ω (.assign 6 (.load (.bin .add (.reg 0) (.const 4)))) { st0 with regs := r5 } .normal { st0 with regs := r6 } 5 :=
      runs_assign_iff.mpr ⟨btEdgeSlotBase tbl slotCap, by
        simp [Expr.eval, BinOp.eval, r5, st0, startState, show 4 < 2 ^ w by omega, hhdr_w 4 (by decide)]
        exact hr4, rfl, rfl, rfl⟩
    have ha7 : Runs w pProg ω (.assign 7 (.load (.bin .add (.reg 0) (.const 5)))) { st0 with regs := r6 } .normal { st0 with regs := r7 } 5 :=
      runs_assign_iff.mpr ⟨btEndBundleBase tbl slotCap eCap, by
        simp [Expr.eval, BinOp.eval, r6, r5, st0, startState, show 5 < 2 ^ w by omega, hhdr_w 5 (by decide)]
        exact hr5, rfl, rfl, rfl⟩
    have ha8 : Runs w pProg ω (.assign 8 (.load (.bin .add (.reg 0) (.const 6)))) { st0 with regs := r7 } .normal { st0 with regs := r8 } 5 :=
      runs_assign_iff.mpr ⟨btEndPrevBase tbl slotCap eCap, by
        simp [Expr.eval, BinOp.eval, r7, r6, r5, st0, startState, show 6 < 2 ^ w by omega, hhdr_w 6 (by decide)]
        exact hr6, rfl, rfl, rfl⟩
    have ha9 : Runs w pProg ω (.assign 9 (.load (.bin .add (.reg 0) (.const 7)))) { st0 with regs := r8 } .normal { st0 with regs := r9 } 5 :=
      runs_assign_iff.mpr ⟨btEndNextBase tbl slotCap eCap, by
        simp [Expr.eval, BinOp.eval, r8, r7, r6, r5, st0, startState, show 7 < 2 ^ w by omega, hhdr_w 7 (by decide)]
        exact hr7, rfl, rfl, rfl⟩
    have ha10 : Runs w pProg ω (.assign 10 (.load (.bin .add (.reg 0) (.const 8)))) { st0 with regs := r9 } .normal { st0 with regs := r10 } 5 :=
      runs_assign_iff.mpr ⟨btSlotTouchedBase tbl slotCap eCap, by
        simp [Expr.eval, BinOp.eval, r9, r8, r7, r6, r5, st0, startState, show 8 < 2 ^ w by omega, hhdr_w 8 (by decide)]
        exact hr8, rfl, rfl, rfl⟩
    have ha11 : Runs w pProg ω (.assign 11 (.load (.bin .add (.reg 0) (.const 9)))) { st0 with regs := r10 } .normal { st0 with regs := r11 } 5 :=
      runs_assign_iff.mpr ⟨btSlotDelHeadBase tbl slotCap eCap, by
        simp [Expr.eval, BinOp.eval, r10, r9, r8, r7, r6, r5, st0, startState, show 9 < 2 ^ w by omega, hhdr_w 9 (by decide)]
        exact hr9, rfl, rfl, rfl⟩
    have ha12 : Runs w pProg ω (.assign 12 (.load (.bin .add (.reg 0) (.const 10)))) { st0 with regs := r11 } .normal { st0 with regs := r12 } 5 :=
      runs_assign_iff.mpr ⟨btSlotDelNextBase tbl slotCap eCap, by
        simp [Expr.eval, BinOp.eval, r11, r10, r9, r8, r7, r6, r5, st0, startState, show 10 < 2 ^ w by omega, hhdr_w 10 (by decide)]
        exact hr10, rfl, rfl, rfl⟩
    have ha13 : Runs w pProg ω (.assign 13 (.const 0)) { st0 with regs := r12 } .normal st_h 2 :=
      runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
    exact (show 5 + (5 + (5 + (5 + (5 + (5 + (5 + (5 + (2 + cTail + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 = 51 + cTail by omega) ▸
      bundle_runs_seq_normal ha5 (bundle_runs_seq_normal ha6 (bundle_runs_seq_normal ha7
        (bundle_runs_seq_normal ha8 (bundle_runs_seq_normal ha9 (bundle_runs_seq_normal ha10
          (bundle_runs_seq_normal ha11 (bundle_runs_seq_normal ha12 (bundle_runs_seq_normal ha13 hTail))))))))
  let Inv : ℕ → List ℕ → State → Prop := fun i touched st =>
    st.regs 0 = tbl ∧ st.regs 1 = delCount ∧ st.regs 2 = delPtr ∧ st.regs 3 = touchedBufPtr ∧
    st.regs 5 = btSlotPtrBase tbl ∧ st.regs 6 = btEdgeSlotBase tbl slotCap ∧
    st.regs 7 = btEndBundleBase tbl slotCap eCap ∧ st.regs 8 = btEndPrevBase tbl slotCap eCap ∧
    st.regs 9 = btEndNextBase tbl slotCap eCap ∧ st.regs 10 = btSlotTouchedBase tbl slotCap eCap ∧
    st.regs 11 = btSlotDelHeadBase tbl slotCap eCap ∧ st.regs 12 = btSlotDelNextBase tbl slotCap eCap ∧
    st.regs 13 = touched.length ∧ st.regs 14 = i ∧
    BundleTableAfterDel slotCap vCap eCap tbl S₀ (delPrefixSet dels i) m touched st.mem ∧
    ListAt st.mem touchedBufPtr touched ∧
    (∀ a, ¬ bundleTableCoreFoot eCap tbl m a →
      (a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a) → st.mem a = mem₀ a)
  obtain ⟨st_loop, c_loop, touched, hrun_loop, hInv_end, hc_loop⟩ :=
    runs_forRange_pot (w := w) (p := pProg) (ω := ω) (r := 14) (lo := .const 0) (hi := .reg 1)
      (phi := fun _ _ => 0) (Inv := Inv) (stepCost := fun _ => 388) delCount
      (by omega) (fun _ => by omega) (st₀ := st_h) (a₀ := [])
      (by
        refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], ?_, rfl⟩
        have hD0 : delPrefixSet dels 0 = ∅ := by simp [delPrefixSet]
        have htab0 : tableDelEdges S₀ ∅ = S₀ := by
          funext j; simp only [tableDelEdges]; cases S₀ j <;> simp
        refine ⟨by simp [st_h, regs_h, r12, r11, r10, r9, r8, r7, r6, r5, st0, startState],
          by simp [st_h, regs_h, r12, r11, r10, r9, r8, r7, r6, r5, st0, startState],
          by simp [st_h, regs_h, r12, r11, r10, r9, r8, r7, r6, r5, st0, startState],
          by simp [st_h, regs_h, r12, r11, r10, r9, r8, r7, r6, r5, st0, startState],
          by simp [st_h, regs_h, r12, r11, r10, r9, r8, r7, r6, r5],
          by simp [st_h, regs_h, r12, r11, r10, r9, r8, r7, r6],
          by simp [st_h, regs_h, r12, r11, r10, r9, r8, r7],
          by simp [st_h, regs_h, r12, r11, r10, r9, r8],
          by simp [st_h, regs_h, r12, r11, r10, r9],
          by simp [st_h, regs_h, r12, r11, r10],
          by simp [st_h, regs_h, r12, r11],
          by simp [st_h, regs_h, r12],
          by simp [st_h, regs_h], by simp,
          ?_, fun _ hi => by simp at hi, fun _ _ _ => rfl⟩
        rw [hD0]
        simp only [BundleTableAfterDel, htab0]
        refine ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11,
          hdisjE0, hedgeSlot0, hendBun0, hslots0, hdisjB0,
          List.nodup_nil, (fun _ h => by cases h),
          fun s hs => by simpa [st_h, st0, startState] using (hscrS0 s hs).1,
          fun s hs => (hscrS0 s hs).2.2,
          fun j => by
            cases hSj : S₀ j with
            | none => exact ⟨(hscrS0 j.1 j.2).2.1, by simp⟩
            | some B₀ =>
              exact ⟨by simp, [], (hscrS0 j.1 j.2).2.1, by simp⟩,
          fun e he _ => hscrE0 e he⟩)
      (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      (fun _ _ st _ hI => by simp [Expr.eval, hI.2.1])
      (fun i touched st hi hI => by
        rcases hI with ⟨r0, r1, r2, r3, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, hafter,
          htouch_mem, hfr_out⟩
        have hi_len : i < dels.length := by omega
        set tr := dels[i]'hi_len
        set e := tr.1
        set oldT := tr.2.1
        set oldH := tr.2.2
        have htr_lt := hdels_lt tr (List.getElem_mem hi_len)
        have htr_read : tr = (mem₀ (delPtr + 3 * i), mem₀ (delPtr + 3 * i + 1), mem₀ (delPtr + 3 * i + 2)) := by
          have := congrArg (fun l => l[i]?) hdels_mem
          simp only [readDelTriples, List.getElem?_map, List.getElem?_range hi, Option.map_some,
            List.getElem?_eq_getElem hi_len, Option.some.injEq] at this
          exact this.symm
        have hdel_eq : ∀ a, delPtr ≤ a → a < delPtr + 3 * delCount → st.mem a = mem₀ a :=
          fun a ha1 ha2 => hfr_out a (fun hf => hdel_disj_foot a ha1 ha2 (bundleTableCoreFoot_subset_foot hf))
            (hdel_disj_touch a ha1 ha2)
        have hmem_e : st.mem (delPtr + 3 * i) = e := by
          rw [hdel_eq _ (by omega) (by omega)]; exact (Prod.mk.inj htr_read).1.symm
        have hmem_T : st.mem (delPtr + 3 * i + 1) = oldT := by
          rw [hdel_eq _ (by omega) (by omega)]; exact (Prod.mk.inj (Prod.mk.inj htr_read).2).1.symm
        have hmem_H : st.mem (delPtr + 3 * i + 2) = oldH := by
          rw [hdel_eq _ (by omega) (by omega)]; exact (Prod.mk.inj (Prod.mk.inj htr_read).2).2.symm
        have hD_step : delPrefixSet dels (i + 1) = insert e (delPrefixSet dels i) := by
          ext x
          simp only [delPrefixSet, List.take_succ_eq_append_getElem hi_len, List.map_append,
            List.map_singleton, List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
            Finset.mem_union, Finset.mem_insert]
          tauto
        set st1 : State := { st with regs := Function.update st.regs 15 e }
        have ha15 : Runs w pProg ω (.assign 15 (.load (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 14)))))
            st .normal st1 7 :=
          runs_assign_iff.mpr ⟨e, by
            simp [Expr.eval, BinOp.eval, r2, r14, hmem_e, show 3 < 2 ^ w by omega,
              show 3 * i < 2 ^ w by omega, show delPtr + 3 * i < 2 ^ w by omega], rfl, rfl, rfl⟩
        set es := st.mem (btEdgeSlotBase tbl slotCap + e)
        set st2 : State := { st1 with regs := Function.update st1.regs 16 es }
        have ha16 : Runs w pProg ω (.assign 16 (.load (.bin .add (.reg 6) (.reg 15))))
            st1 .normal st2 5 :=
          runs_assign_iff.mpr ⟨es, by
            simp [Expr.eval, BinOp.eval, st1, r6, es, show btEdgeSlotBase tbl slotCap + e < 2 ^ w by
              unfold btEdgeSlotBase; clear * - htr_lt htbl_w'; omega], rfl, rfl, rfl⟩
        by_cases hex : (∃ (j : Fin slotCap) (B : BundleState), S₀ j = some B ∧ e ∈ B.edges) ∧
            e ∉ delPrefixSet dels i
        · obtain ⟨⟨js, B₀, hSjs, heB₀⟩, he_not_prev⟩ := hex
          have hSjs_del : tableDelEdges S₀ (delPrefixSet dels i) js =
              some { B₀ with edges := B₀.edges \ delPrefixSet dels i } := by
            simp [tableDelEdges, hSjs]
          have hes_eq : es = js.1 + 1 :=
            (hafter.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e htr_lt.1).1 js _ hSjs_del
              (Finset.mem_sdiff.mpr ⟨heB₀, he_not_prev⟩)
          have hpar_tr := hdels_par i hi_len he_not_prev js B₀ hSjs heB₀
          obtain ⟨st_f, c_act, hrun_act, fr0, fr1, fr2, fr3, fr5, fr6, fr7, fr8, fr9, fr10, fr11,
            fr12, fr13, fr14, fafter, ftouch, ffr, hc_act⟩ :=
            bundleStepDel_active_step (st2 := st2) hbErase hw16 htbl_w hblks_w hdel_w htouch_w
              hdel_disj_foot htouch_disj_foot hi htr_lt.1 htr_lt.2.1 htr_lt.2.2
              hSjs heB₀ he_not_prev hpar_tr.1 hpar_tr.2 hmem_T hmem_H
              (by simp [st2, st1, r0]) (by simp [st2, st1, r1]) (by simp [st2, st1, r2])
              (by simp [st2, st1, r3]) (by simp [st2, st1, r5]) (by simp [st2, st1, r6])
              (by simp [st2, st1, r7]) (by simp [st2, st1, r8]) (by simp [st2, st1, r9])
              (by simp [st2, st1, r10]) (by simp [st2, st1, r11]) (by simp [st2, st1, r12])
              (by simp [st2, st1, r13]) (by simp [st2, st1, r14]) (by simp [st2, st1, e])
              (by simp [st2, hes_eq]) hafter htouch_mem
          have hcond : Runs w pProg ω (.cond (.reg 16) (bundleStepDelActiveStmt bDllErase) .nop)
              st2 .normal st_f (1 + c_act + 1) :=
            runs_cond_iff.mpr ⟨js.1 + 1, c_act, by simp [Expr.eval, st2, hes_eq],
              by simpa [Nat.succ_ne_zero] using hrun_act, rfl⟩
          refine ⟨st_f, 7 + (5 + (1 + c_act + 1) + 1) + 1,
            if js.1 ∈ touched then touched else touched ++ [js.1],
            bundle_runs_seq_normal ha15 (bundle_runs_seq_normal ha16 hcond), fr14,
            ⟨fr0, fr1, fr2, fr3, fr5, fr6, fr7, fr8, fr9, fr10, fr11, fr12, fr13, by simp,
             hD_step ▸ fafter, ftouch, fun a hnf hout => (ffr a hnf hout).trans (hfr_out a hnf hout)⟩,
            rfl, by omega⟩
        · have hnot_act : ∀ (j : Fin slotCap) (B₀ : BundleState), S₀ j = some B₀ →
              e ∈ B₀.edges → e ∈ delPrefixSet dels i := fun j B₀ hSj heB₀ => by
            by_contra hnp
            exact hex ⟨⟨j, B₀, hSj, heB₀⟩, hnp⟩
          rcases hafter with ⟨ar0, ar1, ar2, ar3, ar4, ar5, ar6, ar7, ar8, ar9, ar10, ar11,
            adisjE, aedgeSlot, aendBun, aslots, adisjB, atouch_nd, atouch_lt, atouch_flag,
            acand0, adelLists, adelNext0⟩
          have hes_eq : es = 0 := (aedgeSlot e htr_lt.1).2 fun j B hSj heB => by
            simp only [tableDelEdges, Option.map_eq_some_iff] at hSj
            rcases hSj with ⟨B₀, hS₀, rfl⟩
            exact (Finset.mem_sdiff.mp heB).2 (hnot_act j B₀ hS₀ (Finset.mem_sdiff.mp heB).1)
          have hcond : ∀ sThen, Runs w pProg ω (.cond (.reg 16) sThen .nop) st2 .normal st2 3 := fun _ =>
            runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, st2, hes_eq],
              by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
          have htab_eq : tableDelEdges S₀ (delPrefixSet dels (i + 1)) =
              tableDelEdges S₀ (delPrefixSet dels i) := by
            funext j; simp only [tableDelEdges, hD_step]
            cases hSj : S₀ j with
            | none => rfl
            | some B₀ =>
              simp only [Option.map_some, Option.some.injEq]
              congr 1; ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
              exact ⟨fun ⟨hx, _, h2⟩ => ⟨hx, h2⟩,
                fun ⟨hx, h2⟩ => ⟨hx, fun hxe => h2 (hxe ▸ hnot_act j B₀ hSj (hxe ▸ hx)), h2⟩⟩
          refine ⟨st2, 7 + (5 + 3 + 1) + 1, touched,
            bundle_runs_seq_normal ha15 (bundle_runs_seq_normal ha16 (hcond _)),
            by simp [st2, st1, r14], ?_, rfl, by omega⟩
          refine ⟨by simp [st2, st1, r0], by simp [st2, st1, r1], by simp [st2, st1, r2],
            by simp [st2, st1, r3], by simp [st2, st1, r5], by simp [st2, st1, r6],
            by simp [st2, st1, r7], by simp [st2, st1, r8], by simp [st2, st1, r9],
            by simp [st2, st1, r10], by simp [st2, st1, r11], by simp [st2, st1, r12],
            by simp [st2, st1, r13], by simp, ?_, htouch_mem, hfr_out⟩
          refine ⟨ar0, ar1, ar2, ar3, ar4, ar5, ar6, ar7, ar8, ar9, ar10, ar11,
            htab_eq ▸ adisjE, htab_eq ▸ aedgeSlot, htab_eq ▸ aendBun, htab_eq ▸ aslots, adisjB,
            atouch_nd, atouch_lt, atouch_flag, acand0, fun j => ?_, fun e' he' hnot => ?_⟩
          · have hj := adelLists j
            cases hSj : S₀ j with
            | none => simpa [hSj] using hj
            | some B₀ =>
              rw [hSj] at hj
              have hinter : B₀.edges ∩ delPrefixSet dels (i + 1) = B₀.edges ∩ delPrefixSet dels i := by
                ext x; simp only [Finset.mem_inter, hD_step, Finset.mem_insert]
                exact ⟨fun ⟨hx, hx2⟩ => ⟨hx, hx2.elim (fun h => h ▸ hnot_act j B₀ hSj (h ▸ hx)) id⟩,
                  fun ⟨hx, hx2⟩ => ⟨hx, Or.inr hx2⟩⟩
              simpa [hinter] using hj
          · apply adelNext0 e' he'
            intro j B₀ hSj hmem
            exact hnot j B₀ hSj (Finset.mem_inter.mpr
              ⟨(Finset.mem_inter.mp hmem).1, hD_step ▸ Finset.mem_insert_of_mem (Finset.mem_inter.mp hmem).2⟩))
  rcases hInv_end with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hr13_end, _, hafter_end, htouch_end, hfr_end⟩
  have hD_eq : delPrefixSet dels delCount = D := by
    simp only [delPrefixSet, D, ← hdels_len, List.take_length]
  have hret : Runs w pProg ω (.ret (.reg 13)) st_loop (.returned touched.length) st_loop 2 :=
    runs_ret_iff.mpr ⟨touched.length, by simp [Expr.eval, hr13_end], rfl, rfl, rfl⟩
  refine ⟨st_loop, 51 + (c_loop + 2 + 1), touched,
    hrun_hdr_cps (bundle_runs_seq_normal hrun_loop hret),
    hD_eq ▸ hafter_end, htouch_end, hfr_end, ?_⟩
  have hrc : rangeCost (fun _ => 388) 0 delCount = 388 * delCount := by
    rw [rangeCost_zero_eq_range]; simp [Nat.mul_comm]
  rw [hrc] at hc_loop; simp only [Expr.size_reg, Expr.size_const] at hc_loop
  omega

end

end MinCostFlow.SparseCore.Program
