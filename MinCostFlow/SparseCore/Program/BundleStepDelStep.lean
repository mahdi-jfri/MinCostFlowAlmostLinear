module

public import MinCostFlow.SparseCore.Program.BundleStepDelPost

/-!
# Active-edge step for Phase 1 deletion loop (`BundleStepDelStep`)

Proves `bundleStepDel_active_step`, executing one active-edge deletion branch inside
`bundleStepDelStmt` and delegating postcondition assembly to `bundleStepDel_active_post`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

public section

/-- The active-edge `then` branch of `bundleStepDelStmt`. -/
@[expose] def bundleStepDelActiveStmt (bDllErase : ℕ) : Stmt :=
  .assign 17 (.bin .sub (.reg 16) (.const 1)) ;;
  .assign 18 (.load (.bin .add (.reg 5) (.reg 17))) ;;
  .assign 19 (.load (.reg 18)) ;;
  .assign 20 (.bin .mul (.const 2) (.reg 15)) ;;
  .assign 24 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 14))) (.const 1))) ;;
  bundleDelEndStmt bDllErase ;;
  .assign 20 (.bin .add (.bin .mul (.const 2) (.reg 15)) (.const 1)) ;;
  .assign 24 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 14))) (.const 2))) ;;
  bundleDelEndStmt bDllErase ;;
  .store (.bin .add (.reg 6) (.reg 15)) (.const 0) ;;
  .assign 23 (.load (.bin .add (.reg 18) (.const 2))) ;;
  .store (.bin .add (.reg 18) (.const 2)) (.bin .sub (.reg 23) (.const 1)) ;;
  .assign 24 (.load (.bin .add (.reg 11) (.reg 17))) ;;
  .store (.bin .add (.reg 12) (.reg 15)) (.reg 24) ;;
  .store (.bin .add (.reg 11) (.reg 17)) (.bin .add (.reg 15) (.const 1)) ;;
  .assign 24 (.load (.bin .add (.reg 10) (.reg 17))) ;;
  .cond (.bin .eq (.reg 24) (.const 0))
    (.store (.bin .add (.reg 10) (.reg 17)) (.const 1) ;;
     .store (.bin .add (.reg 3) (.reg 13)) (.reg 17) ;;
     .assign 13 (.bin .add (.reg 13) (.const 1)))
    .nop

/-- Verifies one active-edge deletion inside `bundleStepDelStmt`. -/
lemma bundleStepDel_active_step {w slotCap vCap eCap tbl delCount delPtr touchedBufPtr i e oldT oldH : ℕ}
    {pProg : Program} {bDllErase : ℕ}
    {S₀ : BundleTableState slotCap} {m : BundleTableMeta slotCap}
    {D : Finset ℕ} {touched : List ℕ} {js : Fin slotCap} {B₀ : BundleState}
    {st2 : State} {ω : ℕ → Bool}
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
    (hi : i < delCount) (he_lt : e < eCap) (holdT_w : oldT < 2 ^ w) (holdH_w : oldH < 2 ^ w)
    (hSjs : S₀ js = some B₀) (heB₀ : e ∈ B₀.edges) (he_not_D : e ∉ D)
    (hparT : oldT = B₀.parent (B₀.bundleOf (e, true)))
    (hparH : oldH = B₀.parent (B₀.bundleOf (e, false)))
    (hmem_T : st2.mem (delPtr + 3 * i + 1) = oldT)
    (hmem_H : st2.mem (delPtr + 3 * i + 2) = oldH)
    (r0 : st2.regs 0 = tbl) (r1 : st2.regs 1 = delCount) (r2 : st2.regs 2 = delPtr)
    (r3 : st2.regs 3 = touchedBufPtr) (r5 : st2.regs 5 = btSlotPtrBase tbl)
    (r6 : st2.regs 6 = btEdgeSlotBase tbl slotCap)
    (r7 : st2.regs 7 = btEndBundleBase tbl slotCap eCap)
    (r8 : st2.regs 8 = btEndPrevBase tbl slotCap eCap)
    (r9 : st2.regs 9 = btEndNextBase tbl slotCap eCap)
    (r10 : st2.regs 10 = btSlotTouchedBase tbl slotCap eCap)
    (r11 : st2.regs 11 = btSlotDelHeadBase tbl slotCap eCap)
    (r12 : st2.regs 12 = btSlotDelNextBase tbl slotCap eCap)
    (r13 : st2.regs 13 = touched.length) (r14 : st2.regs 14 = i)
    (r15 : st2.regs 15 = e) (r16 : st2.regs 16 = js.1 + 1)
    (hafter : BundleTableAfterDel slotCap vCap eCap tbl S₀ D m touched st2.mem)
    (htouch_mem : ListAt st2.mem touchedBufPtr touched) :
    let touched' := if js.1 ∈ touched then touched else touched ++ [js.1]
    ∃ st' c,
      Runs w pProg ω (bundleStepDelActiveStmt bDllErase) st2 .normal st' c ∧
      st'.regs 0 = tbl ∧ st'.regs 1 = delCount ∧ st'.regs 2 = delPtr ∧
      st'.regs 3 = touchedBufPtr ∧ st'.regs 5 = btSlotPtrBase tbl ∧
      st'.regs 6 = btEdgeSlotBase tbl slotCap ∧ st'.regs 7 = btEndBundleBase tbl slotCap eCap ∧
      st'.regs 8 = btEndPrevBase tbl slotCap eCap ∧ st'.regs 9 = btEndNextBase tbl slotCap eCap ∧
      st'.regs 10 = btSlotTouchedBase tbl slotCap eCap ∧
      st'.regs 11 = btSlotDelHeadBase tbl slotCap eCap ∧
      st'.regs 12 = btSlotDelNextBase tbl slotCap eCap ∧
      st'.regs 13 = touched'.length ∧ st'.regs 14 = i ∧
      BundleTableAfterDel slotCap vCap eCap tbl S₀ (insert e D) m touched' st'.mem ∧
      ListAt st'.mem touchedBufPtr touched' ∧
      (∀ a, ¬ bundleTableCoreFoot eCap tbl m a →
        (a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a) → st'.mem a = st2.mem a) ∧
      c ≤ 370 := by
  intro touched'
  have hjs_lt : js.1 < slotCap := js.2
  have htbl_w' : tbl + (14 + 7 * slotCap + 8 * eCap) < 2 ^ w := htbl_w
  have h1_w : 1 < 2 ^ w := by clear * - hw16; omega
  have h2_w : 2 < 2 ^ w := by clear * - hw16; omega
  have h3_w : 3 < 2 ^ w := by clear * - hw16; omega
  have hprev_w : btEndPrevBase tbl slotCap eCap + 2 * eCap < 2 ^ w := by
    unfold btEndPrevBase; clear * - htbl_w'; omega
  have hnext_w : btEndNextBase tbl slotCap eCap + 2 * eCap < 2 ^ w := by
    unfold btEndNextBase; clear * - htbl_w'; omega
  have hprev_next : btEndPrevBase tbl slotCap eCap + 2 * eCap ≤ btEndNextBase tbl slotCap eCap ∨
      btEndNextBase tbl slotCap eCap + 2 * eCap ≤ btEndPrevBase tbl slotCap eCap :=
    Or.inl (by unfold btEndPrevBase btEndNextBase; omega)
  have hafter_copy := hafter
  rcases hafter with ⟨_, _, _, _, _, _, _, _, _, _, _, _,
    _, _, aendBun, aslots, _, atouch_nd, atouch_lt, atouch_flag, _, _, _⟩
  have hScurr_js : tableDelEdges S₀ D js = some { B₀ with edges := B₀.edges \ D } := by
    simp [tableDelEdges, hSjs]
  set B := ({ B₀ with edges := B₀.edges \ D } : BundleState)
  have he_curr : e ∈ B.edges := Finset.mem_sdiff.mpr ⟨heB₀, he_not_D⟩
  have hslot_js := aslots js
  rw [hScurr_js] at hslot_js
  cases hm_js : m.slotBlocks js with
  | none => rw [hm_js] at hslot_js; exact False.elim hslot_js
  | some pb =>
  rcases pb with ⟨p, cap⟩
  rw [hm_js] at hslot_js
  rcases hslot_js with ⟨hslotPtr_js, hslotRep_js, hp_disj_tbl⟩
  have hp_w : p + bundleSlotBlockSize cap < 2 ^ w := hblks_w js p cap hm_js
  have hp_w' : p + (3 + 6 * cap) < 2 ^ w := hp_w
  have hp_disj_tbl' : p + (3 + 6 * cap) ≤ tbl ∨ tbl + (14 + 7 * slotCap + 8 * eCap) ≤ p := hp_disj_tbl
  have hblk_prev : p + bundleSlotBlockSize cap ≤ btEndPrevBase tbl slotCap eCap ∨
      btEndPrevBase tbl slotCap eCap + 2 * eCap ≤ p := by
    unfold btEndPrevBase bundleSlotBlockSize; clear * - hp_disj_tbl'; omega
  have hblk_next : p + bundleSlotBlockSize cap ≤ btEndNextBase tbl slotCap eCap ∨
      btEndNextBase tbl slotCap eCap + 2 * eCap ≤ p := by
    unfold btEndNextBase bundleSlotBlockSize; clear * - hp_disj_tbl'; omega
  set b1 := B.bundleOf (e, true)
  set b2 := B.bundleOf (e, false)
  obtain ⟨nB, _, hnB, hE, hbo, _, h0, _, h2, hdll, _, _, _⟩ := hslotRep_js
  have hb1_lt : b1 < nB := hbo (e, true) ((mem_edgeEnds _ _).mpr he_curr)
  have hb2_lt : b2 < nB := hbo (e, false) ((mem_edgeEnds _ _).mpr he_curr)
  have hb1_cap : b1 < cap := lt_of_lt_of_le hb1_lt hnB
  have hb2_cap : b2 < cap := lt_of_lt_of_le hb2_lt hnB
  obtain ⟨L1, hL1_dll, hL1_sz, hL1_mem⟩ := hdll b1 hb1_lt
  obtain ⟨L2, hL2_dll, hL2_sz, hL2_mem⟩ := hdll b2 hb2_lt
  have h2e_in : 2 * e ∈ L1 := (hL1_mem (2 * e)).mpr (by
    change endOfKey (endKey (e, true)) ∈ B.ends b1
    rw [bundle_endOfKey_endKey]; exact (BundleState.mem_ends B b1 (e, true)).mpr ⟨he_curr, rfl⟩)
  have h2e1_in : 2 * e + 1 ∈ L2 := (hL2_mem (2 * e + 1)).mpr (by
    change endOfKey (endKey (e, false)) ∈ B.ends b2
    rw [bundle_endOfKey_endKey]; exact (BundleState.mem_ends B b2 (e, false)).mpr ⟨he_curr, rfl⟩)
  have hL1_len_w : L1.length < 2 ^ w := by
    have hcard := Finset.card_le_card (show L1.toFinset ⊆ Finset.range (2 * eCap) from
      fun k hk => Finset.mem_range.mpr (hL1_dll.2.1 k (List.mem_toFinset.mp hk)))
    rw [List.toFinset_card_of_nodup hL1_dll.1, Finset.card_range] at hcard
    clear * - hcard htbl_w'; omega
  have hL2_len_w : L2.length < 2 ^ w := by
    have hcard := Finset.card_le_card (show L2.toFinset ⊆ Finset.range (2 * eCap) from
      fun k hk => Finset.mem_range.mpr (hL2_dll.2.1 k (List.mem_toFinset.mp hk)))
    rw [List.toFinset_card_of_nodup hL2_dll.1, Finset.card_range] at hcard
    clear * - hcard htbl_w'; omega
  have hend_2e : st2.mem (btEndBundleBase tbl slotCap eCap + 2 * e) = b1 :=
    aendBun js B hScurr_js (e, true) ((mem_edgeEnds _ _).mpr he_curr)
  have hend_2e1 : st2.mem (btEndBundleBase tbl slotCap eCap + (2 * e + 1)) = b2 :=
    aendBun js B hScurr_js (e, false) ((mem_edgeEnds _ _).mpr he_curr)
  -- Prefix assigns
  set r_a1 := Function.update st2.regs 17 js.1
  set r_a2 := Function.update r_a1 18 p
  set r_a3 := Function.update r_a2 19 cap
  set r_a4 := Function.update r_a3 20 (2 * e)
  set r_a5 := Function.update r_a4 24 oldT
  set st_a5 : State := { st2 with regs := r_a5 }
  have hjs_w : js.1 < 2 ^ w := by clear * - hjs_lt htbl_w'; omega
  have hptr_w : btSlotPtrBase tbl + js.1 < 2 ^ w := by unfold btSlotPtrBase; clear * - hjs_lt htbl_w'; omega
  have h2e_w : 2 * e < 2 ^ w := by clear * - he_lt htbl_w'; omega
  have h2e1_w : 2 * e + 1 < 2 ^ w := by clear * - he_lt htbl_w'; omega
  have h3i_w : 3 * i < 2 ^ w := by clear * - hi hdel_w; omega
  have hd3i_w : delPtr + 3 * i < 2 ^ w := by clear * - hi hdel_w; omega
  have hd3i1_w : delPtr + 3 * i + 1 < 2 ^ w := by clear * - hi hdel_w; omega
  have hd3i2_w : delPtr + 3 * i + 2 < 2 ^ w := by clear * - hi hdel_w; omega
  have hrun_pre_cps : ∀ {sTail : Stmt} {stF : State} {cTail : ℕ},
      Runs w pProg ω sTail st_a5 .normal stF cTail →
      Runs w pProg ω
        (.assign 17 (.bin .sub (.reg 16) (.const 1)) ;;
         .assign 18 (.load (.bin .add (.reg 5) (.reg 17))) ;;
         .assign 19 (.load (.reg 18)) ;;
         .assign 20 (.bin .mul (.const 2) (.reg 15)) ;;
         .assign 24 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 14))) (.const 1))) ;;
         sTail) st2 .normal stF (30 + cTail) := by
    intro sTail stF cTail hTail
    have h17 : Runs w pProg ω (.assign 17 (.bin .sub (.reg 16) (.const 1))) st2 .normal
        { st2 with regs := r_a1 } 4 :=
      runs_assign_iff.mpr ⟨js.1, by simp [Expr.eval, BinOp.eval, r16, h1_w, hjs_w], rfl, rfl, rfl⟩
    have h18 : Runs w pProg ω (.assign 18 (.load (.bin .add (.reg 5) (.reg 17))))
        { st2 with regs := r_a1 } .normal { st2 with regs := r_a2 } 5 :=
      runs_assign_iff.mpr ⟨p, by simp [Expr.eval, BinOp.eval, r_a1, r5, hslotPtr_js, hptr_w], rfl, rfl, rfl⟩
    have h19 : Runs w pProg ω (.assign 19 (.load (.reg 18)))
        { st2 with regs := r_a2 } .normal { st2 with regs := r_a3 } 3 :=
      runs_assign_iff.mpr ⟨cap, by
        simp [Expr.eval, r_a2, show st2.mem p = cap by simpa [bsOffBunCap] using h0], rfl, rfl, rfl⟩
    have h20 : Runs w pProg ω (.assign 20 (.bin .mul (.const 2) (.reg 15)))
        { st2 with regs := r_a3 } .normal { st2 with regs := r_a4 } 4 :=
      runs_assign_iff.mpr ⟨2 * e, by
        simp [Expr.eval, BinOp.eval, r_a3, r_a2, r_a1, r15, h2_w, h2e_w], rfl, rfl, rfl⟩
    have h24 : Runs w pProg ω
        (.assign 24 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 14))) (.const 1))))
        { st2 with regs := r_a4 } .normal st_a5 9 :=
      runs_assign_iff.mpr ⟨oldT, by
        simp [Expr.eval, BinOp.eval, r_a4, r_a3, r_a2, r_a1, r2, r14, hmem_T, h3_w, h1_w,
          h3i_w, hd3i_w, hd3i1_w], rfl, rfl, rfl⟩
    exact (show 4 + (5 + (3 + (4 + (9 + cTail + 1) + 1) + 1) + 1) + 1 = 30 + cTail by omega) ▸
      bundle_runs_seq_normal h17 (bundle_runs_seq_normal h18
        (bundle_runs_seq_normal h19 (bundle_runs_seq_normal h20 (bundle_runs_seq_normal h24 hTail))))
  -- First bundleDelEnd_triple: erase 2*e from b1
  obtain ⟨o_d1, st_d1, c_d1, hrun_d1, hpost_d1, hc_d1⟩ :=
    bundleDelEnd_triple (hbErase _ _ _ _ _) hw16 hprev_w hnext_w hprev_next hp_w
      hblk_prev hblk_next (by unfold btEndBundleBase; clear * - htbl_w' he_lt; omega)
      hb1_cap (by clear * - he_lt; omega) h2e_in holdT_w hL1_len_w
      hend_2e hL1_dll hL1_sz st_a5 ω
      ⟨rfl, rfl, by simp [st_a5, r_a5, r_a4, r_a3, r_a2, r_a1, r7],
        by simp [st_a5, r_a5, r_a4, r_a3, r_a2, r_a1, r8],
        by simp [st_a5, r_a5, r_a4, r_a3, r_a2, r_a1, r9],
        by simp [st_a5, r_a5, r_a4, r_a3, r_a2], by simp [st_a5, r_a5, r_a4, r_a3],
        by simp [st_a5, r_a5, r_a4], by simp [st_a5, r_a5]⟩
  cases o_d1 with
  | returned _ => exact False.elim hpost_d1
  | normal =>
  rcases hpost_d1 with ⟨hreg_d1, hdll_d1, hsz_d1, hpar0_d1, _, hfr_d1⟩
  have hst_d1_out : ∀ a, ¬ bundleTableFoot eCap tbl m a → st_d1.mem a = st2.mem a := fun a hnf =>
    hfr_d1 a
      (fun h => hnf (h ▸ Or.inr ⟨js, p, cap, hm_js, by unfold bsHeadBase; omega, by unfold bsHeadBase bundleSlotBlockSize; omega⟩))
      (fun h => hnf (h ▸ Or.inr ⟨js, p, cap, hm_js, by unfold bsSizeBase; omega, by unfold bsSizeBase bundleSlotBlockSize; omega⟩))
      (fun h => hnf (h ▸ Or.inr ⟨js, p, cap, hm_js, by unfold bsParentBase; omega, by unfold bsParentBase bundleSlotBlockSize; omega⟩))
      fun k hk =>
        have hk_lt := hL1_dll.2.1 k hk
        ⟨fun h => hnf (h ▸ Or.inl ⟨by unfold btEndPrevBase; omega, by unfold btEndPrevBase bundleTableFixedSize; omega⟩),
         fun h => hnf (h ▸ Or.inl ⟨by unfold btEndNextBase; omega, by unfold btEndNextBase bundleTableFixedSize; omega⟩)⟩
  -- Mid assigns
  set r_b1 := Function.update st_d1.regs 20 (2 * e + 1)
  set r_b2 := Function.update r_b1 24 oldH
  set st_b2 : State := { st_d1 with regs := r_b2 }
  have hrun_mid_cps : ∀ {sTail : Stmt} {stF : State} {cTail : ℕ},
      Runs w pProg ω sTail st_b2 .normal stF cTail →
      Runs w pProg ω
        (.assign 20 (.bin .add (.bin .mul (.const 2) (.reg 15)) (.const 1)) ;;
         .assign 24 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 14))) (.const 2))) ;;
         sTail) st_d1 .normal stF (17 + cTail) := by
    intro sTail stF cTail hTail
    have hr15' : st_d1.regs 15 = e := by
      rw [hreg_d1 15 (by decide) (by decide) (by decide)]; simp [st_a5, r_a5, r_a4, r_a3, r_a2, r_a1, r15]
    have hr2' : st_d1.regs 2 = delPtr := by
      rw [hreg_d1 2 (by decide) (by decide) (by decide)]; simp [st_a5, r_a5, r_a4, r_a3, r_a2, r_a1, r2]
    have hr14' : st_d1.regs 14 = i := by
      rw [hreg_d1 14 (by decide) (by decide) (by decide)]; simp [st_a5, r_a5, r_a4, r_a3, r_a2, r_a1, r14]
    have h20 : Runs w pProg ω (.assign 20 (.bin .add (.bin .mul (.const 2) (.reg 15)) (.const 1)))
        st_d1 .normal { st_d1 with regs := r_b1 } 6 :=
      runs_assign_iff.mpr ⟨2 * e + 1, by simp [Expr.eval, BinOp.eval, hr15', h2_w, h1_w, h2e_w, h2e1_w], rfl, rfl, rfl⟩
    have h24 : Runs w pProg ω
        (.assign 24 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 14))) (.const 2))))
        { st_d1 with regs := r_b1 } .normal st_b2 9 :=
      runs_assign_iff.mpr ⟨oldH, by
        have hmem_H1 : st_d1.mem (delPtr + 3 * i + 2) = oldH :=
          (hst_d1_out _ (hdel_disj_foot _ (by omega) (by omega))).trans hmem_H
        simp [Expr.eval, BinOp.eval, r_b1, hr2', hr14', hmem_H1, h3_w, h2_w, h3i_w, hd3i_w, hd3i2_w], rfl, rfl, rfl⟩
    exact (show 6 + (9 + cTail + 1) + 1 = 17 + cTail by omega) ▸
      bundle_runs_seq_normal h20 (bundle_runs_seq_normal h24 hTail)
  -- Second bundleDelEnd_triple: erase 2*e+1 from b2
  set L2pre := if b2 = b1 then L1.erase (2 * e) else L2
  have h2e1_in_pre : 2 * e + 1 ∈ L2pre := by
    dsimp only [L2pre]; split_ifs with h21
    · rw [List.Nodup.mem_erase_iff hL1_dll.1]
      exact ⟨by omega, (hL1_mem (2 * e + 1)).mpr (by
        change endOfKey (endKey (e, false)) ∈ B.ends b1
        rw [bundle_endOfKey_endKey, ← h21]; exact (BundleState.mem_ends B b2 (e, false)).mpr ⟨he_curr, rfl⟩)⟩
    · exact h2e1_in
  have hL2pre_len_w : L2pre.length < 2 ^ w := by
    dsimp only [L2pre]; split_ifs
    · have := List.length_erase_of_mem h2e_in; omega
    · exact hL2_len_w
  have hL2pre_dll_sz :
      IsDoublyLinkedList st_d1.mem (btEndPrevBase tbl slotCap eCap)
        (btEndNextBase tbl slotCap eCap) (bsHeadBase p + b2) (2 * eCap) L2pre ∧
      st_d1.mem (bsSizeBase p cap + b2) = L2pre.length := by
    dsimp only [L2pre]; split_ifs with h21
    · rw [h21]; exact ⟨hdll_d1, hsz_d1⟩
    · refine ⟨hL2_dll.of_agree ?_ ?_ ?_, ?_⟩
      · exact hfr_d1 _ (by unfold bsHeadBase; omega) (by unfold bsHeadBase bsSizeBase; omega)
          (by unfold bsHeadBase bsParentBase; omega) fun k hk => by
            have hk_lt := hL1_dll.2.1 k hk
            unfold bsHeadBase; unfold bundleSlotBlockSize at hblk_prev hblk_next
            exact ⟨by clear * - hblk_prev hb2_cap hk_lt; omega, by clear * - hblk_next hb2_cap hk_lt; omega⟩
      · intro k hk
        have hk_lt := hL2_dll.2.1 k hk
        exact hfr_d1 _ (by unfold bsHeadBase; unfold bundleSlotBlockSize at hblk_prev; clear * - hblk_prev hb1_cap hk_lt; omega)
          (by unfold bsSizeBase; unfold bundleSlotBlockSize at hblk_prev; clear * - hblk_prev hb1_cap hk_lt; omega)
          (by unfold bsParentBase; unfold bundleSlotBlockSize at hblk_prev; clear * - hblk_prev hb1_cap hk_lt; omega)
          fun k' hk' => by
            have hk'_lt := hL1_dll.2.1 k' hk'
            have hne_k : k ≠ k' := fun h => h21 (by
              have h1m := ((BundleState.mem_ends B b1 (endOfKey k')).mp ((hL1_mem k').mp hk')).2
              have h2m := ((BundleState.mem_ends B b2 (endOfKey k)).mp ((hL2_mem k).mp hk)).2
              rw [h] at h2m; exact h2m.symm.trans h1m)
            exact ⟨by omega, by clear * - hprev_next hk_lt hk'_lt; omega⟩
      · intro k hk
        have hk_lt := hL2_dll.2.1 k hk
        exact hfr_d1 _ (by unfold bsHeadBase; unfold bundleSlotBlockSize at hblk_next; clear * - hblk_next hb1_cap hk_lt; omega)
          (by unfold bsSizeBase; unfold bundleSlotBlockSize at hblk_next; clear * - hblk_next hb1_cap hk_lt; omega)
          (by unfold bsParentBase; unfold bundleSlotBlockSize at hblk_next; clear * - hblk_next hb1_cap hk_lt; omega)
          fun k' hk' => by
            have hk'_lt := hL1_dll.2.1 k' hk'
            have hne_k : k ≠ k' := fun h => h21 (by
              have h1m := ((BundleState.mem_ends B b1 (endOfKey k')).mp ((hL1_mem k').mp hk')).2
              have h2m := ((BundleState.mem_ends B b2 (endOfKey k)).mp ((hL2_mem k).mp hk)).2
              rw [h] at h2m; exact h2m.symm.trans h1m)
            exact ⟨by clear * - hprev_next hk_lt hk'_lt; omega, by omega⟩
      · exact (hfr_d1 _ (by unfold bsSizeBase bsHeadBase; omega) (by unfold bsSizeBase; omega)
          (by unfold bsSizeBase bsParentBase; omega) fun k hk => by
            have hk_lt := hL1_dll.2.1 k hk
            unfold bsSizeBase; unfold bundleSlotBlockSize at hblk_prev hblk_next
            exact ⟨by clear * - hblk_prev hb2_cap hk_lt; omega, by clear * - hblk_next hb2_cap hk_lt; omega⟩).trans hL2_sz
  have hend_2e1' : st_d1.mem (btEndBundleBase tbl slotCap eCap + (2 * e + 1)) = b2 :=
    (hfr_d1 _
      (by unfold btEndBundleBase bsHeadBase; clear * - hp_disj_tbl' he_lt hb1_cap; omega)
      (by unfold btEndBundleBase bsSizeBase; clear * - hp_disj_tbl' he_lt hb1_cap; omega)
      (by unfold btEndBundleBase bsParentBase; clear * - hp_disj_tbl' he_lt hb1_cap; omega)
      fun k hk => by
        have hk_lt := hL1_dll.2.1 k hk
        unfold btEndBundleBase btEndPrevBase btEndNextBase
        exact ⟨by clear * - he_lt hk_lt; omega, by clear * - he_lt hk_lt; omega⟩).trans hend_2e1
  obtain ⟨o_d2, st_d2, c_d2, hrun_d2, hpost_d2, hc_d2⟩ :=
    bundleDelEnd_triple (hbErase _ _ _ _ _) hw16 hprev_w hnext_w hprev_next hp_w
      hblk_prev hblk_next (by unfold btEndBundleBase; clear * - htbl_w' he_lt; omega)
      hb2_cap (by clear * - he_lt; omega) h2e1_in_pre holdH_w hL2pre_len_w
      hend_2e1' hL2pre_dll_sz.1 hL2pre_dll_sz.2 st_b2 ω
      ⟨rfl, rfl,
        by simp [st_b2, r_b2, r_b1]; rw [hreg_d1 7 (by decide) (by decide) (by decide)]; simp [st_a5, r_a5, r_a4, r_a3, r_a2, r_a1, r7],
        by simp [st_b2, r_b2, r_b1]; rw [hreg_d1 8 (by decide) (by decide) (by decide)]; simp [st_a5, r_a5, r_a4, r_a3, r_a2, r_a1, r8],
        by simp [st_b2, r_b2, r_b1]; rw [hreg_d1 9 (by decide) (by decide) (by decide)]; simp [st_a5, r_a5, r_a4, r_a3, r_a2, r_a1, r9],
        by simp [st_b2, r_b2, r_b1]; rw [hreg_d1 18 (by decide) (by decide) (by decide)]; simp [st_a5, r_a5, r_a4, r_a3, r_a2],
        by simp [st_b2, r_b2, r_b1]; rw [hreg_d1 19 (by decide) (by decide) (by decide)]; simp [st_a5, r_a5, r_a4, r_a3],
        by simp [st_b2, r_b2, r_b1], by simp [st_b2, r_b2]⟩
  cases o_d2 with
  | returned _ => exact False.elim hpost_d2
  | normal =>
  rcases hpost_d2 with ⟨hreg_d2, hdll_d2, hsz_d2, hpar0_d2, _, hfr_d2⟩
  have hreg2 : ∀ r, r ≤ 19 → st_d2.regs r = r_a5 r := fun r hr => by
    rw [hreg_d2 r (by omega) (by omega) (by omega)]
    have hne20 : r ≠ 20 := by omega
    have hne24 : r ≠ 24 := by omega
    simp only [st_b2, r_b2, r_b1, Function.update_of_ne hne24, Function.update_of_ne hne20]
    exact hreg_d1 r (by omega) (by omega) (by omega)
  have hd2_r0 : st_d2.regs 0 = tbl := by rw [hreg2 0 (by decide)]; simp [r_a5, r_a4, r_a3, r_a2, r_a1, r0]
  have hd2_r1 : st_d2.regs 1 = delCount := by rw [hreg2 1 (by decide)]; simp [r_a5, r_a4, r_a3, r_a2, r_a1, r1]
  have hd2_r2 : st_d2.regs 2 = delPtr := by rw [hreg2 2 (by decide)]; simp [r_a5, r_a4, r_a3, r_a2, r_a1, r2]
  have hd2_r3 : st_d2.regs 3 = touchedBufPtr := by rw [hreg2 3 (by decide)]; simp [r_a5, r_a4, r_a3, r_a2, r_a1, r3]
  have hd2_r5 : st_d2.regs 5 = btSlotPtrBase tbl := by rw [hreg2 5 (by decide)]; simp [r_a5, r_a4, r_a3, r_a2, r_a1, r5]
  have hd2_r6 : st_d2.regs 6 = btEdgeSlotBase tbl slotCap := by rw [hreg2 6 (by decide)]; simp [r_a5, r_a4, r_a3, r_a2, r_a1, r6]
  have hd2_r7 : st_d2.regs 7 = btEndBundleBase tbl slotCap eCap := by rw [hreg2 7 (by decide)]; simp [r_a5, r_a4, r_a3, r_a2, r_a1, r7]
  have hd2_r8 : st_d2.regs 8 = btEndPrevBase tbl slotCap eCap := by rw [hreg2 8 (by decide)]; simp [r_a5, r_a4, r_a3, r_a2, r_a1, r8]
  have hd2_r9 : st_d2.regs 9 = btEndNextBase tbl slotCap eCap := by rw [hreg2 9 (by decide)]; simp [r_a5, r_a4, r_a3, r_a2, r_a1, r9]
  have hd2_r10 : st_d2.regs 10 = btSlotTouchedBase tbl slotCap eCap := by rw [hreg2 10 (by decide)]; simp [r_a5, r_a4, r_a3, r_a2, r_a1, r10]
  have hd2_r11 : st_d2.regs 11 = btSlotDelHeadBase tbl slotCap eCap := by rw [hreg2 11 (by decide)]; simp [r_a5, r_a4, r_a3, r_a2, r_a1, r11]
  have hd2_r12 : st_d2.regs 12 = btSlotDelNextBase tbl slotCap eCap := by rw [hreg2 12 (by decide)]; simp [r_a5, r_a4, r_a3, r_a2, r_a1, r12]
  have hd2_r13 : st_d2.regs 13 = touched.length := by rw [hreg2 13 (by decide)]; simp [r_a5, r_a4, r_a3, r_a2, r_a1, r13]
  have hd2_r14 : st_d2.regs 14 = i := by rw [hreg2 14 (by decide)]; simp [r_a5, r_a4, r_a3, r_a2, r_a1, r14]
  have hd2_r15 : st_d2.regs 15 = e := by rw [hreg2 15 (by decide)]; simp [r_a5, r_a4, r_a3, r_a2, r_a1, r15]
  have hd2_r17 : st_d2.regs 17 = js.1 := by rw [hreg2 17 (by decide)]; simp [r_a5, r_a4, r_a3, r_a2, r_a1]
  have hd2_r18 : st_d2.regs 18 = p := by rw [hreg2 18 (by decide)]; simp [r_a5, r_a4, r_a3, r_a2]
  -- Trailing 7 statements + cond
  have hd2_fixed_eq : ∀ a, tbl ≤ a → a < tbl + bundleTableFixedSize slotCap eCap →
      (a < btEndPrevBase tbl slotCap eCap ∨ btEndPrevBase tbl slotCap eCap + 2 * eCap ≤ a) →
      (a < btEndNextBase tbl slotCap eCap ∨ btEndNextBase tbl slotCap eCap + 2 * eCap ≤ a) →
      st_d2.mem a = st2.mem a := fun a ha1 ha2 hnp hnn =>
    (hfr_d2 a
      (by unfold bsHeadBase; unfold bundleTableFixedSize at ha2; clear * - ha1 ha2 hp_disj_tbl' hb2_cap; omega)
      (by unfold bsSizeBase; unfold bundleTableFixedSize at ha2; clear * - ha1 ha2 hp_disj_tbl' hb2_cap; omega)
      (by unfold bsParentBase; unfold bundleTableFixedSize at ha2; clear * - ha1 ha2 hp_disj_tbl' hb2_cap; omega)
      (fun k hk => have := hL2pre_dll_sz.1.2.1 k hk; ⟨by omega, by omega⟩)).trans
    (hfr_d1 a
      (by unfold bsHeadBase; unfold bundleTableFixedSize at ha2; clear * - ha1 ha2 hp_disj_tbl' hb1_cap; omega)
      (by unfold bsSizeBase; unfold bundleTableFixedSize at ha2; clear * - ha1 ha2 hp_disj_tbl' hb1_cap; omega)
      (by unfold bsParentBase; unfold bundleTableFixedSize at ha2; clear * - ha1 ha2 hp_disj_tbl' hb1_cap; omega)
      (fun k hk => have := hL1_dll.2.1 k hk; ⟨by omega, by omega⟩))
  have hnE_w : B.edges.card < 2 ^ w := by
    have hle : B.edges.card ≤ eCap := by
      simpa using Finset.card_le_card (show B.edges ⊆ Finset.range eCap from
        fun x hx => Finset.mem_range.mpr (hE x hx))
    clear * - hle htbl_w'; omega
  have hp2_d2 : st_d2.mem (p + 2) = B.edges.card := by
    rw [hfr_d2 (p + 2) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
        (by unfold bsParentBase; omega)
        (fun k hk => by have := hL2pre_dll_sz.1.2.1 k hk; unfold bundleSlotBlockSize at hblk_prev hblk_next; exact ⟨by clear * - hblk_prev this; omega, by clear * - hblk_next this; omega⟩),
      hfr_d1 (p + 2) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
        (by unfold bsParentBase; omega)
        (fun k hk => by have := hL1_dll.2.1 k hk; unfold bundleSlotBlockSize at hblk_prev hblk_next; exact ⟨by clear * - hblk_prev this; omega, by clear * - hblk_next this; omega⟩)]
    simpa [bsOffNE] using h2
  set oldDelHead := st2.mem (btSlotDelHeadBase tbl slotCap eCap + js.1)
  have hdelHead_d2 : st_d2.mem (btSlotDelHeadBase tbl slotCap eCap + js.1) = oldDelHead :=
    hd2_fixed_eq _ (by unfold btSlotDelHeadBase; omega)
      (by unfold btSlotDelHeadBase bundleTableFixedSize; clear * - hjs_lt; omega)
      (Or.inr (by unfold btSlotDelHeadBase btEndPrevBase; omega))
      (Or.inr (by unfold btSlotDelHeadBase btEndNextBase; omega))
  set oldFlag := st2.mem (btSlotTouchedBase tbl slotCap eCap + js.1)
  have hflag_eq : oldFlag = if js.1 ∈ touched then 1 else 0 := atouch_flag js.1 js.2
  have hflag_d2 : st_d2.mem (btSlotTouchedBase tbl slotCap eCap + js.1) = oldFlag :=
    hd2_fixed_eq _ (by unfold btSlotTouchedBase; omega)
      (by unfold btSlotTouchedBase bundleTableFixedSize; clear * - hjs_lt; omega)
      (Or.inr (by unfold btSlotTouchedBase btEndPrevBase; omega))
      (Or.inr (by unfold btSlotTouchedBase btEndNextBase; omega))
  set a_es := btEdgeSlotBase tbl slotCap + e
  set a_nE := p + 2
  set a_dn := btSlotDelNextBase tbl slotCap eCap + e
  set a_dh := btSlotDelHeadBase tbl slotCap eCap + js.1
  set a_tf := btSlotTouchedBase tbl slotCap eCap + js.1
  set a_tb := touchedBufPtr + touched.length
  have ha_es_w : a_es < 2 ^ w := by unfold a_es btEdgeSlotBase; clear * - he_lt htbl_w'; omega
  have ha_nE_w : a_nE < 2 ^ w := by unfold a_nE; clear * - hp_w'; omega
  have ha_dn_w : a_dn < 2 ^ w := by unfold a_dn btSlotDelNextBase; clear * - he_lt htbl_w'; omega
  have ha_dh_w : a_dh < 2 ^ w := by unfold a_dh btSlotDelHeadBase; clear * - hjs_lt htbl_w'; omega
  have ha_tf_w : a_tf < 2 ^ w := by unfold a_tf btSlotTouchedBase; clear * - hjs_lt htbl_w'; omega
  have he1_w : e + 1 < 2 ^ w := by clear * - he_lt htbl_w'; omega
  have hne_es_nE : a_es ≠ a_nE := by unfold a_es a_nE btEdgeSlotBase; clear * - hp_disj_tbl' he_lt; omega
  have hne_dh_es : a_dh ≠ a_es := by unfold a_dh a_es btSlotDelHeadBase btEdgeSlotBase; clear * - he_lt; omega
  have hne_dh_nE : a_dh ≠ a_nE := by unfold a_dh a_nE btSlotDelHeadBase; clear * - hp_disj_tbl' hjs_lt; omega
  have hne_tf_es : a_tf ≠ a_es := by unfold a_tf a_es btSlotTouchedBase btEdgeSlotBase; clear * - he_lt; omega
  have hne_tf_nE : a_tf ≠ a_nE := by unfold a_tf a_nE btSlotTouchedBase; clear * - hp_disj_tbl' hjs_lt; omega
  have hne_tf_dn : a_tf ≠ a_dn := by unfold a_tf a_dn btSlotTouchedBase btSlotDelNextBase; clear * - hjs_lt; omega
  have hne_tf_dh : a_tf ≠ a_dh := by unfold a_tf a_dh btSlotTouchedBase btSlotDelHeadBase; clear * - hjs_lt; omega
  set mem_t1 := Function.update st_d2.mem a_es 0
  set mem_t2 := Function.update mem_t1 a_nE (B.edges.card - 1)
  set mem_t3 := Function.update mem_t2 a_dn oldDelHead
  set mem_t4 := Function.update mem_t3 a_dh (e + 1)
  set regs_t1 := Function.update st_d2.regs 23 B.edges.card
  set regs_t2 := Function.update regs_t1 24 oldDelHead
  set regs_t3 := Function.update regs_t2 24 oldFlag
  set st_t4 : State := { st_d2 with mem := mem_t4, regs := regs_t3 }
  have hrun_tail_cps : ∀ {sTail : Stmt} {stF : State} {cTail : ℕ},
      Runs w pProg ω sTail st_t4 .normal stF cTail →
      Runs w pProg ω
        (.store (.bin .add (.reg 6) (.reg 15)) (.const 0) ;;
         .assign 23 (.load (.bin .add (.reg 18) (.const 2))) ;;
         .store (.bin .add (.reg 18) (.const 2)) (.bin .sub (.reg 23) (.const 1)) ;;
         .assign 24 (.load (.bin .add (.reg 11) (.reg 17))) ;;
         .store (.bin .add (.reg 12) (.reg 15)) (.reg 24) ;;
         .store (.bin .add (.reg 11) (.reg 17)) (.bin .add (.reg 15) (.const 1)) ;;
         .assign 24 (.load (.bin .add (.reg 10) (.reg 17))) ;;
         sTail) st_d2 .normal stF (46 + cTail) := by
    intro sTail stF cTail hTail
    have hs1 : Runs w pProg ω (.store (.bin .add (.reg 6) (.reg 15)) (.const 0))
        st_d2 .normal { st_d2 with mem := mem_t1 } 5 :=
      runs_store_iff.mpr ⟨a_es, 0, by simp [Expr.eval, BinOp.eval, hd2_r6, hd2_r15, a_es, ha_es_w],
        by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
    have hs2 : Runs w pProg ω (.assign 23 (.load (.bin .add (.reg 18) (.const 2))))
        { st_d2 with mem := mem_t1 } .normal { st_d2 with mem := mem_t1, regs := regs_t1 } 5 :=
      runs_assign_iff.mpr ⟨B.edges.card, by
        have hm1 : mem_t1 (p + 2) = B.edges.card :=
          (Function.update_of_ne hne_es_nE.symm _ _).trans hp2_d2
        simp [Expr.eval, BinOp.eval, hd2_r18, h2_w, show p + 2 < 2 ^ w from ha_nE_w, hm1], rfl, rfl, rfl⟩
    have hs3 : Runs w pProg ω (.store (.bin .add (.reg 18) (.const 2)) (.bin .sub (.reg 23) (.const 1)))
        { st_d2 with mem := mem_t1, regs := regs_t1 } .normal
        { st_d2 with mem := mem_t2, regs := regs_t1 } 7 :=
      runs_store_iff.mpr ⟨a_nE, B.edges.card - 1,
        by simp [Expr.eval, BinOp.eval, regs_t1, hd2_r18, h2_w, a_nE, ha_nE_w],
        by simp [Expr.eval, BinOp.eval, regs_t1, h1_w, show B.edges.card - 1 < 2 ^ w by omega],
        rfl, rfl, rfl⟩
    have hs4 : Runs w pProg ω (.assign 24 (.load (.bin .add (.reg 11) (.reg 17))))
        { st_d2 with mem := mem_t2, regs := regs_t1 } .normal
        { st_d2 with mem := mem_t2, regs := regs_t2 } 5 :=
      runs_assign_iff.mpr ⟨oldDelHead, by
        have hm2 : mem_t2 (btSlotDelHeadBase tbl slotCap eCap + js.1) = oldDelHead :=
          ((Function.update_of_ne hne_dh_nE _ _).trans (Function.update_of_ne hne_dh_es _ _)).trans hdelHead_d2
        simp [Expr.eval, BinOp.eval, regs_t1, hd2_r11, hd2_r17,
          show btSlotDelHeadBase tbl slotCap eCap + js.1 < 2 ^ w from ha_dh_w, hm2],
        rfl, rfl, rfl⟩
    have hs5 : Runs w pProg ω (.store (.bin .add (.reg 12) (.reg 15)) (.reg 24))
        { st_d2 with mem := mem_t2, regs := regs_t2 } .normal
        { st_d2 with mem := mem_t3, regs := regs_t2 } 5 :=
      runs_store_iff.mpr ⟨a_dn, oldDelHead,
        by simp [Expr.eval, BinOp.eval, regs_t2, regs_t1, hd2_r12, hd2_r15, a_dn, ha_dn_w],
        by simp [Expr.eval, regs_t2], rfl, rfl, rfl⟩
    have hs6 : Runs w pProg ω (.store (.bin .add (.reg 11) (.reg 17)) (.bin .add (.reg 15) (.const 1)))
        { st_d2 with mem := mem_t3, regs := regs_t2 } .normal
        { st_d2 with mem := mem_t4, regs := regs_t2 } 7 :=
      runs_store_iff.mpr ⟨a_dh, e + 1,
        by simp [Expr.eval, BinOp.eval, regs_t2, regs_t1, hd2_r11, hd2_r17, a_dh, ha_dh_w],
        by simp [Expr.eval, BinOp.eval, regs_t2, regs_t1, hd2_r15, h1_w, he1_w], rfl, rfl, rfl⟩
    have hs7 : Runs w pProg ω (.assign 24 (.load (.bin .add (.reg 10) (.reg 17))))
        { st_d2 with mem := mem_t4, regs := regs_t2 } .normal st_t4 5 :=
      runs_assign_iff.mpr ⟨oldFlag, by
        have hm4 : mem_t4 (btSlotTouchedBase tbl slotCap eCap + js.1) = oldFlag :=
          ((((Function.update_of_ne hne_tf_dh _ _).trans (Function.update_of_ne hne_tf_dn _ _)).trans
            (Function.update_of_ne hne_tf_nE _ _)).trans (Function.update_of_ne hne_tf_es _ _)).trans hflag_d2
        simp [Expr.eval, BinOp.eval, regs_t2, regs_t1, hd2_r10, hd2_r17,
          show btSlotTouchedBase tbl slotCap eCap + js.1 < 2 ^ w from ha_tf_w, hm4], rfl, rfl, rfl⟩
    exact (show 5 + (5 + (7 + (5 + (5 + (7 + (5 + cTail + 1) + 1) + 1) + 1) + 1) + 1) + 1 = 46 + cTail by omega) ▸
      bundle_runs_seq_normal hs1 (bundle_runs_seq_normal hs2 (bundle_runs_seq_normal hs3
        (bundle_runs_seq_normal hs4 (bundle_runs_seq_normal hs5 (bundle_runs_seq_normal hs6 (bundle_runs_seq_normal hs7 hTail))))))
  set sCond : Stmt :=
    .cond (.bin .eq (.reg 24) (.const 0))
      (.store (.bin .add (.reg 10) (.reg 17)) (.const 1) ;;
       .store (.bin .add (.reg 3) (.reg 13)) (.reg 17) ;;
       .assign 13 (.bin .add (.reg 13) (.const 1))) .nop
  have hcond_ex : ∃ st_f c_f,
      Runs w pProg ω sCond st_t4 .normal st_f c_f ∧ c_f ≤ 20 ∧
      (∀ r, r ≤ 14 → r ≠ 13 → st_f.regs r = st_d2.regs r) ∧
      st_f.regs 13 = touched'.length ∧
      (js.1 ∈ touched → st_f.mem = mem_t4) ∧
      (js.1 ∉ touched → st_f.mem = Function.update (Function.update mem_t4 a_tf 1) a_tb js.1) := by
    by_cases hmem_t : js.1 ∈ touched
    · have hof : oldFlag = 1 := by simp only [hflag_eq, hmem_t, ↓reduceIte]
      have hcond : Runs w pProg ω sCond st_t4 .normal st_t4 5 :=
        runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, BinOp.eval, st_t4, regs_t3, hof],
          by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
      refine ⟨st_t4, 5, hcond, by omega,
        fun r hr _ => by simp [st_t4, regs_t3, regs_t2, regs_t1, show r ≠ 24 by omega, show r ≠ 23 by omega],
        by simp [st_t4, regs_t3, regs_t2, regs_t1, hd2_r13, touched', hmem_t],
        fun _ => rfl, fun h => absurd hmem_t h⟩
    · have hof : oldFlag = 0 := by simp only [hflag_eq, hmem_t, ↓reduceIte]
      have htlen_lt : touched.length < slotCap := by
        have hsub : touched.toFinset ⊂ Finset.range slotCap :=
          Finset.ssubset_iff_subset_ne.mpr
            ⟨fun x hx => Finset.mem_range.mpr (atouch_lt x (List.mem_toFinset.mp hx)),
             fun heq => hmem_t (List.mem_toFinset.mp (heq ▸ Finset.mem_range.mpr js.2))⟩
        have := Finset.card_lt_card hsub
        rwa [List.toFinset_card_of_nodup atouch_nd, Finset.card_range] at this
      have ha_tb_w : a_tb < 2 ^ w := by unfold a_tb; clear * - htlen_lt htouch_w; omega
      have htl1_w : touched.length + 1 < 2 ^ w := by clear * - htlen_lt htbl_w'; omega
      set mem_f1 := Function.update mem_t4 a_tf 1
      set mem_f2 := Function.update mem_f1 a_tb js.1
      set regs_f := Function.update regs_t3 13 (touched.length + 1)
      set st_f : State := { st_t4 with mem := mem_f2, regs := regs_f }
      have h1 : Runs w pProg ω (.store (.bin .add (.reg 10) (.reg 17)) (.const 1))
          st_t4 .normal { st_t4 with mem := mem_f1 } 5 :=
        runs_store_iff.mpr ⟨a_tf, 1,
          by simp [Expr.eval, BinOp.eval, st_t4, regs_t3, regs_t2, regs_t1, hd2_r10, hd2_r17, a_tf, ha_tf_w],
          by simp [Expr.eval, h1_w], rfl, rfl, rfl⟩
      have h2 : Runs w pProg ω (.store (.bin .add (.reg 3) (.reg 13)) (.reg 17))
          { st_t4 with mem := mem_f1 } .normal { st_t4 with mem := mem_f2 } 5 :=
        runs_store_iff.mpr ⟨a_tb, js.1,
          by simp [Expr.eval, BinOp.eval, st_t4, regs_t3, regs_t2, regs_t1, hd2_r3, hd2_r13, a_tb, ha_tb_w],
          by simp [Expr.eval, st_t4, regs_t3, regs_t2, regs_t1, hd2_r17], rfl, rfl, rfl⟩
      have h3 : Runs w pProg ω (.assign 13 (.bin .add (.reg 13) (.const 1)))
          { st_t4 with mem := mem_f2 } .normal st_f 4 :=
        runs_assign_iff.mpr ⟨touched.length + 1,
          by simp [Expr.eval, BinOp.eval, st_t4, regs_t3, regs_t2, regs_t1, hd2_r13, h1_w, htl1_w],
          rfl, rfl, rfl⟩
      have hcond : Runs w pProg ω sCond st_t4 .normal st_f 20 :=
        runs_cond_iff.mpr ⟨1, 16, by simp [Expr.eval, BinOp.eval, st_t4, regs_t3, hof, h1_w],
          by simpa using bundle_runs_seq_normal h1 (bundle_runs_seq_normal h2 h3), rfl⟩
      refine ⟨st_f, 20, hcond, by omega,
        fun r hr hne13 => by simp [st_f, regs_f, regs_t3, regs_t2, regs_t1, hne13, show r ≠ 24 by omega, show r ≠ 23 by omega],
        by simp [st_f, regs_f, touched', hmem_t],
        fun h => absurd h hmem_t, fun _ => rfl⟩
  obtain ⟨st_f, c_f, hrun_cond, hc_f, hreg_f, hr13_f, hmem_f_in, hmem_f_out⟩ := hcond_ex
  have hrun_all : Runs w pProg ω (bundleStepDelActiveStmt bDllErase) st2 .normal st_f
      (30 + (c_d1 + (17 + (c_d2 + (46 + c_f) + 1)) + 1)) := by
    dsimp only [bundleStepDelActiveStmt]
    exact hrun_pre_cps (bundle_runs_seq_normal hrun_d1 (hrun_mid_cps (bundle_runs_seq_normal hrun_d2 (hrun_tail_cps hrun_cond))))
  obtain ⟨hafter', htouch', hfr'⟩ :=
    bundleStepDel_active_post htouch_disj_foot he_lt hSjs heB₀ he_not_D hm_js
      hafter_copy htouch_mem rfl rfl hL1_dll.1 hL2_dll.1 hL1_dll.2.1 hL2_dll.2.1
      hL1_mem hL2_mem hdll_d1 hsz_d1 (fun h => (hpar0_d1 h).trans hparT) hfr_d1
      hdll_d2 hsz_d2 (fun h => (hpar0_d2 h).trans hparH) hfr_d2 ⟨hmem_f_in, hmem_f_out⟩
  dsimp only at hc_d1 hc_d2
  exact ⟨st_f, _, hrun_all,
    by rw [hreg_f 0 (by decide) (by decide)]; exact hd2_r0,
    by rw [hreg_f 1 (by decide) (by decide)]; exact hd2_r1,
    by rw [hreg_f 2 (by decide) (by decide)]; exact hd2_r2,
    by rw [hreg_f 3 (by decide) (by decide)]; exact hd2_r3,
    by rw [hreg_f 5 (by decide) (by decide)]; exact hd2_r5,
    by rw [hreg_f 6 (by decide) (by decide)]; exact hd2_r6,
    by rw [hreg_f 7 (by decide) (by decide)]; exact hd2_r7,
    by rw [hreg_f 8 (by decide) (by decide)]; exact hd2_r8,
    by rw [hreg_f 9 (by decide) (by decide)]; exact hd2_r9,
    by rw [hreg_f 10 (by decide) (by decide)]; exact hd2_r10,
    by rw [hreg_f 11 (by decide) (by decide)]; exact hd2_r11,
    by rw [hreg_f 12 (by decide) (by decide)]; exact hd2_r12,
    hr13_f, by rw [hreg_f 14 (by decide) (by decide)]; exact hd2_r14,
    hafter', htouch', hfr', by omega⟩

end

end MinCostFlow.SparseCore.Program
