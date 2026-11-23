module

public import MinCostFlow.SparseCore.Program.BundleStepScanPassBPost

/-!
# Verification of Pass B in Phase 2 (`BundleStepScanPassB`)

Proves `bundleStepScanPassB_runs`, verifying `bundleStepScanPassBStmt` using the memory invariant
transitions in `BundleStepScanPassBPost`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

public section
open Classical

private lemma seenVisited_take_succ_iff {slotCap : ℕ} {S : BundleTableState slotCap} {xs : List End}
    {t : ℕ} (ht : t < xs.length) (j : Fin slotCap) (b : ℕ) :
    seenVisited S xs (t + 1) j b ↔
      seenVisited S xs t j b ∨ match S j with | none => False | some B => xs[t] ∈ B.ends b := by
  unfold seenVisited
  cases S j with
  | none => simp
  | some B =>
    simp only [List.take_succ_eq_append_getElem ht, List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨y, hy | rfl, hyb⟩
      · exact Or.inl ⟨y, hy, hyb⟩
      · exact Or.inr hyb
    · rintro (⟨y, hy, hyb⟩ | hxb)
      · exact ⟨y, Or.inl hy, hyb⟩
      · exact ⟨xs[t], Or.inr rfl, hxb⟩

private lemma dll_len_eq_card_ends {eCap prevBase nextBase hd : ℕ} {mem : ℕ → ℕ}
    {B : BundleState} {b : ℕ} {L : List ℕ}
    (hL : IsDoublyLinkedList mem prevBase nextBase hd (2 * eCap) L)
    (hmem : ∀ k, k ∈ L ↔ endOfKey k ∈ B.ends b) :
    L.length = (B.ends b).card := by
  rw [← List.toFinset_card_of_nodup hL.1]
  refine Finset.card_bij (fun k _ => endOfKey k)
    (fun k hk => (hmem k).mp (List.mem_toFinset.mp hk))
    (fun k1 _ k2 _ heq => by
      have h1 := bundle_endKey_endOfKey k1; have h2 := bundle_endKey_endOfKey k2
      rw [heq] at h1; exact h1.symm.trans h2)
    (fun x hx => ⟨endKey x, List.mem_toFinset.mpr ((hmem (endKey x)).mpr (by rwa [bundle_endOfKey_endKey])),
      bundle_endOfKey_endKey x⟩)

/-- Verifies `bundleStepScanPassBStmt`: zeroes `seen[b]` for every end in `xs` and enqueues every
bundle `b` with `0 < seenCount < |B.ends b|` into `slotCandHead`/`candNext` (and `touched`). -/
lemma bundleStepScanPassB_runs {w slotCap vCap eCap tbl listPtr touchedBufPtr : ℕ}
    {pProg : Program} {S₀ : BundleTableState slotCap} {D : Finset ℕ}
    {m : BundleTableMeta slotCap} {cand₀ : Fin slotCap → Finset ℕ} {touched₀ : List ℕ}
    {xs : List End} {mem₀ : ℕ → ℕ} {st₀ : State} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (htbl_w : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w)
    (hblks_w : ∀ j : Fin slotCap, ∀ p c, m.slotBlocks j = some (p, c) →
      p + bundleSlotBlockSize c < 2 ^ w)
    (hlist_w : listPtr + 1 + xs.length < 2 ^ w)
    (htouch_w : touchedBufPtr + slotCap < 2 ^ w)
    (hlist_disj_foot : ∀ a, listPtr ≤ a → a < listPtr + 1 + xs.length → ¬ bundleTableFoot eCap tbl m a)
    (hlist_disj_touch : ∀ a, listPtr ≤ a → a < listPtr + 1 + xs.length →
      a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a)
    (htouch_disj_foot : ∀ a, touchedBufPtr ≤ a → a < touchedBufPtr + slotCap →
      ¬ bundleTableCoreFoot eCap tbl m a)
    (hlist_mem : EndListAt mem₀ listPtr xs)
    (hxs_lt : ∀ x ∈ xs, x.1 < eCap) (_hxs_nd : xs.Nodup)
    (hafter₀ : BundleTableAfterScan slotCap vCap eCap tbl S₀ D m cand₀ touched₀ mem₀)
    (htouch₀ : ListAt mem₀ touchedBufPtr touched₀)
    (hseenA : ∀ j : Fin slotCap, ∀ B p cap, tableDelEdges S₀ D j = some B →
      m.slotBlocks j = some (p, cap) →
      ∀ b < cap, st₀.mem (bsSeenBase p cap + b) = seenCount (tableDelEdges S₀ D) xs j b)
    (hfrA : ∀ a, ¬ isSeenAddr m a → st₀.mem a = mem₀ a)
    (hr5 : st₀.regs 5 = touchedBufPtr)
    (hr7 : st₀.regs 7 = btSlotPtrBase tbl)
    (hr8 : st₀.regs 8 = btEdgeSlotBase tbl slotCap)
    (hr9 : st₀.regs 9 = btEndBundleBase tbl slotCap eCap)
    (hr10 : st₀.regs 10 = btSlotTouchedBase tbl slotCap eCap)
    (hr11 : st₀.regs 11 = btSlotCandHeadBase tbl slotCap eCap)
    (hr13 : st₀.regs 13 = touched₀.length)
    (hr21 : st₀.regs 21 = listPtr) (hr22 : st₀.regs 22 = xs.length) :
    let S := tableDelEdges S₀ D
    ∃ touched' st' c,
      Runs w pProg ω bundleStepScanPassBStmt st₀ .normal st' c ∧
      (∀ r, r ≤ 22 → r ≠ 13 → st'.regs r = st₀.regs r) ∧
      st'.regs 13 = touched'.length ∧
      BundleTableAfterScan slotCap vCap eCap tbl S₀ D m (passBCands S xs xs.length cand₀) touched' st'.mem ∧
      ListAt st'.mem touchedBufPtr touched' ∧
      (∀ a, ¬ bundleTableCoreFoot eCap tbl m a →
        (a < touchedBufPtr ∨ touchedBufPtr + slotCap ≤ a) → st'.mem a = mem₀ a) ∧
      c ≤ 165 * xs.length + 12 := by
  intro S
  have hafter₀_copy := hafter₀
  rcases hafter₀ with ⟨_, _, _, _, _, _, _, _, _, _, _, _,
    hdisjE, hedgeSlot, hendBun, hslots, hdisjB, _, _, _, _, _⟩
  have htbl_w' : tbl + (14 + 7 * slotCap + 8 * eCap) < 2 ^ w := htbl_w
  have h1_w : 1 < 2 ^ w := by clear * - hw16; omega
  have h2_w : 2 < 2 ^ w := by clear * - hw16; omega
  have h3_w : 3 < 2 ^ w := by clear * - hw16; omega
  have h4_w : 4 < 2 ^ w := by clear * - hw16; omega
  have h5_w : 5 < 2 ^ w := by clear * - hw16; omega
  have hblks_disj_tbl : ∀ j : Fin slotCap, ∀ p' c', m.slotBlocks j = some (p', c') →
      p' + bundleSlotBlockSize c' ≤ tbl ∨ tbl + bundleTableFixedSize slotCap eCap ≤ p' := by
    intro j p' c' hm'
    have hj := hslots j
    cases hSj : tableDelEdges S₀ D j with
    | none => simp only [hSj, hm'] at hj
    | some B => simp only [hSj, hm'] at hj; exact hj.2.2
  have hnotB_fixed_ro : ∀ a, tbl ≤ a → a < tbl + bundleTableCoreSize slotCap eCap →
      (∀ s < slotCap, a ≠ btSlotCandHeadBase tbl slotCap eCap + s ∧
        a ≠ btSlotTouchedBase tbl slotCap eCap + s) →
      ¬ isPassBAddr eCap tbl touchedBufPtr m a := by
    intro a ha1 ha2 hns hB
    rcases hB with ⟨j, p, cap, b, hm, hb, hcase⟩ | ⟨s, hs, hcase⟩ | ⟨ht1, ht2⟩
    · have hdj : p + (3 + 6 * cap) ≤ tbl ∨ tbl + (14 + 7 * slotCap + 8 * eCap) ≤ p := hblks_disj_tbl j p cap hm
      unfold bundleTableCoreSize at ha2
      rcases hcase with rfl | rfl | rfl
      · unfold bsSeenBase at ha1 ha2; clear * - ha1 ha2 hdj hb; omega
      · unfold bsInCandBase at ha1 ha2; clear * - ha1 ha2 hdj hb; omega
      · unfold bsCandNextBase at ha1 ha2; clear * - ha1 ha2 hdj hb; omega
    · rcases hcase with rfl | rfl
      · exact (hns s hs).1 rfl
      · exact (hns s hs).2 rfl
    · exact htouch_disj_foot a ht1 ht2 (Or.inl ⟨ha1, ha2⟩)
  have hnotB_blk_ro : ∀ (j : Fin slotCap) p cap a, m.slotBlocks j = some (p, cap) →
      p ≤ a → a < p + 3 + 3 * cap → ¬ isPassBAddr eCap tbl touchedBufPtr m a := by
    intro j p cap a hm ha1 ha2 hB
    have hfoot_a : bundleTableCoreFoot eCap tbl m a := Or.inr ⟨j, p, cap, hm, ha1, by unfold bundleSlotBlockSize; omega⟩
    rcases hB with ⟨j', p', cap', b', hm', hb', hcase⟩ | ⟨s, hs, hcase⟩ | ⟨ht1, ht2⟩
    · by_cases hjj : j' = j
      · subst j'; rw [hm] at hm'; cases hm'
        rcases hcase with rfl | rfl | rfl
        · unfold bsSeenBase at ha1 ha2; omega
        · unfold bsInCandBase at ha1 ha2; omega
        · unfold bsCandNextBase at ha1 ha2; omega
      · have hdj := hdisjB j' j hjj p' cap' p cap hm' hm
        unfold bundleSlotBlockSize at hdj
        rcases hcase with rfl | rfl | rfl
        · unfold bsSeenBase at ha1 ha2; clear * - hdj ha1 ha2 hb'; omega
        · unfold bsInCandBase at ha1 ha2; clear * - hdj ha1 ha2 hb'; omega
        · unfold bsCandNextBase at ha1 ha2; clear * - hdj ha1 ha2 hb'; omega
    · have hdj : p + (3 + 6 * cap) ≤ tbl ∨ tbl + (14 + 7 * slotCap + 8 * eCap) ≤ p := hblks_disj_tbl j p cap hm
      rcases hcase with rfl | rfl
      · unfold btSlotCandHeadBase at ha1 ha2; clear * - hdj ha1 ha2 hs; omega
      · unfold btSlotTouchedBase at ha1 ha2; clear * - hdj ha1 ha2 hs; omega
    · exact htouch_disj_foot a ht1 ht2 hfoot_a
  have hnotB_list : ∀ t < xs.length, ¬ isPassBAddr eCap tbl touchedBufPtr m (listPtr + 1 + t) := by
    intro t ht hB
    have hnf := hlist_disj_foot (listPtr + 1 + t) (by omega) (by omega)
    have hnt := hlist_disj_touch (listPtr + 1 + t) (by omega) (by omega)
    rcases hB with ⟨j, p, cap, b, hm, hb, hcase⟩ | ⟨s, hs, hcase⟩ | ⟨ht1, ht2⟩
    · rcases hcase with h | h | h
      · have hf : bundleTableFoot eCap tbl m (bsSeenBase p cap + b) :=
          Or.inr ⟨j, p, cap, hm, by unfold bsSeenBase; omega, by unfold bsSeenBase bundleSlotBlockSize; omega⟩
        exact hnf (h ▸ hf)
      · have hf : bundleTableFoot eCap tbl m (bsInCandBase p cap + b) :=
          Or.inr ⟨j, p, cap, hm, by unfold bsInCandBase; omega, by unfold bsInCandBase bundleSlotBlockSize; omega⟩
        exact hnf (h ▸ hf)
      · have hf : bundleTableFoot eCap tbl m (bsCandNextBase p cap + b) :=
          Or.inr ⟨j, p, cap, hm, by unfold bsCandNextBase; omega, by unfold bsCandNextBase bundleSlotBlockSize; omega⟩
        exact hnf (h ▸ hf)
    · rcases hcase with h | h
      · have hf : bundleTableFoot eCap tbl m (btSlotCandHeadBase tbl slotCap eCap + s) :=
          Or.inl ⟨by unfold btSlotCandHeadBase; omega, by unfold btSlotCandHeadBase bundleTableFixedSize; omega⟩
        exact hnf (h ▸ hf)
      · have hf : bundleTableFoot eCap tbl m (btSlotTouchedBase tbl slotCap eCap + s) :=
          Or.inl ⟨by unfold btSlotTouchedBase; omega, by unfold btSlotTouchedBase bundleTableFixedSize; omega⟩
        exact hnf (h ▸ hf)
    · omega
  let Inv : ℕ → List ℕ → State → Prop := fun t touched st =>
    (∀ r, r ≤ 22 → r ≠ 13 → st.regs r = st₀.regs r) ∧
    st.regs 13 = touched.length ∧ st.regs 23 = t ∧
    PassBMemInv vCap eCap tbl touchedBufPtr S₀ D m cand₀ xs mem₀ t touched st.mem
  let passBBody : Stmt :=
    .assign 24 (.load (.bin .add (.bin .add (.reg 21) (.const 1)) (.reg 23))) ;;
    .assign 25 (.bin .div (.reg 24) (.const 2)) ;;
    .assign 26 (.load (.bin .add (.reg 8) (.reg 25))) ;;
    .cond (.reg 26)
      (.assign 27 (.bin .sub (.reg 26) (.const 1)) ;;
       .assign 28 (.load (.bin .add (.reg 7) (.reg 27))) ;;
       .assign 29 (.load (.reg 28)) ;;
       .assign 30 (.load (.bin .add (.reg 9) (.reg 24))) ;;
       .assign 31 (.bin .add (.bin .add (.bin .add (.reg 28) (.const 3))
         (.bin .mul (.const 3) (.reg 29))) (.reg 30)) ;;
       .assign 32 (.load (.reg 31)) ;;
       .cond (.reg 32)
         (.store (.reg 31) (.const 0) ;;
          .assign 33 (.load (.bin .add (.bin .add (.bin .add (.reg 28) (.const 3))
            (.reg 29)) (.reg 30))) ;;
          .cond (.bin .lt (.reg 32) (.reg 33))
            (.assign 34 (.bin .add (.bin .add (.bin .add (.reg 28) (.const 3))
               (.bin .mul (.const 4) (.reg 29))) (.reg 30)) ;;
             .assign 35 (.load (.reg 34)) ;;
             .cond (.bin .eq (.reg 35) (.const 0))
               (.store (.reg 34) (.const 1) ;;
                .assign 36 (.load (.bin .add (.reg 11) (.reg 27))) ;;
                .store (.bin .add (.bin .add (.bin .add (.reg 28) (.const 3))
                  (.bin .mul (.const 5) (.reg 29))) (.reg 30)) (.reg 36) ;;
                .store (.bin .add (.reg 11) (.reg 27)) (.bin .add (.reg 30) (.const 1)) ;;
                .assign 36 (.load (.bin .add (.reg 10) (.reg 27))) ;;
                .cond (.bin .eq (.reg 36) (.const 0))
                  (.store (.bin .add (.reg 10) (.reg 27)) (.const 1) ;;
                   .store (.bin .add (.reg 5) (.reg 13)) (.reg 27) ;;
                   .assign 13 (.bin .add (.reg 13) (.const 1)))
                  .nop)
               .nop)
            .nop)
         .nop)
      .nop
  have hloop_ex : ∃ st_end c_loop touched_end,
      Runs w pProg ω bundleStepScanPassBStmt st₀ .normal st_end c_loop ∧
      Inv xs.length touched_end st_end ∧
      c_loop ≤ 165 * xs.length + 12 := by
    unfold bundleStepScanPassBStmt
    obtain ⟨st_end, c_loop, touched_end, hrun_loop, hInv_end, hc_loop⟩ :=
      runs_forRange_pot (w := w) (p := pProg) (ω := ω) (r := 23) (lo := .const 0) (hi := .reg 22)
        (body := passBBody) (phi := fun _ _ => 0) (Inv := Inv) (stepCost := fun _ => 154) xs.length
        (by omega) (fun _ => by omega) (st₀ := st₀) (a₀ := touched₀)
      (by
        refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], ?_, rfl⟩
        exact ⟨fun r hr _ => by simp [show r ≠ 23 by omega], by simp [hr13], by simp,
          passBMemInv_init htouch_disj_foot hafter₀_copy htouch₀ hseenA hfrA⟩)
      (fun _ _ _ _ hI => hI.2.2.1)
      (fun _ _ st _ hI => by simp [Expr.eval, hI.1 22 (by decide) (by decide), hr22])
      (fun t touched st ht hI => by
        rcases hI with ⟨hregs, hr13_st, hr23_st, hpm⟩
        have hpm_copy := hpm
        rcases hpm with ⟨hfr, htnd, htlt, htflag, _, _, hslotsT⟩
        set x := xs[t]'ht
        have hx_lt : x.1 < eCap := hxs_lt x (List.getElem_mem ht)
        have hkx_lt : endKey x < 2 * eCap := by rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
        have hkx_w : endKey x < 2 ^ w := by clear * - hkx_lt htbl_w'; omega
        have he_eq : endKey x / 2 = x.1 := by rcases x with ⟨ee, side⟩; cases side <;> simp [endKey]; omega
        have hmem_k : st.mem (listPtr + 1 + t) = endKey x := by
          rw [hfr _ (hnotB_list t ht)]
          have hget := hlist_mem.2 t ht; rw [List.getD_eq_getElem _ _ ht] at hget; exact hget
        set es := mem₀ (btEdgeSlotBase tbl slotCap + x.1)
        have hes_eq : st.mem (btEdgeSlotBase tbl slotCap + x.1) = es :=
          hfr _ (hnotB_fixed_ro _ (by unfold btEdgeSlotBase; omega)
            (by unfold btEdgeSlotBase bundleTableCoreSize; clear * - hx_lt; omega)
            fun s _ => ⟨by unfold btEdgeSlotBase btSlotCandHeadBase; clear * - hx_lt; omega,
              by unfold btEdgeSlotBase btSlotTouchedBase; clear * - hx_lt; omega⟩)
        set st1 : State := { st with regs := Function.update st.regs 24 (endKey x) }
        set st2 : State := { st1 with regs := Function.update st1.regs 25 x.1 }
        set st3 : State := { st2 with regs := Function.update st2.regs 26 es }
        have ha24 : Runs w pProg ω (.assign 24 (.load (.bin .add (.bin .add (.reg 21) (.const 1)) (.reg 23))))
            st .normal st1 7 :=
          runs_assign_iff.mpr ⟨endKey x, by
            simp [Expr.eval, BinOp.eval, hregs 21 (by decide) (by decide), hr21, hr23_st, hmem_k, h1_w,
              show listPtr + 1 < 2 ^ w by omega, show listPtr + 1 + t < 2 ^ w by omega], rfl, rfl, rfl⟩
        have ha25 : Runs w pProg ω (.assign 25 (.bin .div (.reg 24) (.const 2))) st1 .normal st2 4 :=
          runs_assign_iff.mpr ⟨x.1, by
            simp [Expr.eval, BinOp.eval, st1, h2_w, he_eq, show x.1 < 2 ^ w by clear * - hx_lt htbl_w'; omega],
            rfl, rfl, rfl⟩
        have ha26 : Runs w pProg ω (.assign 26 (.load (.bin .add (.reg 8) (.reg 25)))) st2 .normal st3 5 :=
          runs_assign_iff.mpr ⟨es, by
            simp [Expr.eval, BinOp.eval, st2, st1, hregs 8 (by decide) (by decide), hr8, hes_eq,
              show btEdgeSlotBase tbl slotCap + x.1 < 2 ^ w by unfold btEdgeSlotBase; clear * - hx_lt htbl_w'; omega],
            rfl, rfl, rfl⟩
        by_cases hex : ∃ (js : Fin slotCap) (B : BundleState), S js = some B ∧ x.1 ∈ B.edges
        · obtain ⟨js, B, hSjs, hxB⟩ := hex
          have hjs_lt : js.1 < slotCap := js.2
          have hes_val : es = js.1 + 1 := (hedgeSlot x.1 hx_lt).1 js B hSjs hxB
          have hslot_js := hslots js
          have hSjs' : tableDelEdges S₀ D js = some B := hSjs
          simp only [hSjs'] at hslot_js
          cases hm_js : m.slotBlocks js with
          | none => simp only [hm_js] at hslot_js
          | some pb =>
          rcases pb with ⟨p, cap⟩; simp only [hm_js] at hslot_js
          rcases hslot_js with ⟨hptr_js, hrep_js, hp_disj_tbl⟩
          obtain ⟨nB, hV_js, hnB, _, hbo, _, h0, _, _, hdll, _, _, _, _, _, _, _⟩ := hrep_js
          set b := B.bundleOf x
          have hb_lt : b < nB := hbo x ((mem_edgeEnds _ _).mpr hxB)
          have hb_cap : b < cap := lt_of_lt_of_le hb_lt hnB
          have hp_w' : p + (3 + 6 * cap) < 2 ^ w := hblks_w js p cap hm_js
          have hp_disj_tbl' : p + (3 + 6 * cap) ≤ tbl ∨ tbl + (14 + 7 * slotCap + 8 * eCap) ≤ p := hp_disj_tbl
          have hptr_st : st.mem (btSlotPtrBase tbl + js.1) = p :=
            (hfr _ (hnotB_fixed_ro _ (by unfold btSlotPtrBase; omega)
              (by unfold btSlotPtrBase bundleTableCoreSize; clear * - hjs_lt; omega)
              fun s _ => ⟨by unfold btSlotPtrBase btSlotCandHeadBase; clear * - hjs_lt; omega,
                by unfold btSlotPtrBase btSlotTouchedBase; clear * - hjs_lt; omega⟩)).trans hptr_js
          have hcap_st : st.mem p = cap :=
            (hfr p (hnotB_blk_ro js p cap p hm_js (le_refl _) (by omega))).trans (by simpa [bsOffBunCap] using h0)
          have hbun_st : st.mem (btEndBundleBase tbl slotCap eCap + endKey x) = b :=
            (hfr _ (hnotB_fixed_ro _ (by unfold btEndBundleBase; omega)
              (by unfold btEndBundleBase bundleTableCoreSize; clear * - hkx_lt; omega)
              fun s _ => ⟨by unfold btEndBundleBase btSlotCandHeadBase; clear * - hkx_lt; omega,
                by unfold btEndBundleBase btSlotTouchedBase; clear * - hkx_lt; omega⟩)).trans
              (hendBun js B hSjs x ((mem_edgeEnds _ _).mpr hxB))
          have hslotsT_js := hslotsT js
          simp only [hSjs', hm_js] at hslotsT_js
          set seenVal := st.mem (bsSeenBase p cap + b)
          have hseenVal_eq : seenVal = if seenVisited S xs t js b then 0 else seenCount S xs js b :=
            hslotsT_js.1 b hb_cap
          have hjs_w : js.1 < 2 ^ w := by clear * - hjs_lt htbl_w'; omega
          have hptr_w : btSlotPtrBase tbl + js.1 < 2 ^ w := by unfold btSlotPtrBase; clear * - hjs_lt htbl_w'; omega
          have hbun_w : btEndBundleBase tbl slotCap eCap + endKey x < 2 ^ w := by unfold btEndBundleBase; clear * - hkx_lt htbl_w'; omega
          have hp3_w : p + 3 < 2 ^ w := by clear * - hp_w'; omega
          have h3c_w : 3 * cap < 2 ^ w := by clear * - hp_w'; omega
          have hp33c_w : p + 3 + 3 * cap < 2 ^ w := by clear * - hp_w'; omega
          have hseen_w : bsSeenBase p cap + b < 2 ^ w := by unfold bsSeenBase; clear * - hp_w' hb_cap; omega
          set r27 := Function.update st3.regs 27 js.1
          set r28 := Function.update r27 28 p
          set r29 := Function.update r28 29 cap
          set r30 := Function.update r29 30 b
          set r31 := Function.update r30 31 (bsSeenBase p cap + b)
          set r32 := Function.update r31 32 seenVal
          set st32 : State := { st3 with regs := r32 }
          have hpre_cps : ∀ {sTail : Stmt} {stF : State} {cTail : ℕ},
              Runs w pProg ω sTail st32 .normal stF cTail →
              Runs w pProg ω
                (.assign 27 (.bin .sub (.reg 26) (.const 1)) ;;
                 .assign 28 (.load (.bin .add (.reg 7) (.reg 27))) ;;
                 .assign 29 (.load (.reg 28)) ;;
                 .assign 30 (.load (.bin .add (.reg 9) (.reg 24))) ;;
                 .assign 31 (.bin .add (.bin .add (.bin .add (.reg 28) (.const 3))
                   (.bin .mul (.const 3) (.reg 29))) (.reg 30)) ;;
                 .assign 32 (.load (.reg 31)) ;;
                 sTail) st3 .normal stF (36 + cTail) := by
            intro sTail stF cTail hTail
            have h27 : Runs w pProg ω (.assign 27 (.bin .sub (.reg 26) (.const 1))) st3 .normal { st3 with regs := r27 } 4 :=
              runs_assign_iff.mpr ⟨js.1, by simp [Expr.eval, BinOp.eval, st3, hes_val, h1_w, hjs_w], rfl, rfl, rfl⟩
            have h28 : Runs w pProg ω (.assign 28 (.load (.bin .add (.reg 7) (.reg 27))))
                { st3 with regs := r27 } .normal { st3 with regs := r28 } 5 :=
              runs_assign_iff.mpr ⟨p, by
                simp [Expr.eval, BinOp.eval, r27, st3, st2, st1, hregs 7 (by decide) (by decide), hr7, hptr_st, hptr_w], rfl, rfl, rfl⟩
            have h29 : Runs w pProg ω (.assign 29 (.load (.reg 28)))
                { st3 with regs := r28 } .normal { st3 with regs := r29 } 3 :=
              runs_assign_iff.mpr ⟨cap, by simp [Expr.eval, r28, st3, st2, st1, hcap_st], rfl, rfl, rfl⟩
            have h30 : Runs w pProg ω (.assign 30 (.load (.bin .add (.reg 9) (.reg 24))))
                { st3 with regs := r29 } .normal { st3 with regs := r30 } 5 :=
              runs_assign_iff.mpr ⟨b, by
                simp [Expr.eval, BinOp.eval, r29, r28, r27, st3, st2, st1, hregs 9 (by decide) (by decide), hr9, hbun_st, hbun_w],
                rfl, rfl, rfl⟩
            have h31 : Runs w pProg ω (.assign 31 (.bin .add (.bin .add (.bin .add (.reg 28) (.const 3))
                (.bin .mul (.const 3) (.reg 29))) (.reg 30)))
                { st3 with regs := r30 } .normal { st3 with regs := r31 } 10 :=
              runs_assign_iff.mpr ⟨bsSeenBase p cap + b, by
                unfold bsSeenBase
                simp [Expr.eval, BinOp.eval, r30, r29, r28, h3_w, hp3_w, h3c_w, hp33c_w,
                  show p + 3 + 3 * cap + b < 2 ^ w from hseen_w], rfl, rfl, rfl⟩
            have h32 : Runs w pProg ω (.assign 32 (.load (.reg 31)))
                { st3 with regs := r31 } .normal st32 3 :=
              runs_assign_iff.mpr ⟨seenVal, by simp [Expr.eval, r31, st3, st2, st1, seenVal], rfl, rfl, rfl⟩
            exact (show 4 + (5 + (3 + (5 + (10 + (3 + cTail + 1) + 1) + 1) + 1) + 1) + 1 = 36 + cTail by omega) ▸
              bundle_runs_seq_normal h27 (bundle_runs_seq_normal h28 (bundle_runs_seq_normal h29
                (bundle_runs_seq_normal h30 (bundle_runs_seq_normal h31 (bundle_runs_seq_normal h32 hTail)))))
          have hvis_now : seenVisited S xs (t + 1) js b := by
            rw [seenVisited_take_succ_iff ht js b, hSjs]; exact Or.inr ((BundleState.mem_ends B b x).mpr ⟨hxB, rfl⟩)
          have hvis_other : ∀ (j' : Fin slotCap) b', (j' ≠ js ∨ b' ≠ b) →
              (seenVisited S xs (t + 1) j' b' ↔ seenVisited S xs t j' b') := by
            intro j' b' hne
            rw [seenVisited_take_succ_iff ht j' b']
            refine ⟨fun h => h.elim id fun hm => ?_, Or.inl⟩
            cases hSj' : S j' with
            | none => rw [hSj'] at hm; exact False.elim hm
            | some B' =>
              rw [hSj'] at hm
              obtain ⟨hxB', hbb'⟩ := (BundleState.mem_ends B' b' x).mp hm
              rcases hne with hjj | hbb
              · exact False.elim (Finset.disjoint_left.mp (hdisjE j' js hjj B' B hSj' hSjs) hxB' hxB)
              · by_cases hjj : j' = js
                · subst j'; rw [hSjs] at hSj'; cases hSj'; exact False.elim (hbb hbb'.symm)
                · exact False.elim (Finset.disjoint_left.mp (hdisjE j' js hjj B' B hSj' hSjs) hxB' hxB)
          have hr32_regs : ∀ r, r ≤ 23 → st32.regs r = st.regs r := fun r hr => by
            simp [st32, r32, r31, r30, r29, r28, r27, st3, st2, st1,
              show r ≠ 32 by omega, show r ≠ 31 by omega, show r ≠ 30 by omega, show r ≠ 29 by omega,
              show r ≠ 28 by omega, show r ≠ 27 by omega, show r ≠ 26 by omega, show r ≠ 25 by omega,
              show r ≠ 24 by omega]
          by_cases hvis_t : seenVisited S xs t js b
          · have hsv0 : seenVal = 0 := by simp [hseenVal_eq, hvis_t]
            have hcond32 : ∀ sThen, Runs w pProg ω (.cond (.reg 32) sThen .nop) st32 .normal st32 3 := fun _ =>
              runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, st32, r32, hsv0],
                by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
            have hcond26 : ∀ sThen, Runs w pProg ω (.cond (.reg 26)
                (.assign 27 (.bin .sub (.reg 26) (.const 1)) ;;
                 .assign 28 (.load (.bin .add (.reg 7) (.reg 27))) ;;
                 .assign 29 (.load (.reg 28)) ;;
                 .assign 30 (.load (.bin .add (.reg 9) (.reg 24))) ;;
                 .assign 31 (.bin .add (.bin .add (.bin .add (.reg 28) (.const 3))
                   (.bin .mul (.const 3) (.reg 29))) (.reg 30)) ;;
                 .assign 32 (.load (.reg 31)) ;;
                 .cond (.reg 32) sThen .nop) .nop) st3 .normal st32 41 := fun sThen =>
              runs_cond_iff.mpr ⟨js.1 + 1, 39, by simp [Expr.eval, st3, hes_val],
                by simpa [Nat.succ_ne_zero] using hpre_cps (hcond32 sThen), rfl⟩
            have hvis_all : ∀ j' b', seenVisited S xs (t + 1) j' b' ↔ seenVisited S xs t j' b' := fun j' b' => by
              by_cases hjb : j' = js ∧ b' = b
              · rcases hjb with ⟨rfl, rfl⟩; exact ⟨fun _ => hvis_t, fun _ => hvis_now⟩
              · exact hvis_other j' b' (not_and_or.mp hjb)
            have hcand_eq : passBCands S xs (t + 1) cand₀ = passBCands S xs t cand₀ := by
              funext j'; unfold passBCands; cases hSj' : S j' with
              | none => rfl
              | some B' => ext b'; simp [hvis_all]
            refine ⟨st32, 7 + (4 + (5 + 41 + 1) + 1) + 1, touched,
              bundle_runs_seq_normal ha24 (bundle_runs_seq_normal ha25 (bundle_runs_seq_normal ha26 (hcond26 _))),
              by rw [hr32_regs 23 (by decide), hr23_st], ?_, rfl, by omega⟩
            refine ⟨fun r hr hne13 => by
                simp only [Function.update_of_ne (show r ≠ 23 by omega)]
                exact (hr32_regs r (by omega)).trans (hregs r hr hne13),
              by simp [hr32_regs 13 (by decide), hr13_st], by simp, ?_⟩
            rcases hpm_copy with ⟨p1, p2, p3, p4, p5, p6, p7⟩
            refine ⟨p1, p2, p3, p4, p5, fun j' => by rw [hcand_eq]; exact p6 j',
              fun j' => by
                rw [hcand_eq]; have hj' := p7 j'
                cases hSj' : tableDelEdges S₀ D j' with
                | none =>
                  simp only [hSj'] at hj' ⊢
                  cases hm' : m.slotBlocks j' with
                  | none => simp only [hm'] at hj' ⊢; exact hj'
                  | some _ => simp only [hm'] at hj'
                | some B' =>
                  simp only [hSj'] at hj' ⊢
                  cases hm' : m.slotBlocks j' with
                  | none => simp only [hm'] at hj'
                  | some pb' =>
                    rcases pb' with ⟨p', cap'⟩; simp only [hm'] at hj' ⊢
                    exact ⟨fun b' hb' => by
                      have hv := hvis_all j' b'; dsimp only [S] at hv
                      simp only [hv]; exact hj'.1 b' hb', hj'.2⟩⟩
          · have hsv_eq : seenVal = seenCount S xs js b := by simp [hseenVal_eq, hvis_t]
            have hsv_pos : 0 < seenVal := by
              rw [hsv_eq, ← seenVisited_iff_pos]
              unfold seenVisited; rw [hSjs]
              exact ⟨x, by rw [List.take_length]; exact List.getElem_mem ht, (BundleState.mem_ends B b x).mpr ⟨hxB, rfl⟩⟩
            obtain ⟨L, hL_dll, hL_sz, hL_mem⟩ := hdll b hb_lt
            have hcard_eq : L.length = (B.ends b).card := dll_len_eq_card_ends hL_dll hL_mem
            have hsz_st : st.mem (bsSizeBase p cap + b) = (B.ends b).card := by
              rw [hfr _ (hnotB_blk_ro js p cap _ hm_js (by unfold bsSizeBase; omega) (by unfold bsSizeBase; omega))]
              exact hL_sz.trans hcard_eq
            have hsz_w : bsSizeBase p cap + b < 2 ^ w := by unfold bsSizeBase; clear * - hp_w' hb_cap; omega
            have hp3c_w : p + 3 + cap < 2 ^ w := by clear * - hp_w'; omega
            set mem_z := Function.update st.mem (bsSeenBase p cap + b) 0
            set r33 := Function.update r32 33 (B.ends b).card
            set st_z : State := { st32 with mem := mem_z }
            set st33 : State := { st_z with regs := r33 }
            have hne_sz_seen : bsSizeBase p cap + b ≠ bsSeenBase p cap + b := by unfold bsSizeBase bsSeenBase; omega
            have hst_z : Runs w pProg ω (.store (.reg 31) (.const 0)) st32 .normal st_z 3 :=
              runs_store_iff.mpr ⟨bsSeenBase p cap + b, 0, by simp [Expr.eval, st32, r32, r31],
                by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
            have ha33 : Runs w pProg ω (.assign 33 (.load (.bin .add (.bin .add (.bin .add (.reg 28) (.const 3))
                (.reg 29)) (.reg 30)))) st_z .normal st33 9 :=
              runs_assign_iff.mpr ⟨(B.ends b).card, by
                have hmv : mem_z (p + 3 + cap + b) = (B.ends b).card := by
                  simpa [bsSizeBase] using (Function.update_of_ne hne_sz_seen _ _).trans hsz_st
                simp [Expr.eval, BinOp.eval, st_z, st32, r32, r31, r30, r29, r28, h3_w, hp3_w, hp3c_w,
                  show p + 3 + cap + b < 2 ^ w from hsz_w, hmv], rfl, rfl, rfl⟩
            have hzero_done : ∀ (hcand_eq : passBCands S xs (t + 1) cand₀ = passBCands S xs t cand₀)
                {sLtBody : Stmt} {stF : State} {cInner : ℕ}
                (hInner : Runs w pProg ω (.cond (.bin .lt (.reg 32) (.reg 33)) sLtBody .nop) st33 .normal stF cInner)
                (hcI : cInner ≤ 35)
                (hregsF : ∀ r, r ≤ 23 → stF.regs r = st33.regs r) (hmemF : stF.mem = mem_z),
                ∃ st' c touched',
                  Runs w pProg ω
                    (.assign 24 (.load (.bin .add (.bin .add (.reg 21) (.const 1)) (.reg 23))) ;;
                     .assign 25 (.bin .div (.reg 24) (.const 2)) ;;
                     .assign 26 (.load (.bin .add (.reg 8) (.reg 25))) ;;
                     .cond (.reg 26)
                       (.assign 27 (.bin .sub (.reg 26) (.const 1)) ;;
                        .assign 28 (.load (.bin .add (.reg 7) (.reg 27))) ;;
                        .assign 29 (.load (.reg 28)) ;;
                        .assign 30 (.load (.bin .add (.reg 9) (.reg 24))) ;;
                        .assign 31 (.bin .add (.bin .add (.bin .add (.reg 28) (.const 3))
                          (.bin .mul (.const 3) (.reg 29))) (.reg 30)) ;;
                        .assign 32 (.load (.reg 31)) ;;
                        .cond (.reg 32)
                          (.store (.reg 31) (.const 0) ;;
                           .assign 33 (.load (.bin .add (.bin .add (.bin .add (.reg 28) (.const 3))
                             (.reg 29)) (.reg 30))) ;;
                           .cond (.bin .lt (.reg 32) (.reg 33)) sLtBody .nop) .nop) .nop)
                    st .normal st' c ∧ st'.regs 23 = t ∧
                  Inv (t + 1) touched' { st' with regs := Function.update st'.regs 23 (t + 1) } ∧
                  0 ≤ 0 ∧ c ≤ 154 := by
              intro hcand_eq sLtBody stF cInner hInner hcI hregsF hmemF
              have hcond32 : Runs w pProg ω (.cond (.reg 32) _ .nop) st32 .normal stF (16 + cInner) :=
                runs_cond_iff.mpr ⟨seenVal, 3 + (9 + cInner + 1) + 1, by simp [Expr.eval, st32, r32],
                  by simpa [Nat.ne_of_gt hsv_pos] using bundle_runs_seq_normal hst_z (bundle_runs_seq_normal ha33 hInner),
                  by simp only [Expr.size]; omega⟩
              have hcond26 : Runs w pProg ω (.cond (.reg 26) _ .nop) st3 .normal stF (54 + cInner) :=
                runs_cond_iff.mpr ⟨js.1 + 1, 36 + (16 + cInner), by simp [Expr.eval, st3, hes_val],
                  by simpa [Nat.succ_ne_zero] using hpre_cps hcond32, by simp only [Expr.size]; omega⟩
              refine ⟨stF, 7 + (4 + (5 + (54 + cInner) + 1) + 1) + 1, touched,
                bundle_runs_seq_normal ha24 (bundle_runs_seq_normal ha25 (bundle_runs_seq_normal ha26 hcond26)),
                by rw [hregsF 23 (by decide)]; simp only [st33, r33, Function.update_of_ne (show (23 : ℕ) ≠ 33 by decide)]; exact (hr32_regs 23 (by decide)).trans hr23_st,
                ⟨fun r hr hne13 => by
                  simp only [Function.update_of_ne (show r ≠ 23 by omega)]
                  rw [hregsF r (by omega)]; simp only [st33, r33, Function.update_of_ne (show r ≠ 33 by omega)]
                  exact (hr32_regs r (by omega)).trans (hregs r hr hne13),
                 by simp only [Function.update_of_ne (show (13 : ℕ) ≠ 23 by decide)]; rw [hregsF 13 (by decide)]; simp only [st33, r33, Function.update_of_ne (show (13 : ℕ) ≠ 33 by decide)]; exact (hr32_regs 13 (by decide)).trans hr13_st,
                 by simp, hmemF ▸ passBMemInv_zeroSeen htouch_disj_foot hdisjB hp_disj_tbl hm_js hb_cap
                   hvis_now hvis_other hcand_eq hpm_copy⟩,
                le_refl _, by omega⟩
            by_cases hlt : seenVal < (B.ends b).card
            · have h4c_w : 4 * cap < 2 ^ w := by clear * - hp_w'; omega
              have hp34c_w : p + 3 + 4 * cap < 2 ^ w := by clear * - hp_w'; omega
              have hic_w : bsInCandBase p cap + b < 2 ^ w := by unfold bsInCandBase; clear * - hp_w' hb_cap; omega
              have hne_ic_seen : bsInCandBase p cap + b ≠ bsSeenBase p cap + b := by unfold bsInCandBase bsSeenBase; omega
              set icVal := st.mem (bsInCandBase p cap + b)
              have hic_eq : icVal = if b ∈ passBCands S xs t cand₀ js then 1 else 0 := hslotsT_js.2.1 b hb_cap
              set r34 := Function.update r33 34 (bsInCandBase p cap + b)
              set r35 := Function.update r34 35 icVal
              set st35 : State := { st33 with regs := r35 }
              have ha34 : Runs w pProg ω (.assign 34 (.bin .add (.bin .add (.bin .add (.reg 28) (.const 3))
                  (.bin .mul (.const 4) (.reg 29))) (.reg 30))) st33 .normal { st33 with regs := r34 } 10 :=
                runs_assign_iff.mpr ⟨bsInCandBase p cap + b, by
                  unfold bsInCandBase
                  simp [Expr.eval, BinOp.eval, st33, r33, r32, r31, r30, r29, r28, h3_w, h4_w,
                    hp3_w, h4c_w, hp34c_w, show p + 3 + 4 * cap + b < 2 ^ w from hic_w], rfl, rfl, rfl⟩
              have ha35 : Runs w pProg ω (.assign 35 (.load (.reg 34))) { st33 with regs := r34 } .normal st35 3 :=
                runs_assign_iff.mpr ⟨icVal, by
                  simp [Expr.eval, r34, st33, st_z, mem_z, Function.update_of_ne hne_ic_seen, icVal], rfl, rfl, rfl⟩
              by_cases hin_c : b ∈ passBCands S xs t cand₀ js
              · have hic1 : icVal = 1 := by simp [hic_eq, hin_c]
                have hcond35 : ∀ sThen, Runs w pProg ω (.cond (.bin .eq (.reg 35) (.const 0)) sThen .nop) st35 .normal st35 5 := fun _ =>
                  runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, BinOp.eval, st35, r35, hic1],
                    by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
                have hcond_lt : ∀ sThen, Runs w pProg ω (.cond (.bin .lt (.reg 32) (.reg 33))
                    (.assign 34 (.bin .add (.bin .add (.bin .add (.reg 28) (.const 3))
                      (.bin .mul (.const 4) (.reg 29))) (.reg 30)) ;;
                     .assign 35 (.load (.reg 34)) ;;
                     .cond (.bin .eq (.reg 35) (.const 0)) sThen .nop) .nop) st33 .normal st35 24 := fun sThen =>
                  runs_cond_iff.mpr ⟨1, 10 + (3 + 5 + 1) + 1,
                    by simp [Expr.eval, BinOp.eval, st33, r33, r32, hlt, h1_w],
                    by simpa using bundle_runs_seq_normal ha34 (bundle_runs_seq_normal ha35 (hcond35 sThen)), rfl⟩
                have hcand_eq : passBCands S xs (t + 1) cand₀ = passBCands S xs t cand₀ := by
                  funext j'; unfold passBCands; cases hSj' : S j' with
                  | none => rfl
                  | some B' =>
                    ext b'; simp only [Finset.mem_union, Finset.mem_filter]
                    by_cases hjb : j' = js ∧ b' = b
                    · rcases hjb with ⟨hjj, hbb⟩; rw [hjj] at hSj' ⊢; rw [hbb]
                      rw [hSjs] at hSj'; cases hSj'
                      have hmem_c : b ∈ passBCands S xs t cand₀ js := hin_c
                      simp only [passBCands, hSjs, Finset.mem_union, Finset.mem_filter] at hmem_c
                      exact ⟨fun _ => hmem_c, fun h => h.elim Or.inl fun ⟨hbV, _, hlt'⟩ => Or.inr ⟨hbV, hvis_now, hlt'⟩⟩
                    · simp only [hvis_other j' b' (not_and_or.mp hjb)]
                obtain ⟨st', c, touched', h1, h2, h3, _, h5⟩ := hzero_done hcand_eq (hcond_lt _) (by omega)
                  (fun r hr => by simp [st35, r35, r34, show r ≠ 35 by omega, show r ≠ 34 by omega]; rfl) rfl
                exact ⟨st', c, touched', h1, h2, h3, rfl, h5⟩
              · -- New candidate enqueue!
                have hic0 : icVal = 0 := by simp [hic_eq, hin_c]
                have h5c_w : 5 * cap < 2 ^ w := by clear * - hp_w'; omega
                have hp35c_w : p + 3 + 5 * cap < 2 ^ w := by clear * - hp_w'; omega
                have hcn_w : bsCandNextBase p cap + b < 2 ^ w := by unfold bsCandNextBase; clear * - hp_w' hb_cap; omega
                have hch_w : btSlotCandHeadBase tbl slotCap eCap + js.1 < 2 ^ w := by unfold btSlotCandHeadBase; clear * - hjs_lt htbl_w'; omega
                have htf_w : btSlotTouchedBase tbl slotCap eCap + js.1 < 2 ^ w := by unfold btSlotTouchedBase; clear * - hjs_lt htbl_w'; omega
                have hb1_w : b + 1 < 2 ^ w := by clear * - hp_w' hb_cap; omega
                set a_ic := bsInCandBase p cap + b
                set a_cn := bsCandNextBase p cap + b
                set a_ch := btSlotCandHeadBase tbl slotCap eCap + js.1
                set a_tf := btSlotTouchedBase tbl slotCap eCap + js.1
                set oldCH := st.mem a_ch
                set oldTF := st.mem a_tf
                have hne_ch_seen : a_ch ≠ bsSeenBase p cap + b := by unfold a_ch btSlotCandHeadBase bsSeenBase; clear * - hp_disj_tbl' hjs_lt hb_cap; omega
                have hne_ch_ic : a_ch ≠ a_ic := by unfold a_ch a_ic btSlotCandHeadBase bsInCandBase; clear * - hp_disj_tbl' hjs_lt hb_cap; omega
                have hne_tf_seen : a_tf ≠ bsSeenBase p cap + b := by unfold a_tf btSlotTouchedBase bsSeenBase; clear * - hp_disj_tbl' hjs_lt hb_cap; omega
                have hne_tf_ic : a_tf ≠ a_ic := by unfold a_tf a_ic btSlotTouchedBase bsInCandBase; clear * - hp_disj_tbl' hjs_lt hb_cap; omega
                have hne_tf_cn : a_tf ≠ a_cn := by unfold a_tf a_cn btSlotTouchedBase bsCandNextBase; clear * - hp_disj_tbl' hjs_lt hb_cap; omega
                have hne_tf_ch : a_tf ≠ a_ch := by unfold a_tf a_ch btSlotTouchedBase btSlotCandHeadBase; clear * - hjs_lt; omega
                set mem_e1 := Function.update mem_z a_ic 1
                set mem_e2 := Function.update mem_e1 a_cn oldCH
                set mem_e3 := Function.update mem_e2 a_ch (b + 1)
                set r36a := Function.update r35 36 oldCH
                set r36b := Function.update r36a 36 oldTF
                set st_e3 : State := { st35 with mem := mem_e3, regs := r36b }
                have he1 : Runs w pProg ω (.store (.reg 34) (.const 1)) st35 .normal { st35 with mem := mem_e1 } 3 :=
                  runs_store_iff.mpr ⟨a_ic, 1, by simp [Expr.eval, st35, r35, r34, a_ic], by simp [Expr.eval, h1_w], rfl, rfl, rfl⟩
                have he2 : Runs w pProg ω (.assign 36 (.load (.bin .add (.reg 11) (.reg 27))))
                    { st35 with mem := mem_e1 } .normal { st35 with mem := mem_e1, regs := r36a } 5 :=
                  runs_assign_iff.mpr ⟨oldCH, by
                    simp [Expr.eval, BinOp.eval, st35, r35, r34, r33, r32, r31, r30, r29, r28, r27, st3, st2, st1,
                      hregs 11 (by decide) (by decide), hr11, show btSlotCandHeadBase tbl slotCap eCap + js.1 < 2 ^ w from hch_w,
                      mem_e1, mem_z, Function.update_of_ne hne_ch_ic, Function.update_of_ne hne_ch_seen, oldCH, a_ch], rfl, rfl, rfl⟩
                have he3 : Runs w pProg ω (.store (.bin .add (.bin .add (.bin .add (.reg 28) (.const 3))
                    (.bin .mul (.const 5) (.reg 29))) (.reg 30)) (.reg 36))
                    { st35 with mem := mem_e1, regs := r36a } .normal { st35 with mem := mem_e2, regs := r36a } 11 :=
                  runs_store_iff.mpr ⟨a_cn, oldCH, by
                    unfold a_cn bsCandNextBase
                    simp [Expr.eval, BinOp.eval, r36a, r35, r34, r33, r32, r31, r30, r29, r28,
                      h3_w, h5_w, hp3_w, h5c_w, hp35c_w, show p + 3 + 5 * cap + b < 2 ^ w from hcn_w],
                    by simp [Expr.eval, r36a], rfl, rfl, rfl⟩
                have he4 : Runs w pProg ω (.store (.bin .add (.reg 11) (.reg 27)) (.bin .add (.reg 30) (.const 1)))
                    { st35 with mem := mem_e2, regs := r36a } .normal { st35 with mem := mem_e3, regs := r36a } 7 :=
                  runs_store_iff.mpr ⟨a_ch, b + 1,
                    by simp [Expr.eval, BinOp.eval, r36a, r35, r34, r33, r32, r31, r30, r29, r28, r27, st3, st2, st1,
                      hregs 11 (by decide) (by decide), hr11, a_ch, hch_w],
                    by simp [Expr.eval, BinOp.eval, r36a, r35, r34, r33, r32, r31, r30, h1_w, hb1_w], rfl, rfl, rfl⟩
                have he5 : Runs w pProg ω (.assign 36 (.load (.bin .add (.reg 10) (.reg 27))))
                    { st35 with mem := mem_e3, regs := r36a } .normal st_e3 5 :=
                  runs_assign_iff.mpr ⟨oldTF, by
                    simp [Expr.eval, BinOp.eval, r36a, r35, r34, r33, r32, r31, r30, r29, r28, r27, st3, st2, st1,
                      hregs 10 (by decide) (by decide), hr10, show btSlotTouchedBase tbl slotCap eCap + js.1 < 2 ^ w from htf_w,
                      mem_e3, mem_e2, mem_e1, mem_z, Function.update_of_ne hne_tf_ch, Function.update_of_ne hne_tf_cn,
                      Function.update_of_ne hne_tf_ic, Function.update_of_ne hne_tf_seen, oldTF, a_tf], rfl, rfl, rfl⟩
                set touched' := if js.1 ∈ touched then touched else touched ++ [js.1]
                have htf_cond : ∃ stF cTF,
                    Runs w pProg ω (.cond (.bin .eq (.reg 36) (.const 0))
                      (.store (.bin .add (.reg 10) (.reg 27)) (.const 1) ;;
                       .store (.bin .add (.reg 5) (.reg 13)) (.reg 27) ;;
                       .assign 13 (.bin .add (.reg 13) (.const 1))) .nop) st_e3 .normal stF cTF ∧
                    cTF ≤ 20 ∧
                    (∀ r, r ≤ 23 → r ≠ 13 → stF.regs r = st_e3.regs r) ∧
                    stF.regs 13 = touched'.length ∧
                    (js.1 ∈ touched → stF.mem = mem_e3) ∧
                    (js.1 ∉ touched → stF.mem = Function.update (Function.update mem_e3 a_tf 1) (touchedBufPtr + touched.length) js.1) := by
                  have hotf : oldTF = if js.1 ∈ touched then 1 else 0 := htflag js.1 hjs_lt
                  by_cases hmt : js.1 ∈ touched
                  · have hv1 : oldTF = 1 := by simp [hotf, hmt]
                    refine ⟨st_e3, 5, runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, BinOp.eval, st_e3, r36b, hv1],
                      by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩, by omega,
                      fun _ _ _ => rfl,
                      by simp [st_e3, r36b, r36a, r35, r34, r33, r32, r31, r30, r29, r28, r27, st3, st2, st1, hr13_st, touched', hmt],
                      fun _ => rfl, fun h => absurd hmt h⟩
                  · have hv0 : oldTF = 0 := by simp [hotf, hmt]
                    have htlen_lt : touched.length < slotCap := by
                      have hsub : touched.toFinset ⊂ Finset.range slotCap :=
                        Finset.ssubset_iff_subset_ne.mpr
                          ⟨fun y hy => Finset.mem_range.mpr (htlt y (List.mem_toFinset.mp hy)),
                           fun heq => hmt (List.mem_toFinset.mp (heq ▸ Finset.mem_range.mpr hjs_lt))⟩
                      have := Finset.card_lt_card hsub
                      rwa [List.toFinset_card_of_nodup htnd, Finset.card_range] at this
                    have hatb_w : touchedBufPtr + touched.length < 2 ^ w := by clear * - htlen_lt htouch_w; omega
                    have htl1_w : touched.length + 1 < 2 ^ w := by clear * - htlen_lt htbl_w'; omega
                    set mf1 := Function.update mem_e3 a_tf 1
                    set mf2 := Function.update mf1 (touchedBufPtr + touched.length) js.1
                    set rf := Function.update r36b 13 (touched.length + 1)
                    set stF : State := { st_e3 with mem := mf2, regs := rf }
                    have hf1 : Runs w pProg ω (.store (.bin .add (.reg 10) (.reg 27)) (.const 1))
                        st_e3 .normal { st_e3 with mem := mf1 } 5 :=
                      runs_store_iff.mpr ⟨a_tf, 1, by
                        simp [Expr.eval, BinOp.eval, st_e3, r36b, r36a, r35, r34, r33, r32, r31, r30, r29, r28, r27,
                          st3, st2, st1, hregs 10 (by decide) (by decide), hr10, a_tf, htf_w],
                        by simp [Expr.eval, h1_w], rfl, rfl, rfl⟩
                    have hf2 : Runs w pProg ω (.store (.bin .add (.reg 5) (.reg 13)) (.reg 27))
                        { st_e3 with mem := mf1 } .normal { st_e3 with mem := mf2 } 5 :=
                      runs_store_iff.mpr ⟨touchedBufPtr + touched.length, js.1, by
                        simp [Expr.eval, BinOp.eval, st_e3, r36b, r36a, r35, r34, r33, r32, r31, r30, r29, r28, r27,
                          st3, st2, st1, hregs 5 (by decide) (by decide), hr5, hr13_st, hatb_w],
                        by simp [Expr.eval, st_e3, r36b, r36a, r35, r34, r33, r32, r31, r30, r29, r28, r27], rfl, rfl, rfl⟩
                    have hf3 : Runs w pProg ω (.assign 13 (.bin .add (.reg 13) (.const 1)))
                        { st_e3 with mem := mf2 } .normal stF 4 :=
                      runs_assign_iff.mpr ⟨touched.length + 1, by
                        simp [Expr.eval, BinOp.eval, st_e3, r36b, r36a, r35, r34, r33, r32, r31, r30, r29, r28, r27,
                          st3, st2, st1, hr13_st, h1_w, htl1_w], rfl, rfl, rfl⟩
                    refine ⟨stF, 20, runs_cond_iff.mpr ⟨1, 16, by simp [Expr.eval, BinOp.eval, st_e3, r36b, hv0, h1_w],
                      by simpa using bundle_runs_seq_normal hf1 (bundle_runs_seq_normal hf2 hf3), rfl⟩,
                      by omega, fun r hr hne13 => by simp [stF, rf, st_e3, hne13],
                      by simp [stF, rf, touched', hmt], fun h => absurd h hmt, fun _ => rfl⟩
                obtain ⟨stF, cTF, hrun_tf, hcTF, hregsF, hr13F, hmf_in, hmf_out⟩ := htf_cond
                have henq_body := bundle_runs_seq_normal he1 (bundle_runs_seq_normal he2
                  (bundle_runs_seq_normal he3 (bundle_runs_seq_normal he4 (bundle_runs_seq_normal he5 hrun_tf))))
                have hcond35 : Runs w pProg ω (.cond (.bin .eq (.reg 35) (.const 0)) _ .nop) st35 .normal stF (40 + cTF) :=
                  runs_cond_iff.mpr ⟨1, 3 + (5 + (11 + (7 + (5 + cTF + 1) + 1) + 1) + 1) + 1,
                    by simp [Expr.eval, BinOp.eval, st35, r35, hic0, h1_w],
                    by simpa using henq_body, by simp only [Expr.size]; omega⟩
                have hcond_lt : Runs w pProg ω (.cond (.bin .lt (.reg 32) (.reg 33)) _ .nop) st33 .normal stF (59 + cTF) :=
                  runs_cond_iff.mpr ⟨1, 10 + (3 + (40 + cTF) + 1) + 1,
                    by simp [Expr.eval, BinOp.eval, st33, r33, r32, hlt, h1_w],
                    by simpa using bundle_runs_seq_normal ha34 (bundle_runs_seq_normal ha35 hcond35),
                    by simp only [Expr.size]; omega⟩
                have hcond32 : Runs w pProg ω (.cond (.reg 32) _ .nop) st32 .normal stF (75 + cTF) :=
                  runs_cond_iff.mpr ⟨seenVal, 3 + (9 + (59 + cTF) + 1) + 1, by simp [Expr.eval, st32, r32],
                    by simpa [Nat.ne_of_gt hsv_pos] using bundle_runs_seq_normal hst_z (bundle_runs_seq_normal ha33 hcond_lt),
                    by simp only [Expr.size]; omega⟩
                have hcond26 : Runs w pProg ω (.cond (.reg 26) _ .nop) st3 .normal stF (113 + cTF) :=
                  runs_cond_iff.mpr ⟨js.1 + 1, 36 + (75 + cTF), by simp [Expr.eval, st3, hes_val],
                    by simpa [Nat.succ_ne_zero] using hpre_cps hcond32, by simp only [Expr.size]; omega⟩
                have hcand_step : ∀ j', passBCands S xs (t + 1) cand₀ j' =
                    if j' = js then insert b (passBCands S xs t cand₀ js) else passBCands S xs t cand₀ j' := by
                  intro j'; split_ifs with hjj
                  · subst j'; ext b'
                    simp only [passBCands, hSjs, Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
                    by_cases hbb : b' = b
                    · subst b'
                      have hbv : b ∈ B.vertices := hV_js ▸ Finset.mem_range.mpr hb_lt
                      have hlt' : seenCount S xs js b < (B.ends b).card := hsv_eq ▸ hlt
                      exact ⟨fun _ => Or.inl rfl, fun _ => Or.inr ⟨hbv, hvis_now, hlt'⟩⟩
                    · simp only [hbb, false_or, hvis_other js b' (Or.inr hbb)]
                  · unfold passBCands; cases hSj' : S j' with
                    | none => rfl
                    | some B' => ext b'; simp [hvis_other j' b' (Or.inl hjj)]
                have hr_e3 : ∀ r, r ≤ 23 → r ≠ 13 → stF.regs r = st.regs r := fun r hr hne13 => by
                  rw [hregsF r hr hne13]
                  simp [st_e3, r36b, r36a, r35, r34, r33, show r ≠ 36 by omega, show r ≠ 35 by omega,
                    show r ≠ 34 by omega, show r ≠ 33 by omega]
                  exact hr32_regs r hr
                refine ⟨stF, 7 + (4 + (5 + (113 + cTF) + 1) + 1) + 1, touched',
                  bundle_runs_seq_normal ha24 (bundle_runs_seq_normal ha25 (bundle_runs_seq_normal ha26 hcond26)),
                  (hr_e3 23 (by decide) (by decide)).trans hr23_st,
                  ⟨fun r hr hne13 => by
                    simp only [Function.update_of_ne (show r ≠ 23 by omega)]
                    exact (hr_e3 r (by omega) hne13).trans (hregs r hr hne13),
                   by simp [hr13F], by simp,
                   passBMemInv_enq htouch_disj_foot hdisjB hblks_disj_tbl hSjs hm_js hb_cap hin_c
                     hvis_now hvis_other hcand_step hpm_copy ⟨hmf_in, hmf_out⟩⟩,
                  rfl, by omega⟩
            · -- seenVal >= (B.ends b).card: cond_lt takes nop
              have hcond_lt : ∀ sThen, Runs w pProg ω (.cond (.bin .lt (.reg 32) (.reg 33)) sThen .nop) st33 .normal st33 5 := fun _ =>
                runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, BinOp.eval, st33, r33, r32, hlt],
                  by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
              have hcand_eq : passBCands S xs (t + 1) cand₀ = passBCands S xs t cand₀ := by
                funext j'; unfold passBCands; cases hSj' : S j' with
                | none => rfl
                | some B' =>
                  ext b'
                  by_cases hjb : j' = js ∧ b' = b
                  · rcases hjb with ⟨hjj, hbb⟩; rw [hjj] at hSj' ⊢; rw [hbb]; rw [hSjs] at hSj'; cases hSj'
                    have hge : ¬ seenCount S xs js b < (B.ends b).card := hsv_eq ▸ hlt
                    simp [hge]
                  · simp [hvis_other j' b' (not_and_or.mp hjb)]
              obtain ⟨st', c, touched', h1, h2, h3, _, h5⟩ := hzero_done hcand_eq (hcond_lt _) (by omega)
                (fun _ _ => rfl) rfl
              exact ⟨st', c, touched', h1, h2, h3, rfl, h5⟩
        · push Not at hex
          have hes_val : es = 0 := (hedgeSlot x.1 hx_lt).2 hex
          have hcond26 : ∀ sThen, Runs w pProg ω (.cond (.reg 26) sThen .nop) st3 .normal st3 3 := fun _ =>
            runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, st3, hes_val],
              by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
          have hvis_all : ∀ j' b', seenVisited S xs (t + 1) j' b' ↔ seenVisited S xs t j' b' := by
            intro j' b'; rw [seenVisited_take_succ_iff ht j' b']
            cases hSj' : S j' with
            | none => simp
            | some B' =>
              have hnot : xs[t] ∉ B'.ends b' := fun h => hex j' B' hSj' ((BundleState.mem_ends B' b' xs[t]).mp h).1
              simp [hnot]
          have hcand_eq : passBCands S xs (t + 1) cand₀ = passBCands S xs t cand₀ := by
            funext j'; unfold passBCands; cases hSj' : S j' with
            | none => rfl
            | some B' => ext b'; simp [hvis_all]
          refine ⟨st3, 7 + (4 + (5 + 3 + 1) + 1) + 1, touched,
            bundle_runs_seq_normal ha24 (bundle_runs_seq_normal ha25 (bundle_runs_seq_normal ha26 (hcond26 _))),
            by simp [st3, st2, st1, hr23_st],
            ⟨fun r hr hne13 => by
                simp [st3, st2, st1, show r ≠ 26 by omega, show r ≠ 25 by omega, show r ≠ 24 by omega,
                  show r ≠ 23 by omega, hregs r hr hne13],
             by simp [st3, st2, st1, hr13_st], by simp, ?_⟩, rfl, by omega⟩
          rcases hpm_copy with ⟨p1, p2, p3, p4, p5, p6, p7⟩
          refine ⟨p1, p2, p3, p4, p5, fun j' => by rw [hcand_eq]; exact p6 j',
            fun j' => by
              rw [hcand_eq]; have hj' := p7 j'
              cases hSj' : tableDelEdges S₀ D j' with
              | none =>
                simp only [hSj'] at hj' ⊢
                cases hm' : m.slotBlocks j' with
                | none => simp only [hm'] at hj' ⊢; exact hj'
                | some _ => simp only [hm'] at hj'
              | some B' =>
                simp only [hSj'] at hj' ⊢
                cases hm' : m.slotBlocks j' with
                | none => simp only [hm'] at hj'
                | some pb' =>
                  rcases pb' with ⟨p', cap'⟩; simp only [hm'] at hj' ⊢
                  exact ⟨fun b' hb' => by
                    have hv := hvis_all j' b'; dsimp only [S] at hv
                    simp only [hv]; exact hj'.1 b' hb', hj'.2⟩⟩)
    refine ⟨st_end, c_loop, touched_end, hrun_loop, hInv_end, ?_⟩
    have hrc : rangeCost (fun _ => 154) 0 xs.length = 154 * xs.length := by
      rw [rangeCost_zero_eq_range]; simp [Nat.mul_comm]
    rw [hrc] at hc_loop; simp only [Expr.size_const, Expr.size_reg] at hc_loop; omega
  obtain ⟨st_end, c_loop, touched_end, hrun_loop, hInv_end, hc_loop⟩ := hloop_ex
  rcases hInv_end with ⟨hregs_e, hr13_e, _, hpm_e⟩
  obtain ⟨hafter_e, htouch_e, hfr_e⟩ := passBMemInv_to_afterScan htouch_disj_foot hafter₀_copy hpm_e
  exact ⟨touched_end, st_end, c_loop, hrun_loop, hregs_e, hr13_e, hafter_e, htouch_e, hfr_e, hc_loop⟩

end

end MinCostFlow.SparseCore.Program
