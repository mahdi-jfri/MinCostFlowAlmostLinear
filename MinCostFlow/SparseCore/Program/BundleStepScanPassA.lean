module

public import MinCostFlow.SparseCore.Program.BundleStepScanProcs

/-!
# Verification of Pass A in Phase 2 (`BundleStepScanPassA`)

Proves `bundleStepScanPassA_runs` (counting ends per active bundle in `seen[b]`) and defines
the Pass B address predicates and `passBCands`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Number of ends in `xs` belonging to bundle `b` of slot `j` in table `S`. -/
def seenCount {slotCap : ℕ} (S : BundleTableState slotCap) (xs : List End)
    (j : Fin slotCap) (b : ℕ) : ℕ :=
  match S j with
  | none => 0
  | some B => (xs.filter fun x => decide (x ∈ B.ends b)).length

/-- Predicate that some end in `xs.take t` belongs to bundle `b` of slot `j` in table `S`. -/
def seenVisited {slotCap : ℕ} (S : BundleTableState slotCap) (xs : List End)
    (t : ℕ) (j : Fin slotCap) (b : ℕ) : Prop :=
  match S j with
  | none => False
  | some B => ∃ x ∈ xs.take t, x ∈ B.ends b

/-- Address belongs to the `seen` array of some active slot block in `m`. -/
def isSeenAddr {slotCap : ℕ} (m : BundleTableMeta slotCap) (a : ℕ) : Prop :=
  ∃ (j : Fin slotCap) (p cap b : ℕ), m.slotBlocks j = some (p, cap) ∧ b < cap ∧
    a = bsSeenBase p cap + b

/-- Address belongs to the mutable candidate/seen/touched region of Phase 2 Pass B. -/
def isPassBAddr {slotCap : ℕ} (eCap tbl touchedBufPtr : ℕ) (m : BundleTableMeta slotCap) (a : ℕ) : Prop :=
  (∃ (j : Fin slotCap) (p cap b : ℕ), m.slotBlocks j = some (p, cap) ∧ b < cap ∧
    (a = bsSeenBase p cap + b ∨ a = bsInCandBase p cap + b ∨ a = bsCandNextBase p cap + b)) ∨
  (∃ s < slotCap, a = btSlotCandHeadBase tbl slotCap eCap + s ∨
    a = btSlotTouchedBase tbl slotCap eCap + s) ∨
  (touchedBufPtr ≤ a ∧ a < touchedBufPtr + slotCap)

end

public section

lemma seenCount_nil {slotCap : ℕ} (S : BundleTableState slotCap) (j : Fin slotCap) (b : ℕ) :
    seenCount S [] j b = 0 := by
  unfold seenCount; cases S j <;> rfl

lemma seenCount_take_succ {slotCap : ℕ} (S : BundleTableState slotCap) (xs : List End)
    {t : ℕ} (ht : t < xs.length) (j : Fin slotCap) (b : ℕ) :
    seenCount S (xs.take (t + 1)) j b =
      seenCount S (xs.take t) j b +
        match S j with
        | none => 0
        | some B => if xs[t] ∈ B.ends b then 1 else 0 := by
  unfold seenCount
  cases S j with
  | none => rfl
  | some B =>
    dsimp only
    rw [List.take_succ_eq_append_getElem ht, List.filter_append, List.length_append,
      List.filter_cons, List.filter_nil]
    by_cases h : xs[t] ∈ B.ends b <;> simp [h]

lemma seenCount_le_card_ends {slotCap : ℕ} {S : BundleTableState slotCap} {xs : List End}
    (hnd : xs.Nodup) {j : Fin slotCap} {B : BundleState} (hSj : S j = some B) (b : ℕ) :
    seenCount S xs j b ≤ (B.ends b).card := by
  simp only [seenCount, hSj]
  have hnd_f : (xs.filter fun x => decide (x ∈ B.ends b)).Nodup := hnd.filter _
  have hsub : (xs.filter fun x => decide (x ∈ B.ends b)).toFinset ⊆ B.ends b := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hx
    exact hx.2
  have hcard := Finset.card_le_card hsub
  rwa [List.toFinset_card_of_nodup hnd_f] at hcard

lemma seenCount_eq_card_filter {slotCap : ℕ} {S : BundleTableState slotCap} {xs : List End}
    (hnd : xs.Nodup) {j : Fin slotCap} {B : BundleState} (hSj : S j = some B) (b : ℕ) :
    seenCount S xs j b = ((B.ends b).filter fun x => x ∈ xs).card := by
  simp only [seenCount, hSj]
  have hnd_f : (xs.filter fun x => decide (x ∈ B.ends b)).Nodup := hnd.filter _
  rw [← List.toFinset_card_of_nodup hnd_f]
  congr 1; ext x
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_filter, decide_eq_true_eq]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩

lemma seenCount_eq_zero_of_not_visited {slotCap : ℕ} {S : BundleTableState slotCap} {xs : List End}
    {j : Fin slotCap} {b : ℕ} (hnot : ¬ seenVisited S xs xs.length j b) :
    seenCount S xs j b = 0 := by
  unfold seenCount seenVisited at *
  cases hSj : S j with
  | none => rfl
  | some B =>
    rw [hSj] at hnot
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro x hx; simp only [decide_eq_true_eq]
    exact fun hmem => hnot ⟨x, by rwa [List.take_length], hmem⟩

lemma seenVisited_iff_pos {slotCap : ℕ} {S : BundleTableState slotCap} {xs : List End}
    {j : Fin slotCap} {b : ℕ} :
    seenVisited S xs xs.length j b ↔ 0 < seenCount S xs j b := by
  unfold seenVisited seenCount
  cases S j with
  | none => simp
  | some B =>
    rw [List.take_length, List.length_pos_iff_exists_mem]
    constructor
    · rintro ⟨x, hx, hxb⟩; exact ⟨x, List.mem_filter.mpr ⟨hx, decide_eq_true hxb⟩⟩
    · rintro ⟨x, hx⟩; obtain ⟨h1, h2⟩ := List.mem_filter.mp hx; exact ⟨x, h1, of_decide_eq_true h2⟩

/-! ## 1. Pass A verification (`bundleStepScanPassA_runs`) -/

/-- Verifies `bundleStepScanPassAStmt`: counts active ends of `xs` (stored as `EndListAt` at
`listPtr`) into `bsSeenBase p cap + b`, leaving all other memory cells unchanged. -/
lemma bundleStepScanPassA_runs {w slotCap vCap eCap tbl listPtr : ℕ}
    {pProg : Program} {S₀ : BundleTableState slotCap} {D : Finset ℕ}
    {m : BundleTableMeta slotCap} {candSet : Fin slotCap → Finset ℕ} {touched : List ℕ}
    {xs : List End} {st₀ : State} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (htbl_w : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w)
    (hblks_w : ∀ j : Fin slotCap, ∀ p c, m.slotBlocks j = some (p, c) →
      p + bundleSlotBlockSize c < 2 ^ w)
    (hlist_w : listPtr + 1 + xs.length < 2 ^ w)
    (hlist_disj_foot : ∀ a, listPtr ≤ a → a < listPtr + 1 + xs.length → ¬ bundleTableFoot eCap tbl m a)
    (hlist_mem : EndListAt st₀.mem listPtr xs)
    (hxs_lt : ∀ x ∈ xs, x.1 < eCap) (_hxs_nd : xs.Nodup)
    (hafter : BundleTableAfterScan slotCap vCap eCap tbl S₀ D m candSet touched st₀.mem)
    (hr7 : st₀.regs 7 = btSlotPtrBase tbl)
    (hr8 : st₀.regs 8 = btEdgeSlotBase tbl slotCap)
    (hr9 : st₀.regs 9 = btEndBundleBase tbl slotCap eCap)
    (hr21 : st₀.regs 21 = listPtr) (hr22 : st₀.regs 22 = xs.length) :
    let S := tableDelEdges S₀ D
    ∃ st' c,
      Runs w pProg ω bundleStepScanPassAStmt st₀ .normal st' c ∧
      (∀ r, r ≤ 22 → st'.regs r = st₀.regs r) ∧
      (∀ j : Fin slotCap, ∀ B p cap, S j = some B → m.slotBlocks j = some (p, cap) →
        ∀ b < cap, st'.mem (bsSeenBase p cap + b) = seenCount S xs j b) ∧
      (∀ a, ¬ isSeenAddr m a → st'.mem a = st₀.mem a) ∧
      c ≤ 70 * xs.length + 12 := by
  intro S
  have htbl_w' : tbl + (14 + 7 * slotCap + 8 * eCap) < 2 ^ w := htbl_w
  have h1_w : 1 < 2 ^ w := by clear * - hw16; omega
  have h2_w : 2 < 2 ^ w := by clear * - hw16; omega
  have h3_w : 3 < 2 ^ w := by clear * - hw16; omega
  rcases hafter with ⟨_, _, _, _, _, _, _, _, _, _, _, _,
    hdisjE, hedgeSlot, hendBun, hslots, hdisjB, _, _, _, _, _⟩
  have hnot_seen_fixed : ∀ a, tbl ≤ a → a < tbl + bundleTableFixedSize slotCap eCap → ¬ isSeenAddr m a := by
    rintro a ha1 ha2 ⟨j, p, cap, b, hm, hb, rfl⟩
    have hj := hslots j
    cases hSj : tableDelEdges S₀ D j with
    | none => simp only [hSj, hm] at hj
    | some B =>
      simp only [hSj, hm] at hj
      have hdj : p + (3 + 6 * cap) ≤ tbl ∨ tbl + (14 + 7 * slotCap + 8 * eCap) ≤ p := hj.2.2
      unfold bsSeenBase at ha1 ha2; unfold bundleTableFixedSize at ha2
      clear * - ha1 ha2 hdj hb; omega
  let Inv : ℕ → Unit → State → Prop := fun t _ st =>
    (∀ r, r ≤ 22 → st.regs r = st₀.regs r) ∧ st.regs 23 = t ∧
    (∀ j : Fin slotCap, ∀ B p cap, S j = some B → m.slotBlocks j = some (p, cap) →
      ∀ b < cap, st.mem (bsSeenBase p cap + b) = seenCount S (xs.take t) j b) ∧
    (∀ a, ¬ isSeenAddr m a → st.mem a = st₀.mem a)
  obtain ⟨st_end, c_loop, _, hrun_loop, hInv_end, hc_loop⟩ :=
    runs_forRange_pot (w := w) (p := pProg) (ω := ω) (r := 23) (lo := .const 0) (hi := .reg 22)
      (phi := fun _ _ => 0) (Inv := Inv) (stepCost := fun _ => 60) xs.length
      (by omega) (fun _ => by omega) (st₀ := st₀) (a₀ := ())
      (by
        refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], ?_, rfl⟩
        refine ⟨fun r hr => by simp [show r ≠ 23 by omega], by simp, ?_, fun _ _ => rfl⟩
        intro j B p cap hSj hm b hb
        have hj := hslots j
        dsimp only [S] at hSj
        simp only [hSj, hm] at hj
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hseen, _, _, _, _⟩ := hj.2.1
        rw [List.take_zero, seenCount_nil]; exact hseen b hb)
      (fun _ _ _ _ hI => hI.2.1)
      (fun _ _ st _ hI => by simp [Expr.eval, hI.1 22 (by decide), hr22])
      (fun t _ st ht hI => by
        rcases hI with ⟨hregs, hr23, hseen, hfr⟩
        set x := xs[t]'ht
        have hx_lt : x.1 < eCap := hxs_lt x (List.getElem_mem ht)
        have hkx_lt : endKey x < 2 * eCap := by rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
        have hkx_w : endKey x < 2 ^ w := by clear * - hkx_lt htbl_w'; omega
        have he_eq : endKey x / 2 = x.1 := by rcases x with ⟨ee, side⟩; cases side <;> simp [endKey]; omega
        have hmem_k : st.mem (listPtr + 1 + t) = endKey x := by
          rw [hfr (listPtr + 1 + t) (fun ⟨j, p, cap, b, hm, hb, heq⟩ => by
            have hfoot : bundleTableFoot eCap tbl m (bsSeenBase p cap + b) :=
              Or.inr ⟨j, p, cap, hm, by unfold bsSeenBase; omega,
                by unfold bsSeenBase bundleSlotBlockSize; omega⟩
            exact hlist_disj_foot _ (by omega) (by omega) (heq ▸ hfoot))]
          have hget := hlist_mem.2 t ht
          rw [List.getD_eq_getElem _ _ ht] at hget
          exact hget
        set es := st₀.mem (btEdgeSlotBase tbl slotCap + x.1)
        have hes_eq : st.mem (btEdgeSlotBase tbl slotCap + x.1) = es :=
          hfr _ (hnot_seen_fixed _ (by unfold btEdgeSlotBase; omega)
            (by unfold btEdgeSlotBase bundleTableFixedSize; clear * - hx_lt; omega))
        set st1 : State := { st with regs := Function.update st.regs 24 (endKey x) }
        set st2 : State := { st1 with regs := Function.update st1.regs 25 x.1 }
        set st3 : State := { st2 with regs := Function.update st2.regs 26 es }
        have ha24 : Runs w pProg ω (.assign 24 (.load (.bin .add (.bin .add (.reg 21) (.const 1)) (.reg 23))))
            st .normal st1 7 :=
          runs_assign_iff.mpr ⟨endKey x, by
            simp [Expr.eval, BinOp.eval, hregs 21 (by decide), hr21, hr23, hmem_k, h1_w,
              show listPtr + 1 < 2 ^ w by omega, show listPtr + 1 + t < 2 ^ w by omega], rfl, rfl, rfl⟩
        have ha25 : Runs w pProg ω (.assign 25 (.bin .div (.reg 24) (.const 2))) st1 .normal st2 4 :=
          runs_assign_iff.mpr ⟨x.1, by
            simp [Expr.eval, BinOp.eval, st1, h2_w, he_eq, show x.1 < 2 ^ w by clear * - hx_lt htbl_w'; omega],
            rfl, rfl, rfl⟩
        have ha26 : Runs w pProg ω (.assign 26 (.load (.bin .add (.reg 8) (.reg 25)))) st2 .normal st3 5 :=
          runs_assign_iff.mpr ⟨es, by
            simp [Expr.eval, BinOp.eval, st2, st1, hregs 8 (by decide), hr8, hes_eq,
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
          rcases hslot_js with ⟨hptr_js, hrep_js, _⟩
          obtain ⟨nB, _, hnB, _, hbo, _, h0, _, _, _, _, _, _, _, _, _, _⟩ := hrep_js
          set b := B.bundleOf x
          have hb_lt : b < nB := hbo x ((mem_edgeEnds _ _).mpr hxB)
          have hb_cap : b < cap := lt_of_lt_of_le hb_lt hnB
          have hp_w' : p + (3 + 6 * cap) < 2 ^ w := hblks_w js p cap hm_js
          have hptr_st : st.mem (btSlotPtrBase tbl + js.1) = p :=
            (hfr _ (hnot_seen_fixed _ (by unfold btSlotPtrBase; omega)
              (by unfold btSlotPtrBase bundleTableFixedSize; clear * - hjs_lt; omega))).trans hptr_js
          have hcap_st : st.mem p = cap := by
            have hns : ¬ isSeenAddr m p := by
              rintro ⟨j', p', cap', b', hm', hb', heq⟩
              by_cases hjj : j' = js
              · subst hjj; rw [hm_js] at hm'; cases hm'; unfold bsSeenBase at heq; omega
              · have hdj := hdisjB j' js hjj p' cap' p cap hm' hm_js
                unfold bundleSlotBlockSize at hdj; unfold bsSeenBase at heq; clear * - hdj hb' heq; omega
            exact (hfr p hns).trans (by simpa [bsOffBunCap] using h0)
          have hbun_st : st.mem (btEndBundleBase tbl slotCap eCap + endKey x) = b :=
            (hfr _ (hnot_seen_fixed _ (by unfold btEndBundleBase; omega)
              (by unfold btEndBundleBase bundleTableFixedSize; clear * - hkx_lt; omega))).trans
              (hendBun js B hSjs x ((mem_edgeEnds _ _).mpr hxB))
          set oldS := seenCount S (xs.take t) js b
          have holdS_eq : st.mem (bsSeenBase p cap + b) = oldS := hseen js B p cap hSjs hm_js b hb_cap
          have holdS1_w : oldS + 1 < 2 ^ w := by
            have hle : oldS ≤ t := by
              simp only [oldS, seenCount, hSjs]
              exact le_trans (List.length_filter_le _ _) (by simp [List.length_take])
            clear * - hle ht hlist_w; omega
          set r27 := Function.update st3.regs 27 js.1
          set r28 := Function.update r27 28 p
          set r29 := Function.update r28 29 cap
          set r30 := Function.update r29 30 b
          set r31 := Function.update r30 31 (bsSeenBase p cap + b)
          set st_f : State := { st3 with mem := Function.update st.mem (bsSeenBase p cap + b) (oldS + 1), regs := r31 }
          have hjs_w : js.1 < 2 ^ w := by clear * - hjs_lt htbl_w'; omega
          have hptr_w : btSlotPtrBase tbl + js.1 < 2 ^ w := by unfold btSlotPtrBase; clear * - hjs_lt htbl_w'; omega
          have hbun_w : btEndBundleBase tbl slotCap eCap + endKey x < 2 ^ w := by unfold btEndBundleBase; clear * - hkx_lt htbl_w'; omega
          have hp3_w : p + 3 < 2 ^ w := by clear * - hp_w'; omega
          have h3c_w : 3 * cap < 2 ^ w := by clear * - hp_w'; omega
          have hp33c_w : p + 3 + 3 * cap < 2 ^ w := by clear * - hp_w'; omega
          have hseen_w : bsSeenBase p cap + b < 2 ^ w := by unfold bsSeenBase; clear * - hp_w' hb_cap; omega
          have h27 : Runs w pProg ω (.assign 27 (.bin .sub (.reg 26) (.const 1))) st3 .normal { st3 with regs := r27 } 4 :=
            runs_assign_iff.mpr ⟨js.1, by simp [Expr.eval, BinOp.eval, st3, hes_val, h1_w, hjs_w], rfl, rfl, rfl⟩
          have h28 : Runs w pProg ω (.assign 28 (.load (.bin .add (.reg 7) (.reg 27))))
              { st3 with regs := r27 } .normal { st3 with regs := r28 } 5 :=
            runs_assign_iff.mpr ⟨p, by
              simp [Expr.eval, BinOp.eval, r27, st3, st2, st1, hregs 7 (by decide), hr7, hptr_st, hptr_w], rfl, rfl, rfl⟩
          have h29 : Runs w pProg ω (.assign 29 (.load (.reg 28)))
              { st3 with regs := r28 } .normal { st3 with regs := r29 } 3 :=
            runs_assign_iff.mpr ⟨cap, by simp [Expr.eval, r28, st3, st2, st1, hcap_st], rfl, rfl, rfl⟩
          have h30 : Runs w pProg ω (.assign 30 (.load (.bin .add (.reg 9) (.reg 24))))
              { st3 with regs := r29 } .normal { st3 with regs := r30 } 5 :=
            runs_assign_iff.mpr ⟨b, by
              simp [Expr.eval, BinOp.eval, r29, r28, r27, st3, st2, st1, hregs 9 (by decide), hr9, hbun_st, hbun_w],
              rfl, rfl, rfl⟩
          have h31 : Runs w pProg ω (.assign 31 (.bin .add (.bin .add (.bin .add (.reg 28) (.const 3))
              (.bin .mul (.const 3) (.reg 29))) (.reg 30)))
              { st3 with regs := r30 } .normal { st3 with regs := r31 } 10 :=
            runs_assign_iff.mpr ⟨bsSeenBase p cap + b, by
              unfold bsSeenBase
              simp [Expr.eval, BinOp.eval, r30, r29, r28, h3_w, hp3_w, h3c_w, hp33c_w,
                show p + 3 + 3 * cap + b < 2 ^ w from hseen_w], rfl, rfl, rfl⟩
          have hst_wr : Runs w pProg ω (.store (.reg 31) (.bin .add (.load (.reg 31)) (.const 1)))
              { st3 with regs := r31 } .normal st_f 6 :=
            runs_store_iff.mpr ⟨bsSeenBase p cap + b, oldS + 1, by simp [Expr.eval, r31],
              by simp [Expr.eval, BinOp.eval, r31, st3, st2, st1, holdS_eq, h1_w, holdS1_w], rfl, rfl, rfl⟩
          have hbody_t := bundle_runs_seq_normal h27 (bundle_runs_seq_normal h28
            (bundle_runs_seq_normal h29 (bundle_runs_seq_normal h30 (bundle_runs_seq_normal h31 hst_wr))))
          have hcond : Runs w pProg ω (.cond (.reg 26) _ .nop) st3 .normal st_f 40 :=
            runs_cond_iff.mpr ⟨js.1 + 1, 38, by simp [Expr.eval, st3, hes_val],
              by simpa [Nat.succ_ne_zero] using hbody_t, rfl⟩
          refine ⟨st_f, 7 + (4 + (5 + 40 + 1) + 1) + 1, (),
            bundle_runs_seq_normal ha24 (bundle_runs_seq_normal ha25 (bundle_runs_seq_normal ha26 hcond)),
            by simp [st_f, r31, r30, r29, r28, r27, st3, st2, st1, hr23], ?_, rfl, by omega⟩
          refine ⟨fun r hr => by
              simp [st_f, r31, r30, r29, r28, r27, st3, st2, st1,
                show r ≠ 31 by omega, show r ≠ 30 by omega, show r ≠ 29 by omega,
                show r ≠ 28 by omega, show r ≠ 27 by omega, show r ≠ 26 by omega,
                show r ≠ 25 by omega, show r ≠ 24 by omega, show r ≠ 23 by omega, hregs r hr],
            by simp, ?_, ?_⟩
          · intro j' B' p' cap' hSj' hm' b' hb'
            rw [seenCount_take_succ S xs ht j' b', hSj']
            by_cases hjj : j' = js
            · subst hjj; rw [hSjs] at hSj'; cases hSj'; rw [hm_js] at hm'; cases hm'
              by_cases hbb : b' = b
              · subst hbb
                have hx_in : x ∈ B.ends b := (BundleState.mem_ends B b x).mpr ⟨hxB, rfl⟩
                simp [st_f, show xs[t] = x from rfl, hx_in, oldS]
              · have hx_out : x ∉ B.ends b' := fun h => hbb (((BundleState.mem_ends B b' x).mp h).2.symm)
                simp only [st_f, show xs[t] = x from rfl, hx_out, ↓reduceIte, add_zero]
                rw [Function.update_of_ne (by unfold bsSeenBase; omega)]
                exact hseen j' B p cap hSjs hm_js b' hb'
            · have hdj_e := hdisjE j' js hjj B' B hSj' hSjs
              have hx_out : x ∉ B'.ends b' := fun h =>
                Finset.disjoint_left.mp hdj_e ((BundleState.mem_ends B' b' x).mp h).1 hxB
              have hdj_p := hdisjB j' js hjj p' cap' p cap hm' hm_js
              have hne_a : bsSeenBase p' cap' + b' ≠ bsSeenBase p cap + b := by
                unfold bsSeenBase; unfold bundleSlotBlockSize at hdj_p
                clear * - hdj_p hb' hb_cap; omega
              simp only [st_f, show xs[t] = x from rfl, hx_out, ↓reduceIte, add_zero]
              rw [Function.update_of_ne hne_a]
              exact hseen j' B' p' cap' hSj' hm' b' hb'
          · intro a hns
            have hne_a : a ≠ bsSeenBase p cap + b := fun h => hns ⟨js, p, cap, b, hm_js, hb_cap, h⟩
            simp only [st_f, Function.update_of_ne hne_a]
            exact hfr a hns
        · push Not at hex
          have hes_val : es = 0 := (hedgeSlot x.1 hx_lt).2 hex
          have hcond : ∀ sThen, Runs w pProg ω (.cond (.reg 26) sThen .nop) st3 .normal st3 3 := fun _ =>
            runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, st3, hes_val],
              by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
          refine ⟨st3, 7 + (4 + (5 + 3 + 1) + 1) + 1, (),
            bundle_runs_seq_normal ha24 (bundle_runs_seq_normal ha25 (bundle_runs_seq_normal ha26 (hcond _))),
            by simp [st3, st2, st1, hr23], ?_, rfl, by omega⟩
          refine ⟨fun r hr => by
              simp [st3, st2, st1, show r ≠ 26 by omega, show r ≠ 25 by omega, show r ≠ 24 by omega,
                show r ≠ 23 by omega, hregs r hr],
            by simp, fun j' B' p' cap' hSj' hm' b' hb' => ?_, hfr⟩
          rw [seenCount_take_succ S xs ht j' b', hSj']
          have hx_out : x ∉ B'.ends b' := fun h => hex j' B' hSj' ((BundleState.mem_ends B' b' x).mp h).1
          simp only [show xs[t] = x from rfl, hx_out, ↓reduceIte, add_zero]
          exact hseen j' B' p' cap' hSj' hm' b' hb')
  rcases hInv_end with ⟨hregs, _, hseen_end, hfr_end⟩
  refine ⟨st_end, c_loop, hrun_loop, hregs, ?_, hfr_end, ?_⟩
  · intro j B p cap hSj hm b hb
    simpa [List.take_length] using hseen_end j B p cap hSj hm b hb
  · have hrc : rangeCost (fun _ => 60) 0 xs.length = 60 * xs.length := by
      rw [rangeCost_zero_eq_range]; simp [Nat.mul_comm]
    rw [hrc] at hc_loop; simp only [Expr.size_const, Expr.size_reg] at hc_loop; omega

/-! ## 2. Pass B verification (`bundleStepScanPassB_runs`) -/

section
open Classical

/-- Bundles newly detected as splitting by scanning `xs` up to prefix `t`. -/
@[expose] noncomputable def passBCands {slotCap : ℕ} (S : BundleTableState slotCap) (xs : List End)
    (t : ℕ) (cand₀ : Fin slotCap → Finset ℕ) (j : Fin slotCap) : Finset ℕ :=
  match S j with
  | none => cand₀ j
  | some B =>
    cand₀ j ∪ B.vertices.filter fun b =>
      seenVisited S xs t j b ∧ seenCount S xs j b < (B.ends b).card

end


end

end MinCostFlow.SparseCore.Program
