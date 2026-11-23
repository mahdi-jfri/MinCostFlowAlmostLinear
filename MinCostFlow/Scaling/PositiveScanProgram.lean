module

public import MinCostFlow.Scaling.PositiveLayout
public import MinCostFlow.Scaling.WordFiveStoreProgram
import WordRAM.Tactic
import WordRAM.Memory
import WordRAM.Entry

/-!
# Compacting positive-capacity records and their original indices

The reductions of Lemma C.1 of Chen et al., arXiv:2203.00671v2, delete zero
capacity slots before calling the scaling solver. This procedure scans the
original records in order. It copies a record and its original index only
when the capacity is positive. Records and indices occupy two disjoint
reserved arrays. The output count and both compacted prefixes agree with
the model's stable filter, in at most `300*edgeCount+20` steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[source,edgeCount,firstIndex,records,indices]`. -/
def positiveScanBody (self writer : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.cond (.bin .eq (.load (.bin .add (.reg 0) (.const 2))) (.const 0))
      (.call 6 self [.bin .add (.reg 0) (.const 5), .bin .sub (.reg 1) (.const 1),
        .bin .add (.reg 2) (.const 1), .reg 3, .reg 4] ;; .ret (.reg 6))
      (.call 5 writer [.load (.reg 0), .load (.bin .add (.reg 0) (.const 1)),
        .load (.bin .add (.reg 0) (.const 2)), .load (.bin .add (.reg 0) (.const 3)),
        .load (.bin .add (.reg 0) (.const 4)), .reg 3] ;;
      .store (.reg 4) (.reg 2) ;;
      .call 6 self [.bin .add (.reg 0) (.const 5), .bin .sub (.reg 1) (.const 1),
        .bin .add (.reg 2) (.const 1), .reg 5, .bin .add (.reg 4) (.const 1)] ;;
      .ret (.bin .add (.reg 6) (.const 1))))

/-- Stable positive-capacity compaction and the direct record writer. -/
def positiveScanModule (b : ℕ) : List Stmt := [positiveScanBody b (b + 1), wordFiveBody]

/-- The input indices are consecutive. The output arrays reserve room for
all source slots, and only their compacted positive prefixes are specified. -/
def positiveScanContract (w : ℕ) (J : Circulation) (es : List (Fin J.m)) (index : ℕ) : Contract where
  pre args mem := ∃ a records indices, args = [a, es.length, index, records, indices] ∧
    ListAt mem a (es.flatMap J.solverEdgeWords) ∧ a + 5 * es.length ≤ records ∧
    records + 5 * es.length ≤ indices ∧ indices + es.length < 2 ^ w ∧
    index + es.length < 2 ^ w ∧
    (∀ i (hi : i < es.length), (es[i]'hi).val = index + i) ∧
    (∀ e ∈ es, ∀ x ∈ J.solverEdgeWords e, x < 2 ^ w) ∧ 8 < 2 ^ w
  post args mem out mem' :=
    out = (es.filter fun e => 0 < J.capacity e).length ∧
    ListAt mem' (args.getD 3 0) ((es.filter fun e => 0 < J.capacity e).flatMap J.solverEdgeWords) ∧
    ListAt mem' (args.getD 4 0) ((es.filter fun e => 0 < J.capacity e).map Fin.val) ∧
    ∀ x, (x < args.getD 3 0 ∨ args.getD 3 0 + 5 * es.length ≤ x) →
      (x < args.getD 4 0 ∨ args.getD 4 0 + es.length ≤ x) → mem' x = mem x
  cost _ _ := 300 * es.length + 20

/-- Stable compaction uses no random instructions. -/
theorem positiveScanModule_noRand (b : ℕ) :
    ∀ body ∈ positiveScanModule b, body.NoRand := by
  simp only [positiveScanModule, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨by simp only [positiveScanBody, Stmt.NoRand, and_self], wordFiveBody_noRand⟩

/-- The scan writes exactly the positive-capacity records and their original
indices, preserving every cell outside the two reserved output arrays. -/
theorem positiveScan_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (positiveScanModule b)) (J : Circulation)
    (es : List (Fin J.m)) (index : ℕ) :
    MeetsContract w p b (positiveScanContract w J es index) := by
  have hwriter : p.HasAt (b + 1) wordFiveModule := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [positiveScanModule, wordFiveModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [positiveScanModule])
  have hkW := wordFiveStore_meetsContract (w := w) hwriter
  induction es generalizing index with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a, records, indices, rfl, _, _, _, _, _, _, _, hw⟩ := hpre
    have hone : 1 < 2 ^ w := by omega
    apply runs_start_le
    unfold positiveScanBody
    wram_step
    · refine runs_ret_le (by eval_expr) ?_ ?_
      · exact ⟨rfl, listAt_nil _ _, listAt_nil _ _, fun _ _ _ => rfl⟩
      · simp only [positiveScanContract, List.length_nil, Expr.size_bin, Expr.size_reg, Expr.size_const]
        omega
    · simp at hcond
  | cons e es ih =>
    have hkR := ih (index + 1)
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a, records, indices, rfl, hat, hend, hsep, hindicesend, hindexend, hseq, hinput, hw⟩ := hpre
    obtain ⟨hhead, htail⟩ := listAt_append.mp hat
    change ListAt mem a (J.solverEdgeWords e) at hhead
    change ListAt mem (a + 5) (es.flatMap J.solverEdgeWords) at htail
    have hfields : ∀ j : Fin 5, mem (a + j.val) = (J.solverEdgeWords e).getD j.val 0 := by
      intro j
      rw [List.getD_eq_getElem _ _ (by change j.val < 5; exact j.isLt)]
      exact hhead _ (by change j.val < 5; exact j.isLt)
    have ht := hfields ⟨0, by decide⟩
    have hh := hfields ⟨1, by decide⟩
    have hc := hfields ⟨2, by decide⟩
    have hcs := hfields ⟨3, by decide⟩
    have hcm := hfields ⟨4, by decide⟩
    simp only [Circulation.solverEdgeWords, List.getD_cons_succ,
      List.getD_cons_zero, Nat.add_zero] at ht hh hc hcs hcm
    have hheadIndex : e.val = index := by
      have hh := hseq 0 (by simp)
      change e.val = index + 0 at hh
      simpa only [Nat.add_zero] using hh
    have hseqTail : ∀ i (hi : i < es.length), (es[i]'hi).val = index + 1 + i := by
      intro i hi
      have hh := hseq (i + 1) (by simp only [List.length_cons]; omega)
      change (es[i]'hi).val = index + (i + 1) at hh
      omega
    have htword : (J.tail e : ℕ) < 2 ^ w := hinput e (List.mem_cons_self) _ (by simp [Circulation.solverEdgeWords])
    have hhword : (J.head e : ℕ) < 2 ^ w := hinput e (List.mem_cons_self) _ (by simp [Circulation.solverEdgeWords])
    have hcword : J.capacity e < 2 ^ w := hinput e (List.mem_cons_self) _ (by simp [Circulation.solverEdgeWords])
    have hcsword : (if J.cost e < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
    have hcmword : (J.cost e).natAbs < 2 ^ w := hinput e (List.mem_cons_self) _ (by simp [Circulation.solverEdgeWords])
    have hrecordBefore : records + 5 ≤ indices := by simp only [List.length_cons, Nat.mul_succ] at hsep; omega
    have hrecords5 : records + 5 < 2 ^ w := by omega
    have hrword : records < 2 ^ w := by omega
    have hiword : indices < 2 ^ w := by omega
    have hi1word : indices + 1 < 2 ^ w := by simp only [List.length_cons] at hindicesend; omega
    have hindexword : index < 2 ^ w := by omega
    have hindex1word : index + 1 < 2 ^ w := by simp only [List.length_cons] at hindexend; omega
    have ha5 : a + 5 < 2 ^ w := by simp only [List.length_cons, Nat.mul_succ] at hend; omega
    have ha : a < 2 ^ w := by omega
    have ha1 : a + 1 < 2 ^ w := by omega
    have ha2 : a + 2 < 2 ^ w := by omega
    have ha3 : a + 3 < 2 ^ w := by omega
    have ha4 : a + 4 < 2 ^ w := by omega
    have hlen : (e :: es).length < 2 ^ w := hwords _ (List.mem_cons_of_mem _ (List.mem_cons_self))
    have htailLen : es.length < 2 ^ w := lt_trans (Nat.lt_succ_self _) hlen
    have hone : 1 < 2 ^ w := by omega
    apply runs_start_le
    unfold positiveScanBody
    wram_step
    · simp at hcond
    · have hlength : (e :: es).length = es.length + 1 := rfl
      wram_step
      · have hz : J.capacity e = 0 := by simpa [startState, hc] using hcond
        have hfilter : (e :: es).filter (fun e => 0 < J.capacity e) = es.filter (fun e => 0 < J.capacity e) := by simp [hz]
        refine runs_seq_call_le hkR (vs := [a + 5, es.length, index + 1, records, indices]) ?_ ?_ ?_ ?_
        · rw [← show (e :: es).length - 1 = es.length from rfl]; eval_expr
        · wram_words
        · exact ⟨a + 5, records, indices, rfl, htail, by omega, by omega, by omega, by omega,
            hseqTail, (fun e' he' => hinput e' (List.mem_cons_of_mem e he')), hw⟩
        · intro count memR posR hpostR
          obtain ⟨hcount, hrecords, hindices, hframe⟩ := hpostR
          change count = (es.filter fun e => 0 < J.capacity e).length at hcount
          change ListAt memR records ((es.filter fun e => 0 < J.capacity e).flatMap J.solverEdgeWords) at hrecords
          change ListAt memR indices ((es.filter fun e => 0 < J.capacity e).map Fin.val) at hindices
          change (∀ x, (x < records ∨ records + 5 * es.length ≤ x) →
            (x < indices ∨ indices + es.length ≤ x) → memR x = mem x) at hframe
          have hcountword : count < 2 ^ w := lt_of_le_of_lt
            (hcount ▸ List.length_filter_le _ _) htailLen
          refine runs_ret_le (v := count) (by eval_expr) ?_ ?_
          · change count = _ ∧ ListAt memR records _ ∧ ListAt memR indices _ ∧
              ∀ x, (x < records ∨ records + 5 * (e :: es).length ≤ x) →
                (x < indices ∨ indices + (e :: es).length ≤ x) → memR x = mem x
            rw [hfilter]
            refine ⟨hcount, hrecords, hindices, ?_⟩
            intro x hr hi
            exact hframe x (by rcases hr with h | h <;> omega) (by rcases hi with h | h <;> omega)
          · simp only [positiveScanContract, List.length_cons, argsSize_cons, argsSize_nil,
              Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
            omega
      · have hpos : 0 < J.capacity e := by
          have hnz : J.capacity e ≠ 0 := by simpa [startState, hc] using hcond
          exact Nat.pos_of_ne_zero hnz
        have hfilter : (e :: es).filter (fun e => 0 < J.capacity e) = e :: es.filter (fun e => 0 < J.capacity e) := by simp [hpos]
        refine runs_seq_call_le hkW
          (vs := [(J.tail e : ℕ), J.head e, J.capacity e, if J.cost e < 0 then 1 else 0, (J.cost e).natAbs, records])
          (by eval_expr) ?_ ⟨_, _, _, _, _, records, rfl, hrecords5⟩ ?_
        · wram_words
        · intro nextRecords memW posW hpostW
          obtain ⟨hptr, hrecordW, hframeW⟩ := hpostW
          change nextRecords = records + 5 at hptr
          change ListAt memW records (J.solverEdgeWords e) at hrecordW
          change (∀ x, x < records ∨ records + 5 ≤ x → memW x = mem x) at hframeW
          have hnextword : nextRecords < 2 ^ w := by omega
          refine runs_seq_store_le (by eval_expr) (v := index) (by eval_expr) ?_
          let memS := Function.update memW indices index
          have hframeS : ∀ x < records, memS x = mem x := by
            intro x hx
            change Function.update memW indices index x = mem x
            rw [Function.update_of_ne (by omega : x ≠ indices)]
            exact hframeW x (Or.inl hx)
          have htailS : ListAt memS (a + 5) (es.flatMap J.solverEdgeWords) :=
            htail.of_agree_below (h₀ := records)
              (by rw [J.solverEdgeRecords_length]; omega) hframeS
          have hrecordS : ListAt memS records (J.solverEdgeWords e) :=
            hrecordW.update_ge (by change records + 5 ≤ indices; exact hrecordBefore)
          have hindexS : memS indices = e.val := by
            change Function.update memW indices index indices = e.val
            rw [Function.update_self, hheadIndex]
          have hchildEnd : nextRecords + 5 * es.length ≤ indices := by omega
          refine runs_seq_call_le hkR
            (vs := [a + 5, es.length, index + 1, nextRecords, indices + 1]) ?_ ?_ ?_ ?_
          · rw [← show (e :: es).length - 1 = es.length from rfl]; eval_expr
          · wram_words
          · exact ⟨a + 5, nextRecords, indices + 1, rfl, htailS, by omega, by omega,
              by omega, by omega, hseqTail, (fun e' he' => hinput e' (List.mem_cons_of_mem e he')), hw⟩
          · intro count memR posR hpostR
            obtain ⟨hcount, hrecords, hindices, hframeR⟩ := hpostR
            change count = (es.filter fun e => 0 < J.capacity e).length at hcount
            change ListAt memR nextRecords ((es.filter fun e => 0 < J.capacity e).flatMap J.solverEdgeWords) at hrecords
            change ListAt memR (indices + 1) ((es.filter fun e => 0 < J.capacity e).map Fin.val) at hindices
            change (∀ x, (x < nextRecords ∨ nextRecords + 5 * es.length ≤ x) →
              (x < indices + 1 ∨ indices + 1 + es.length ≤ x) → memR x = memS x) at hframeR
            have hcountle : count ≤ es.length := hcount ▸ List.length_filter_le _ _
            have hcount1word : count + 1 < 2 ^ w := by omega
            have hcountword : count < 2 ^ w := by omega
            have hrecordR : ListAt memR records (J.solverEdgeWords e) := by
              apply hrecordS.of_agree_below (h₀ := nextRecords) (by change records + 5 ≤ nextRecords; omega)
              intro x hx
              exact hframeR x (Or.inl hx) (Or.inl (by omega))
            have hindexR : memR indices = e.val :=
              (hframeR indices (Or.inr hchildEnd) (Or.inl (by omega))).trans hindexS
            refine runs_ret_le (v := count + 1) (by eval_expr) ?_ ?_
            · change count + 1 = _ ∧ ListAt memR records _ ∧ ListAt memR indices _ ∧
                ∀ x, (x < records ∨ records + 5 * (e :: es).length ≤ x) →
                  (x < indices ∨ indices + (e :: es).length ≤ x) → memR x = mem x
              rw [hfilter]
              refine ⟨by simp only [List.length_cons]; omega, ?_, ?_, ?_⟩
              · apply listAt_append.mpr
                refine ⟨hrecordR, ?_⟩
                simpa only [Circulation.solverEdgeWords, List.length_cons, List.length_nil,
                  Nat.reduceAdd, hptr, List.flatMap] using hrecords
              · exact listAt_cons.mpr ⟨hindexR, hindices⟩
              · intro x hr hi
                rw [hframeR x (by rcases hr with h | h <;> omega)
                  (by rcases hi with h | h <;> omega)]
                change Function.update memW indices index x = mem x
                rw [Function.update_of_ne (by rcases hi with h | h <;> omega)]
                exact hframeW x (by rcases hr with h | h <;> omega)
            · simp only [positiveScanContract, wordFiveStoreContract, List.length_cons,
                argsSize_cons, argsSize_nil, Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
              omega

/-- The scan's consecutive-index, array-separation, and word premises all
hold together on a concrete full circulation input at multiplier two. -/
theorem positiveScan_pre_canonical (J : Circulation) :
    (∀ x ∈ [2, J.m, 0, J.solverWords.length + 2, J.solverWords.length + 2 + 5 * J.m],
      x < 2 ^ wordSize 2 J.solverWords) ∧
      (positiveScanContract (wordSize 2 J.solverWords) J (List.finRange J.m) 0).pre
        [2, J.m, 0, J.solverWords.length + 2, J.solverWords.length + 2 + 5 * J.m]
        (initMem J.solverWords) := by
  let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
  have hlen := J.solverWords_length
  have hbase : 4 + 5 * J.m ≤ B := by dsimp only [B]; omega
  have hbase4 : 4 ≤ B := by omega
  have hproduct : 4 * (4 + 5 * J.m) ≤ B ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hbase4 hbase
  have hp := pow_lt_two_pow_wordSize (by decide : 1 ≤ 2) J.solverWords
  change B ^ 2 < 2 ^ wordSize 2 J.solverWords at hp
  have hlarge : J.solverWords.length + 2 + 6 * J.m < 2 ^ wordSize 2 J.solverWords := by omega
  have hw : 8 < 2 ^ wordSize 2 J.solverWords := by omega
  have hedge : ListAt (initMem J.solverWords) 2
      ((List.finRange J.m).flatMap J.solverEdgeWords) :=
    (listAt_cons.mp (listAt_cons.mp (listAt_initMem J.solverWords)).2).2
  refine ⟨?_, 2, J.solverWords.length + 2, J.solverWords.length + 2 + 5 * J.m,
    ?_, hedge, ?_, ?_, ?_, ?_, ?_, ?_, hw⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega
  · simp only [List.length_finRange]
  · simp only [List.length_finRange]
    omega
  · simp only [List.length_finRange]
    exact le_rfl
  · simp only [List.length_finRange]
    omega
  · simp only [List.length_finRange]
    omega
  · intro i hi
    simp only [List.getElem_finRange, Nat.zero_add]
    rfl
  · intro e _ x hx
    exact lt_two_pow_wordSize_of_mem (by decide) (J.solverEdgeWord_mem e hx)

/-- Stable compaction occupies two procedure slots. -/
theorem positiveScanModule_length (b : ℕ) : (positiveScanModule b).length = 2 := rfl

end MinCostFlow.Scaling.Machine
