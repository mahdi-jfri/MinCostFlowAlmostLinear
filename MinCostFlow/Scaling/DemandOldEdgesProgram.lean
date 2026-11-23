module

public import MinCostFlow.Scaling.DemandArcsLayout
public import MinCostFlow.Scaling.WordFiveProgram
import WordRAM.Tactic
import WordRAM.Memory
import WordRAM.Entry

/-!
# Writing the old-edge block of the feasibility circulation

The demand-instance reduction in Lemma C.1 of Chen et al.,
arXiv:2203.00671v2, keeps capacities and endpoints of the original edges
and sets their costs to zero. This procedure copies those three words and
writes a canonical zero cost for every edge. It takes linear time and
writes exactly the old-edge block in the model's common solver layout.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[firstEdge,edgeCount,heap]`. -/
def demandOldEdgesBody (self writer : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.reg 2))
    (.call 3 writer [.load (.reg 0), .load (.bin .add (.reg 0) (.const 1)),
      .load (.bin .add (.reg 0) (.const 2)), .const 0, .const 0, .reg 2] ;;
    .call 4 self [.bin .add (.reg 0) (.const 5),
      .bin .sub (.reg 1) (.const 1), .reg 3] ;;
    .ret (.reg 4))

/-- Old-edge copying and the shared five-word writer. -/
def demandOldEdgesModule (b : ℕ) : List Stmt :=
  [demandOldEdgesBody b (b + 1), wordFiveBody]

/-- The source rows precede the fresh output and contain fitting words. -/
def demandOldEdgesContract (w : ℕ) (J : Circulation) (es : List (Fin J.m)) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a heap, args = [a, es.length, heap] ∧
      ListAt mem a (es.flatMap J.solverEdgeWords) ∧ a + 5 * es.length ≤ heap ∧
      (∀ e ∈ es, ∀ x ∈ J.solverEdgeWords e, x < 2 ^ w) ∧ 8 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args) (es.flatMap (demandOldEdgeWords J)))
    (fun _ _ => 200 * es.length + 20) (fun _ _ => 5 * es.length)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 5 * es.length }

/-- The old-edge scan and writer use no random instructions. -/
theorem demandOldEdgesModule_noRand (b : ℕ) :
    ∀ body ∈ demandOldEdgesModule b, body.NoRand := by
  simp only [demandOldEdgesModule, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨by simp only [demandOldEdgesBody, Stmt.NoRand, and_self], wordFiveBody_noRand⟩

/-- Old edges receive precisely zero costs, with exact fresh allocation,
preserved input, and cost at most `200*edgeCount+20`. -/
theorem demandOldEdges_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (demandOldEdgesModule b)) (J : Circulation) (es : List (Fin J.m)) :
    MeetsContract w p b (demandOldEdgesContract w J es) := by
  have hwriter : p.HasAt (b + 1) wordFiveModule := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [demandOldEdgesModule, wordFiveModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [demandOldEdgesModule])
  have hkW := wordFive_meetsContract (w := w) hwriter
  induction es with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a, heap, rfl, _, _, _, hw⟩, hzero, hspace⟩ := hpre
    change ZeroFrom mem heap at hzero
    change heap + 0 < 2 ^ w at hspace
    have hh : heap < 2 ^ w := by omega
    have hone : 1 < 2 ^ w := by omega
    apply runs_start_le
    unfold demandOldEdgesBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change (heap ≤ heap ∧ heap ≤ heap + 0 ∧ (∀ x < heap, mem x = mem x) ∧
          ZeroFrom mem heap ∧ ListAt mem heap []) ∧ heap = heap + 0
        exact ⟨⟨le_rfl, by omega, fun _ _ => rfl, hzero, listAt_nil _ _⟩, by omega⟩
      · simp only [demandOldEdgesContract, heapContract, List.length_nil,
          Expr.size_bin, Expr.size_reg, Expr.size_const]
        omega
    · simp at hcond
  | cons e es ih =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a, heap, rfl, hat, hend, hinput, hw⟩, hzero, hspace⟩ := hpre
    change ZeroFrom mem heap at hzero
    change heap + 5 * (e :: es).length < 2 ^ w at hspace
    obtain ⟨hhead, htail⟩ := listAt_append.mp hat
    change ListAt mem a (J.solverEdgeWords e) at hhead
    change ListAt mem (a + 5) (es.flatMap J.solverEdgeWords) at htail
    have ht : mem a = J.tail e := by
      simpa only [Circulation.solverEdgeWords, List.getElem_cons_zero, Nat.add_zero]
        using hhead 0 (by change 0 < 5; decide)
    have hh : mem (a + 1) = J.head e := by
      simpa only [Circulation.solverEdgeWords, List.getElem_cons_succ, List.getElem_cons_zero]
        using hhead 1 (by change 1 < 5; decide)
    have hc : mem (a + 2) = J.capacity e := by
      simpa only [Circulation.solverEdgeWords, List.getElem_cons_succ, List.getElem_cons_zero]
        using hhead 2 (by change 2 < 5; decide)
    have htword : (J.tail e : ℕ) < 2 ^ w := hinput e (List.mem_cons_self) _ (by simp [Circulation.solverEdgeWords])
    have hhword : (J.head e : ℕ) < 2 ^ w := hinput e (List.mem_cons_self) _ (by simp [Circulation.solverEdgeWords])
    have hcword : J.capacity e < 2 ^ w := hinput e (List.mem_cons_self) _ (by simp [Circulation.solverEdgeWords])
    have hheap5 : heap + 5 < 2 ^ w := by simp only [List.length_cons, Nat.mul_succ] at hspace; omega
    have hheap : heap < 2 ^ w := by omega
    have ha5 : a + 5 < 2 ^ w := by simp only [List.length_cons, Nat.mul_succ] at hend; omega
    have ha : a < 2 ^ w := by omega
    have ha1 : a + 1 < 2 ^ w := by omega
    have ha2 : a + 2 < 2 ^ w := by omega
    have hlen : (e :: es).length < 2 ^ w := hwords _ (List.mem_cons_of_mem _ (List.mem_cons_self))
    have hone : 1 < 2 ^ w := by omega
    apply runs_start_le
    unfold demandOldEdgesBody
    wram_step
    · simp at hcond
    · refine runs_seq_call_le hkW
        (vs := [(J.tail e : ℕ), J.head e, J.capacity e, 0, 0, heap]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨⟨_, _, _, _, _, heap, rfl⟩, hzero, hheap5⟩
      · intro nextHeap memW posW hpostW
        obtain ⟨⟨_, _, hframeW, hzeroW, hrecord⟩, hptr⟩ := hpostW
        change nextHeap = heap + 5 at hptr
        change (∀ x < heap, memW x = mem x) at hframeW
        change ZeroFrom memW nextHeap at hzeroW
        change ListAt memW heap (demandOldEdgeWords J e) at hrecord
        have htailW : ListAt memW (a + 5) (es.flatMap J.solverEdgeWords) := by
          intro i hi
          have hlength := J.solverEdgeRecords_length es
          exact (hframeW _ (by simp only [List.length_cons, Nat.mul_succ] at hend; omega)).trans (htail i hi)
        have hnextword : nextHeap < 2 ^ w := by omega
        have htailLen : es.length < 2 ^ w := lt_trans (Nat.lt_succ_self _) hlen
        refine runs_seq_call_le ih (vs := [a + 5, es.length, nextHeap]) ?_ ?_ ?_ ?_
        · have heq : (e :: es).length - 1 = es.length := rfl
          rw [← heq]; eval_expr
        · wram_words
        · refine ⟨⟨a + 5, nextHeap, rfl, htailW, ?_,
            (fun e' he' => hinput e' (List.mem_cons_of_mem e he')), hw⟩, hzeroW, ?_⟩
          · simp only [List.length_cons, Nat.mul_succ] at hend
            omega
          · change nextHeap + 5 * es.length < 2 ^ w
            simp only [List.length_cons, Nat.mul_succ] at hspace
            omega
        · intro out memR posR hpostR
          obtain ⟨⟨_, _, hframeR, hzeroR, hrecords⟩, hout⟩ := hpostR
          change (∀ x < nextHeap, memR x = memW x) at hframeR
          change ZeroFrom memR out at hzeroR
          change ListAt memR nextHeap (es.flatMap (demandOldEdgeWords J)) at hrecords
          change out = nextHeap + 5 * es.length at hout
          have houtword : out < 2 ^ w := by simp only [List.length_cons, Nat.mul_succ] at hspace; omega
          refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
          · change (heap ≤ out ∧ out ≤ heap + 5 * (e :: es).length ∧
              (∀ x < heap, memR x = mem x) ∧ ZeroFrom memR out ∧
              ListAt memR heap ((e :: es).flatMap (demandOldEdgeWords J))) ∧
              out = heap + 5 * (e :: es).length
            refine ⟨⟨by omega, by simp only [List.length_cons, Nat.mul_succ]; omega,
              ?_, hzeroR, ?_⟩, by simp only [List.length_cons, Nat.mul_succ]; omega⟩
            · intro x hx
              exact (hframeR x (by omega)).trans (hframeW x hx)
            · apply listAt_append.mpr
              refine ⟨hrecord.of_agree_below (h₀ := nextHeap) (by change heap + 5 ≤ nextHeap; omega) hframeR, ?_⟩
              simpa only [demandOldEdgeWords, List.length_cons, List.length_nil, Nat.reduceAdd, hptr,
                List.flatMap] using hrecords
          · simp only [demandOldEdgesContract, heapContract, wordFiveContract, List.length_cons,
              argsSize_cons, argsSize_nil, Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
            omega

/-- Every selected edge list can satisfy all record, word, and fresh-heap
premises together on its canonical input memory. -/
theorem exists_demandOldEdges_pre (J : Circulation) (es : List (Fin J.m)) :
    ∃ w, (∀ x ∈ [0, es.length, 5 * es.length], x < 2 ^ w) ∧
      (demandOldEdgesContract w J es).pre [0, es.length, 5 * es.length]
        (initMem (es.flatMap J.solverEdgeWords)) := by
  let input := es.flatMap J.solverEdgeWords ++ [10 * es.length + 10]
  let w := wordSize 1 input
  have hlarge : 10 * es.length + 10 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_right _ (List.mem_cons_self))
  refine ⟨w, ?_, ⟨0, 5 * es.length, rfl, listAt_initMem _, by omega, ?_, by omega⟩, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · intro e he x hx
    exact lt_two_pow_wordSize_of_mem (by decide)
      (List.mem_append_left _ (List.mem_flatMap.mpr ⟨e, he, hx⟩))
  · change ZeroFrom (initMem (es.flatMap J.solverEdgeWords)) (5 * es.length)
    simpa only [J.solverEdgeRecords_length] using zeroFrom_initMem (es.flatMap J.solverEdgeWords)
  · change 5 * es.length + 5 * es.length < 2 ^ w
    omega

end MinCostFlow.Scaling.Machine
