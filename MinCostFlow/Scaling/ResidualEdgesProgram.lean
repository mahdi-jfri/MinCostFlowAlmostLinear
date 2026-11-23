module

public import MinCostFlow.Scaling.ResidualLayout
public import MinCostFlow.Scaling.WordFiveProgram
import WordRAM.Tactic
import WordRAM.Memory
import WordRAM.Entry

/-!
# Writing a residual edge block

The residual construction in Appendix C of Chen et al., arXiv:2203.00671v2,
scans integral feasible edge values. A forward block subtracts the flow from
capacity. A reverse block swaps endpoints, uses the flow as capacity, and
negates the cost sign while preserving canonical zero. This procedure writes
exactly the selected residual records, in original edge order, with cost
at most `300*edgeCount+20` and exactly five allocated words per edge.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[firstEdge,flowTable,edgeCount,heap]`. Direction is fixed
in the procedure body. -/
def residualEdgesBody (reverse : Bool) (self writer : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.reg 3))
    (.call 4 writer [
      if reverse then .load (.bin .add (.reg 0) (.const 1)) else .load (.reg 0),
      if reverse then .load (.reg 0) else .load (.bin .add (.reg 0) (.const 1)),
      if reverse then .load (.reg 1)
        else .bin .sub (.load (.bin .add (.reg 0) (.const 2))) (.load (.reg 1)),
      if reverse then .bin .mul
        (.bin .sub (.const 1) (.load (.bin .add (.reg 0) (.const 3))))
        (.bin .lt (.const 0) (.load (.bin .add (.reg 0) (.const 4))))
        else .load (.bin .add (.reg 0) (.const 3)),
      .load (.bin .add (.reg 0) (.const 4)), .reg 3] ;;
    .call 5 self [.bin .add (.reg 0) (.const 5), .bin .add (.reg 1) (.const 1),
      .bin .sub (.reg 2) (.const 1), .reg 4] ;;
    .ret (.reg 5))

/-- A residual block scan and its five-word writer. -/
def residualEdgesModule (reverse : Bool) (b : ℕ) : List Stmt :=
  [residualEdgesBody reverse b (b + 1), wordFiveBody]

/-- Both the input graph records and unsigned integral flow table precede
the fresh output. The only flow conditions are its edgewise capacity bounds. -/
def residualEdgesContract (w : ℕ) (J : Circulation) (f : Fin J.m → ℤ)
    (reverse : Bool) (es : List (Fin J.m)) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a flow heap, args = [a, flow, es.length, heap] ∧
      ListAt mem a (es.flatMap J.solverEdgeWords) ∧
      ListAt mem flow (es.map fun e => (f e).toNat) ∧
      a + 5 * es.length ≤ heap ∧ flow + es.length ≤ heap ∧
      (∀ e ∈ es, 0 ≤ f e ∧ f e ≤ J.capacity e) ∧
      (∀ e ∈ es, ∀ x ∈ J.solverEdgeWords e, x < 2 ^ w) ∧ 8 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args) (es.flatMap (residualEdgeWords J f reverse)))
    (fun _ _ => 300 * es.length + 20) (fun _ _ => 5 * es.length)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 5 * es.length }

/-- Neither the residual scan nor its writer has random instructions. -/
theorem residualEdgesModule_noRand (reverse : Bool) (b : ℕ) :
    ∀ body ∈ residualEdgesModule reverse b, body.NoRand := by
  simp only [residualEdgesModule, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨by simp only [residualEdgesBody, Stmt.NoRand, and_self], wordFiveBody_noRand⟩

/-- The scan computes each exact residual record and preserves both source
arrays, with exact fresh allocation and linear machine cost. -/
theorem residualEdges_meetsContract {w b : ℕ} {p : Program} (reverse : Bool)
    (hp : p.HasAt b (residualEdgesModule reverse b)) (J : Circulation)
    (f : Fin J.m → ℤ) (es : List (Fin J.m)) :
    MeetsContract w p b (residualEdgesContract w J f reverse es) := by
  have hwriter : p.HasAt (b + 1) wordFiveModule := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [residualEdgesModule, wordFiveModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [residualEdgesModule])
  have hkW := wordFive_meetsContract (w := w) hwriter
  induction es with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a, flow, heap, rfl, _, _, _, _, _, _, hw⟩, hzero, hspace⟩ := hpre
    change ZeroFrom mem heap at hzero
    change heap + 0 < 2 ^ w at hspace
    have hh : heap < 2 ^ w := by omega
    have hone : 1 < 2 ^ w := by omega
    apply runs_start_le
    unfold residualEdgesBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change (heap ≤ heap ∧ heap ≤ heap + 0 ∧ (∀ x < heap, mem x = mem x) ∧
          ZeroFrom mem heap ∧ ListAt mem heap []) ∧ heap = heap + 0
        exact ⟨⟨le_rfl, by omega, fun _ _ => rfl, hzero, listAt_nil _ _⟩, by omega⟩
      · simp only [residualEdgesContract, heapContract, List.length_nil,
          Expr.size_bin, Expr.size_reg, Expr.size_const]
        omega
    · simp at hcond
  | cons e es ih =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a, flow, heap, rfl, hat, hflow, hend, hflowend, hfeasible, hinput, hw⟩, hzero, hspace⟩ := hpre
    change ZeroFrom mem heap at hzero
    change heap + 5 * (e :: es).length < 2 ^ w at hspace
    obtain ⟨hhead, htail⟩ := listAt_append.mp hat
    change ListAt mem a (J.solverEdgeWords e) at hhead
    change ListAt mem (a + 5) (es.flatMap J.solverEdgeWords) at htail
    obtain ⟨hfcell, hftail⟩ := listAt_cons.mp hflow
    change mem flow = (f e).toNat at hfcell
    change ListAt mem (flow + 1) (es.map fun e => (f e).toNat) at hftail
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
    have htword : (J.tail e : ℕ) < 2 ^ w := hinput e (List.mem_cons_self) _ (by simp [Circulation.solverEdgeWords])
    have hhword : (J.head e : ℕ) < 2 ^ w := hinput e (List.mem_cons_self) _ (by simp [Circulation.solverEdgeWords])
    have hcword : J.capacity e < 2 ^ w := hinput e (List.mem_cons_self) _ (by simp [Circulation.solverEdgeWords])
    have hcmword : (J.cost e).natAbs < 2 ^ w := hinput e (List.mem_cons_self) _ (by simp [Circulation.solverEdgeWords])
    have hcsword : (if J.cost e < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
    have hf := hfeasible e (List.mem_cons_self)
    have hfword : (f e).toNat < 2 ^ w := by omega
    have hsub := residual_capacity_sub (J.capacity e) (f e) hf.1 hf.2
    have hcapword : ((J.capacity e : ℤ) - f e).toNat < 2 ^ w := by omega
    have hncsword : (if -J.cost e < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
    have hflipword : 1 - (if J.cost e < 0 then 1 else 0 : ℕ) < 2 ^ w := by omega
    have hnegword : (1 - (if J.cost e < 0 then 1 else 0 : ℕ)) *
        (if 0 < (J.cost e).natAbs then 1 else 0) < 2 ^ w := by
      rw [← negatedCostSign_eq]
      exact hncsword
    have hheap5 : heap + 5 < 2 ^ w := by simp only [List.length_cons, Nat.mul_succ] at hspace; omega
    have hheap : heap < 2 ^ w := by omega
    have ha5 : a + 5 < 2 ^ w := by simp only [List.length_cons, Nat.mul_succ] at hend; omega
    have ha : a < 2 ^ w := by omega
    have ha1 : a + 1 < 2 ^ w := by omega
    have ha2 : a + 2 < 2 ^ w := by omega
    have ha3 : a + 3 < 2 ^ w := by omega
    have ha4 : a + 4 < 2 ^ w := by omega
    have hfa1 : flow + 1 < 2 ^ w := by simp only [List.length_cons] at hflowend; omega
    have hfa : flow < 2 ^ w := by omega
    have hlen : (e :: es).length < 2 ^ w := hwords _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
    have hone : 1 < 2 ^ w := by omega
    apply runs_start_le
    unfold residualEdgesBody
    wram_step
    · simp at hcond
    · refine runs_seq_call_le hkW
        (vs := [if reverse then (J.head e : ℕ) else J.tail e,
          if reverse then (J.tail e : ℕ) else J.head e,
          if reverse then (f e).toNat else ((J.capacity e : ℤ) - f e).toNat,
          if reverse then (if -J.cost e < 0 then 1 else 0) else (if J.cost e < 0 then 1 else 0),
          (J.cost e).natAbs, heap]) ?_ ?_ ?_ ?_
      · cases reverse
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [← hsub]
          eval_expr
        · simp only [↓reduceIte]
          rw [negatedCostSign_eq]
          eval_expr
      · cases reverse <;> (try simp only [Bool.false_eq_true, ↓reduceIte]) <;> wram_words
      · exact ⟨⟨_, _, _, _, _, heap, rfl⟩, hzero, hheap5⟩
      · intro nextHeap memW posW hpostW
        obtain ⟨⟨_, _, hframeW, hzeroW, hrecord⟩, hptr⟩ := hpostW
        change nextHeap = heap + 5 at hptr
        change (∀ x < heap, memW x = mem x) at hframeW
        change ZeroFrom memW nextHeap at hzeroW
        have hrecord' : ListAt memW heap (residualEdgeWords J f reverse e) := by
          cases reverse <;> exact hrecord
        have htailW : ListAt memW (a + 5) (es.flatMap J.solverEdgeWords) := by
          apply htail.of_agree_below (h₀ := heap)
          · rw [J.solverEdgeRecords_length]
            simp only [List.length_cons, Nat.mul_succ] at hend
            omega
          · exact hframeW
        have hftailW : ListAt memW (flow + 1) (es.map fun e => (f e).toNat) := by
          apply hftail.of_agree_below (h₀ := heap)
          · simp only [List.length_map]
            simp only [List.length_cons] at hflowend
            omega
          · exact hframeW
        have hnextword : nextHeap < 2 ^ w := by omega
        have htailLen : es.length < 2 ^ w := lt_trans (Nat.lt_succ_self _) hlen
        refine runs_seq_call_le ih (vs := [a + 5, flow + 1, es.length, nextHeap]) ?_ ?_ ?_ ?_
        · have heq : (e :: es).length - 1 = es.length := rfl
          rw [← heq]; eval_expr
        · wram_words
        · refine ⟨⟨a + 5, flow + 1, nextHeap, rfl, htailW, hftailW, ?_, ?_,
            (fun e' he' => hfeasible e' (List.mem_cons_of_mem e he')),
            (fun e' he' => hinput e' (List.mem_cons_of_mem e he')), hw⟩, hzeroW, ?_⟩
          · simp only [List.length_cons, Nat.mul_succ] at hend
            omega
          · simp only [List.length_cons] at hflowend
            omega
          · change nextHeap + 5 * es.length < 2 ^ w
            simp only [List.length_cons, Nat.mul_succ] at hspace
            omega
        · intro out memR posR hpostR
          obtain ⟨⟨_, _, hframeR, hzeroR, hrecords⟩, hout⟩ := hpostR
          change (∀ x < nextHeap, memR x = memW x) at hframeR
          change ZeroFrom memR out at hzeroR
          change ListAt memR nextHeap (es.flatMap (residualEdgeWords J f reverse)) at hrecords
          change out = nextHeap + 5 * es.length at hout
          have houtword : out < 2 ^ w := by simp only [List.length_cons, Nat.mul_succ] at hspace; omega
          refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
          · change (heap ≤ out ∧ out ≤ heap + 5 * (e :: es).length ∧
              (∀ x < heap, memR x = mem x) ∧ ZeroFrom memR out ∧
              ListAt memR heap ((e :: es).flatMap (residualEdgeWords J f reverse))) ∧
              out = heap + 5 * (e :: es).length
            refine ⟨⟨by omega, by simp only [List.length_cons, Nat.mul_succ]; omega,
              ?_, hzeroR, ?_⟩, by simp only [List.length_cons, Nat.mul_succ]; omega⟩
            · intro x hx
              exact (hframeR x (by omega)).trans (hframeW x hx)
            · apply listAt_append.mpr
              refine ⟨hrecord'.of_agree_below (h₀ := nextHeap)
                (by rw [residualEdgeWords_length]; omega) hframeR, ?_⟩
              simpa only [residualEdgeWords_length, hptr, List.flatMap] using hrecords
          · simp only [residualEdgesContract, heapContract, wordFiveContract, List.length_cons,
              argsSize_cons, argsSize_nil, Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
            cases reverse <;> (try simp only [Bool.false_eq_true, ↓reduceIte, Expr.size_load,
              Expr.size_bin, Expr.size_reg, Expr.size_const]) <;> omega

/-- Every edgewise feasible integral flow admits a concrete pair of source
arrays satisfying all residual-scan premises at a sufficiently large width. -/
theorem exists_residualEdges_pre (J : Circulation) (f : Fin J.m → ℤ)
    (reverse : Bool) (es : List (Fin J.m))
    (hf : ∀ e ∈ es, 0 ≤ f e ∧ f e ≤ J.capacity e) :
    ∃ w mem, (∀ x ∈ [0, 5 * es.length, es.length, 6 * es.length], x < 2 ^ w) ∧
      (residualEdgesContract w J f reverse es).pre
        [0, 5 * es.length, es.length, 6 * es.length] mem := by
  let records := es.flatMap J.solverEdgeWords
  let flowWords := es.map fun e => (f e).toNat
  let mem := initMem (records ++ flowWords)
  let input := records ++ [20 * es.length + 10]
  let w := wordSize 1 input
  have hlarge : 20 * es.length + 10 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_right _ (List.mem_cons_self))
  have hrecordslen : records.length = 5 * es.length := J.solverEdgeRecords_length es
  have hflowlen : flowWords.length = es.length := by simp only [flowWords, List.length_map]
  have hstored := listAt_append.mp (listAt_initMem (records ++ flowWords))
  have hflow : ListAt mem (5 * es.length) flowWords := by
    simpa only [Nat.zero_add, hrecordslen] using hstored.2
  have hzero : ZeroFrom mem (6 * es.length) := by
    have he : 5 * es.length + es.length = 6 * es.length := by omega
    simpa only [List.length_append, hrecordslen, hflowlen, he] using
      zeroFrom_initMem (records ++ flowWords)
  refine ⟨w, mem, ?_, ⟨0, 5 * es.length, 6 * es.length, rfl, hstored.1,
    hflow, by omega, by omega, hf, ?_, by omega⟩, hzero, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  · intro e he x hx
    exact lt_two_pow_wordSize_of_mem (by decide)
      (List.mem_append_left _ (List.mem_flatMap.mpr ⟨e, he, hx⟩))
  · change 6 * es.length + 5 * es.length < 2 ^ w
    omega

/-- A directed residual scan occupies two procedure slots. -/
theorem residualEdgesModule_length (reverse : Bool) (b : ℕ) :
    (residualEdgesModule reverse b).length = 2 := rfl

end MinCostFlow.Scaling.Machine
