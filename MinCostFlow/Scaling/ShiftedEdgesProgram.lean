module

public import MinCostFlow.Scaling.ShiftedInputLayout
public import MinCostFlow.Scaling.CapacityDifferenceProgram
public import MinCostFlow.Scaling.WordFiveProgram
import WordRAM.Tactic
import WordRAM.Memory
import WordRAM.Entry

/-!
# Building the lower-capacity-shifted edge records

The reduction of Lemma C.1 of Chen et al., arXiv:2203.00671v2, replaces
each consistent capacity interval by its width and keeps endpoints and
costs. This scan reads the statement's eight-word input records and writes
the exact five-word records of `shiftedGraph`. Each edge uses the proved
capacity difference and fresh-record writer. All memory before the heap is
preserved, and the cost is at most `400*edgeCount+20`.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[firstEdge,edgeCount,heap]`. -/
def shiftedEdgesBody (self difference writer : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.reg 2))
    (.call 3 difference [.load (.bin .add (.reg 0) (.const 2)),
      .load (.bin .add (.reg 0) (.const 3)),
      .load (.bin .add (.reg 0) (.const 4)),
      .load (.bin .add (.reg 0) (.const 5))] ;;
    .call 4 writer [.load (.reg 0), .load (.bin .add (.reg 0) (.const 1)),
      .reg 3, .load (.bin .add (.reg 0) (.const 6)),
      .load (.bin .add (.reg 0) (.const 7)), .reg 2] ;;
    .call 5 self [.bin .add (.reg 0) (.const 8),
      .bin .sub (.reg 1) (.const 1), .reg 4] ;;
    .ret (.reg 5))

/-- The recursive scan, capacity difference, and five-word writer. -/
def shiftedEdgesModule (b : ℕ) : List Stmt :=
  [shiftedEdgesBody b (b + 1) (b + 2), capacityDifferenceBody, wordFiveBody]

/-- Consistent input intervals and fitting signed arithmetic suffice to
build the exact shifted edge records in fresh memory. -/
def shiftedEdgesContract (w : ℕ) (edges : List Edge) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a h, args = [a, edges.length, h] ∧
      ListAt mem a (edges.flatMap Edge.encode) ∧ a + 8 * edges.length ≤ h ∧
      (∀ e ∈ edges, e.lower ≤ e.upper) ∧
      (∀ e ∈ edges, e.lower.natAbs + e.upper.natAbs < 2 ^ w) ∧
      (∀ x ∈ edges.flatMap Edge.encode, x < 2 ^ w) ∧ 8 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args) (edges.flatMap shiftedEdgeWords))
    (fun _ _ => 400 * edges.length + 20) (fun _ _ => 5 * edges.length)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 5 * edges.length }

/-- All three procedures of the shifted-record scan have no random instructions. -/
theorem shiftedEdgesModule_noRand (b : ℕ) :
    ∀ body ∈ shiftedEdgesModule b, body.NoRand := by
  simp only [shiftedEdgesModule, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨by simp only [shiftedEdgesBody, Stmt.NoRand, and_self],
    capacityDifferenceBody_noRand, wordFiveBody_noRand⟩

/-- The scan computes exactly the shifted edge list, with linear cost,
exact allocation, and the standard heap frame. -/
theorem shiftedEdges_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (shiftedEdgesModule b)) (edges : List Edge) :
    MeetsContract w p b (shiftedEdgesContract w edges) := by
  have hdiff : p.HasAt (b + 1) capacityDifferenceModule := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [shiftedEdgesModule, capacityDifferenceModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [shiftedEdgesModule])
  have hwriter : p.HasAt (b + 2) wordFiveModule := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [shiftedEdgesModule, wordFiveModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 2 (by simp [shiftedEdgesModule])
  have hkW := wordFive_meetsContract (w := w) hwriter
  induction edges with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a, heap, rfl, _, _, _, _, _, hw⟩, hzero, hspace⟩ := hpre
    change ZeroFrom mem heap at hzero
    change heap + 0 < 2 ^ w at hspace
    have hh : heap < 2 ^ w := by omega
    have hone : 1 < 2 ^ w := by omega
    apply runs_start_le
    unfold shiftedEdgesBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change (heap ≤ heap ∧ heap ≤ heap + 0 ∧ (∀ x < heap, mem x = mem x) ∧
          ZeroFrom mem heap ∧ ListAt mem heap []) ∧ heap = heap + 0
        exact ⟨⟨le_rfl, by omega, fun _ _ => rfl, hzero, listAt_nil _ _⟩, by omega⟩
      · simp only [shiftedEdgesContract, heapContract, List.length_nil,
          Expr.size_bin, Expr.size_reg, Expr.size_const]
        omega
    · simp at hcond
  | cons e edges ih =>
    have hkD := capacityDifference_meetsContract (w := w) hdiff e.lower e.upper
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a, heap, rfl, hat, hend, horder, hsum, hinput, hw⟩, hzero, hspace⟩ := hpre
    change ZeroFrom mem heap at hzero
    change heap + 5 * (e :: edges).length < 2 ^ w at hspace
    have hsplit := listAt_append.mp hat
    change ListAt mem a e.encode ∧ ListAt mem (a + e.encode.length) (edges.flatMap Edge.encode) at hsplit
    have htail : ListAt mem (a + 8) (edges.flatMap Edge.encode) := by
      simpa only [edge_encode_length] using hsplit.2
    have hfields : ∀ j : Fin 8, mem (a + j.val) = e.encode.getD j.val 0 := by
      intro j
      have hj : j.val < e.encode.length := by rw [edge_encode_length]; exact j.isLt
      rw [List.getD_eq_getElem _ _ hj]
      exact hsplit.1 _ hj
    have ht := hfields ⟨0, by decide⟩
    have hh := hfields ⟨1, by decide⟩
    have hls := hfields ⟨2, by decide⟩
    have hlm := hfields ⟨3, by decide⟩
    have hus := hfields ⟨4, by decide⟩
    have hum := hfields ⟨5, by decide⟩
    have hcs := hfields ⟨6, by decide⟩
    have hcm := hfields ⟨7, by decide⟩
    simp only [Edge.encode, encodeInt, List.cons_append, List.nil_append,
      List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero] at ht hh hls hlm hus hum hcs hcm
    have hheadwords : ∀ x ∈ e.encode, x < 2 ^ w := by
      intro x hx
      exact hinput x (List.mem_append_left _ hx)
    have htailwords : ∀ x ∈ edges.flatMap Edge.encode, x < 2 ^ w := by
      intro x hx
      exact hinput x (List.mem_append_right _ hx)
    have htword : e.tail < 2 ^ w := hheadwords _ (by simp [Edge.encode])
    have hhword : e.head < 2 ^ w := hheadwords _ (by simp [Edge.encode])
    have hcsword : (if e.cost < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
    have hcmword : e.cost.natAbs < 2 ^ w := hheadwords _ (by simp [Edge.encode, encodeInt])
    have hdiffwords : ∀ x ∈ [if e.lower < 0 then 1 else 0, e.lower.natAbs,
        if e.upper < 0 then 1 else 0, e.upper.natAbs], x < 2 ^ w := by
      intro x hx
      apply hheadwords x
      simp only [Edge.encode, encodeInt, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl <;> tauto
    have hcapacityword : (e.upper - e.lower).toNat < 2 ^ w := by
      have hbound := hsum e (List.mem_cons_self)
      omega
    have hbefore : a + 8 + 8 * edges.length ≤ heap := by
      simp only [List.length_cons, Nat.mul_succ] at hend
      omega
    have ha8 : a + 8 < 2 ^ w := by omega
    have ha1 : a + 1 < 2 ^ w := by omega
    have ha2 : a + 2 < 2 ^ w := by omega
    have ha3 : a + 3 < 2 ^ w := by omega
    have ha4 : a + 4 < 2 ^ w := by omega
    have ha5 : a + 5 < 2 ^ w := by omega
    have ha6 : a + 6 < 2 ^ w := by omega
    have ha7 : a + 7 < 2 ^ w := by omega
    have hheap5 : heap + 5 < 2 ^ w := by
      simp only [List.length_cons, Nat.mul_succ] at hspace
      omega
    have hheap : heap < 2 ^ w := by omega
    have hlen : (e :: edges).length < 2 ^ w := hwords _ (by simp)
    have hone : 1 < 2 ^ w := by omega
    apply runs_start_le
    unfold shiftedEdgesBody
    wram_step
    · simp at hcond
    · refine runs_seq_call_le hkD
        (vs := [if e.lower < 0 then 1 else 0, e.lower.natAbs,
          if e.upper < 0 then 1 else 0, e.upper.natAbs])
        (by eval_expr) hdiffwords ⟨rfl, horder _ (List.mem_cons_self), hsum _ (List.mem_cons_self), hone⟩ ?_
      intro capacity memD posD hpostD
      obtain ⟨hmemD, hcapacity⟩ := hpostD
      change memD = mem at hmemD
      subst memD
      change capacity = (e.upper - e.lower).toNat at hcapacity
      have hcapword : capacity < 2 ^ w := hcapacity ▸ hcapacityword
      refine runs_seq_call_le hkW
        (vs := [e.tail, e.head, capacity, if e.cost < 0 then 1 else 0, e.cost.natAbs, heap])
        (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨⟨_, _, _, _, _, heap, rfl⟩, hzero, hheap5⟩
      · intro nextHeap memW posW hpostW
        obtain ⟨⟨_, _, hframeW, hzeroW, hrecord⟩, hptr⟩ := hpostW
        change nextHeap = heap + 5 at hptr
        change (∀ x < heap, memW x = mem x) at hframeW
        change ZeroFrom memW nextHeap at hzeroW
        change ListAt memW heap [e.tail, e.head, capacity,
          if e.cost < 0 then 1 else 0, e.cost.natAbs] at hrecord
        rw [hcapacity] at hrecord
        have hnextword : nextHeap < 2 ^ w := by omega
        have htailW : ListAt memW (a + 8) (edges.flatMap Edge.encode) := by
          apply htail.of_agree_below (h₀ := heap)
          · rw [edges_encode_length]
            exact hbefore
          · exact hframeW
        refine runs_seq_call_le ih (vs := [a + 8, edges.length, nextHeap]) ?_ ?_ ?_ ?_
        · have heq : (e :: edges).length - 1 = edges.length := rfl
          rw [← heq]; eval_expr
        · wram_words
        · refine ⟨⟨a + 8, nextHeap, rfl, htailW, by omega,
            (fun e' he' => horder e' (List.mem_cons_of_mem e he')),
            (fun e' he' => hsum e' (List.mem_cons_of_mem e he')), htailwords, hw⟩, hzeroW, ?_⟩
          change nextHeap + 5 * edges.length < 2 ^ w
          simp only [List.length_cons, Nat.mul_succ] at hspace
          omega
        · intro out memR posR hpostR
          obtain ⟨⟨_, _, hframeR, hzeroR, hrecords⟩, hout⟩ := hpostR
          change (∀ x < nextHeap, memR x = memW x) at hframeR
          change ZeroFrom memR out at hzeroR
          change ListAt memR nextHeap (edges.flatMap shiftedEdgeWords) at hrecords
          change out = nextHeap + 5 * edges.length at hout
          have houtword : out < 2 ^ w := by
            simp only [List.length_cons, Nat.mul_succ] at hspace
            omega
          refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
          · change (heap ≤ out ∧ out ≤ heap + 5 * (e :: edges).length ∧
              (∀ x < heap, memR x = mem x) ∧ ZeroFrom memR out ∧
              ListAt memR heap ((e :: edges).flatMap shiftedEdgeWords)) ∧
              out = heap + 5 * (e :: edges).length
            refine ⟨⟨by omega, by simp only [List.length_cons, Nat.mul_succ]; omega,
              ?_, hzeroR, ?_⟩, by simp only [List.length_cons, Nat.mul_succ]; omega⟩
            · intro x hx
              exact (hframeR x (by omega)).trans (hframeW x hx)
            · apply listAt_append.mpr
              constructor
              · apply hrecord.of_agree_below (h₀ := nextHeap)
                · change heap + 5 ≤ nextHeap
                  omega
                · exact hframeR
              · simpa only [List.flatMap, shiftedEdgeWords_length, hptr] using hrecords
          · simp only [shiftedEdgesContract, heapContract, wordFiveContract,
              capacityDifferenceContract, List.length_cons, argsSize_cons, argsSize_nil,
              Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
            omega

/-- Every consistent edge list can satisfy all arithmetic, layout, and
fresh-memory premises at once. -/
theorem exists_shiftedEdges_pre (edges : List Edge)
    (horder : ∀ e ∈ edges, e.lower ≤ e.upper) :
    ∃ w, (∀ x ∈ [0, edges.length, 8 * edges.length], x < 2 ^ w) ∧
      (shiftedEdgesContract w edges).pre [0, edges.length, 8 * edges.length]
        (initMem (edges.flatMap Edge.encode)) := by
  let input := edges.flatMap Edge.encode ++
    ((edges.map fun e => e.lower.natAbs + e.upper.natAbs) ++ [20 * edges.length + 10])
  let w := wordSize 1 input
  have hlarge : 20 * edges.length + 10 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide)
      (List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_self)))
  refine ⟨w, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · refine ⟨⟨0, 8 * edges.length, rfl, listAt_initMem _, by omega, horder,
      ?_, ?_, by omega⟩, ?_, ?_⟩
    · intro e he
      exact lt_two_pow_wordSize_of_mem (by decide)
        (List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩)))
    · intro x hx
      exact lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_left _ hx)
    · change ZeroFrom (initMem (edges.flatMap Edge.encode)) (8 * edges.length)
      simpa only [edges_encode_length] using zeroFrom_initMem (edges.flatMap Edge.encode)
    · change 8 * edges.length + 5 * edges.length < 2 ^ w
      omega

end MinCostFlow.Scaling.Machine
