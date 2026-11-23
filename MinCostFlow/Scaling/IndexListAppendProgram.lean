module

public import MinCostFlow.Scaling.IndexListLayout
public import MinCostFlow.Scaling.WordPairProgram
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Copying a prefix before a stored edge list

Label propagation prepends a newly reached vertex's outgoing list to the
pending edges. This procedure copies exactly the prefix nodes and shares
the suffix. Prefix length is supplied with its representation. New nodes
are written before the recursive call, which preserves their cells. The
procedure allocates two words per prefix entry and costs at most
`100*prefixLength+20` steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Write the current head with its final tail pointer, then copy the rest. -/
def indexListAppendFinish (self writer : ℕ) (next : Expr) : Stmt :=
  .call 4 writer [.load (.reg 0), next, .reg 3] ;;
  .call 5 self [.load (.bin .add (.reg 0) (.const 1)), .reg 1,
    .bin .sub (.reg 2) (.const 1), .reg 4] ;; .ret (.reg 5)

/-- Arguments `[prefixPointer,suffixPointer,prefixLength,heap]`. -/
def indexListAppendBody (self writer : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.reg 3))
    (.cond (.bin .eq (.reg 2) (.const 1))
      (indexListAppendFinish self writer (.reg 1))
      (indexListAppendFinish self writer (.bin .add (.reg 3) (.const 2))))

/-- Prefix copying and the existing two-word writer. -/
def indexListAppendModule (b : ℕ) : List Stmt :=
  [indexListAppendBody b (b+1), wordPairBody]

/-- The old lists are below the fresh heap. The output head is the suffix
pointer for an empty prefix and the old heap for a nonempty prefix. -/
def indexListAppendContract (w lo : ℕ) {m : ℕ} (es rest : List (Fin m)) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ p q heap, args = [p, q, es.length, heap] ∧
      IndexListAt mem lo heap p es ∧ IndexListAt mem lo heap q rest ∧
      0 < heap ∧ lo ≤ heap ∧ (∀ e ∈ es, e.val < 2 ^ w) ∧ 2 < 2 ^ w)
    (fun args _ mem' => IndexListAt mem' lo (heapArg args+2*es.length)
      (if es = [] then args.getD 1 0 else heapArg args) (es ++ rest))
    (fun _ _ => 100*es.length+20) (fun _ _ => 2*es.length)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args+2*es.length }

/-- Prefix copying is deterministic. -/
theorem indexListAppendModule_noRand (b : ℕ) :
    ∀ body ∈ indexListAppendModule b, body.NoRand := by
  intro body hb
  simp only [indexListAppendModule, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · simp only [indexListAppendBody, indexListAppendFinish, Stmt.NoRand, and_self]
  · exact wordPairBody_noRand

/-- The procedure implements the model's list append, allocating and
charging only for the prefix while preserving all old list cells. -/
theorem indexListAppend_meetsContract {w b lo m : ℕ} {p : Program}
    (hp : p.HasAt b (indexListAppendModule b)) (es rest : List (Fin m)) :
    MeetsContract w p b (indexListAppendContract w lo es rest) := by
  have hpair : p.HasAt (b+1) wordPairModule := by
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [indexListAppendModule, wordPairModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [indexListAppendModule])
  have hkW := wordPair_meetsContract (w := w) hpair
  induction es with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨ptr, tail, heap, rfl, _, hrest, _, _, _, hw⟩, hzero, hspace⟩ := hpre
    change ZeroFrom mem heap at hzero
    change heap+2*0 < 2 ^ w at hspace
    have hh : heap < 2 ^ w := by omega
    have hone : 1 < 2 ^ w := by omega
    apply runs_start_le
    unfold indexListAppendBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change (heap ≤ heap ∧ heap ≤ heap+2*0 ∧ (∀ x < heap, mem x = mem x) ∧
          ZeroFrom mem heap ∧ IndexListAt mem lo (heap+2*0) tail ([] ++ rest)) ∧ heap = heap+2*0
        simpa only [Nat.mul_zero, Nat.add_zero, List.nil_append] using
          (show (heap ≤ heap ∧ heap ≤ heap ∧ (∀ x < heap, mem x = mem x) ∧
            ZeroFrom mem heap ∧ IndexListAt mem lo heap tail rest) ∧ heap = heap from
            ⟨⟨le_rfl, le_rfl, fun _ _ => rfl, hzero, hrest⟩, rfl⟩)
      · simp only [indexListAppendContract, heapContract, List.length_nil,
          Expr.size_bin, Expr.size_reg, Expr.size_const]; omega
    · simp at hcond
  | cons e es ih =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨ptr, tail, heap, rfl, hprefix, hrest, hpositive, hlower, hindices, hw⟩,
      hzero, hspace⟩ := hpre
    change ZeroFrom mem heap at hzero
    change heap+2*(e :: es).length < 2 ^ w at hspace
    obtain ⟨hpPos, hpLow, hpEnd, hhead, oldTail, hnext, hprefixTail⟩ := indexListAt_cons_iff.mp hprefix
    have hindex := hindices e List.mem_cons_self
    have htail : tail < 2 ^ w := hwords _ (by simp)
    have hlen : (e :: es).length < 2 ^ w := hwords _ (by simp)
    have hptr : ptr < 2 ^ w := by omega
    have hptr1 : ptr+1 < 2 ^ w := by omega
    have hheap : heap < 2 ^ w := by omega
    have hheap2 : heap+2 < 2 ^ w := by simp only [List.length_cons] at hspace; omega
    have holdTail : oldTail < 2 ^ w := hprefixTail.pointer_le.trans_lt hheap
    have hone : 1 < 2 ^ w := by omega
    let selected := if es = [] then tail else heap+2
    have hselected : selected < 2 ^ w := by dsimp [selected]; split <;> assumption
    apply runs_start_le
    unfold indexListAppendBody
    wram_step
    · simp at hcond
    · wram_step
      all_goals
        unfold indexListAppendFinish
        refine runs_seq_call_le hkW (vs := [e.val, selected, heap]) ?_ ?_ ?_ ?_
        · by_cases hnil : es = []
          · simp [hnil] at hcond
            all_goals
              dsimp only [selected]
              rw [ite_eq_left hnil]
              eval_expr
          · simp [hnil] at hcond
            all_goals
              dsimp only [selected]
              rw [ite_eq_right hnil]
              eval_expr
        · wram_words
        · exact ⟨⟨_, _, heap, rfl⟩, hzero, hheap2⟩
        · intro nextHeap memW posW hpostW
          obtain ⟨⟨_, _, hframeW, hzeroW, hpairs⟩, hnextHeap⟩ := hpostW
          change nextHeap = heap+2 at hnextHeap
          change (∀ x < heap, memW x = mem x) at hframeW
          change ZeroFrom memW nextHeap at hzeroW
          change ListAt memW heap [e.val, selected] at hpairs
          have hprefixW : IndexListAt memW lo nextHeap oldTail es := by
            apply (hprefixTail.of_agree (fun x _ hx => hframeW x hx)).mono le_rfl
            omega
          have hrestW : IndexListAt memW lo nextHeap tail rest := by
            apply (hrest.of_agree (fun x _ hx => hframeW x hx)).mono le_rfl
            omega
          have hnextMem : memW (ptr+1) = oldTail := (hframeW _ (by omega)).trans hnext
          have hnextHeapWord : nextHeap < 2 ^ w := by omega
          have hlenTail : es.length < 2 ^ w := by simp only [List.length_cons] at hlen; omega
          refine runs_seq_call_le ih (vs := [oldTail, tail, es.length, nextHeap]) ?_ ?_ ?_ ?_
          · have heq : (e :: es).length-1 = es.length := rfl
            rw [← heq]; eval_expr
          · wram_words
          · refine ⟨⟨oldTail, tail, nextHeap, rfl, hprefixW, hrestW, by omega, by omega,
              fun e' he' => hindices e' (List.mem_cons_of_mem e he'), hw⟩, hzeroW, ?_⟩
            change nextHeap+2*es.length < 2 ^ w
            simp only [List.length_cons] at hspace; omega
          · intro out memR posR hpostR
            obtain ⟨⟨_, _, hframeR, hzeroR, hresultR⟩, hout⟩ := hpostR
            change out = nextHeap+2*es.length at hout
            change (∀ x < nextHeap, memR x = memW x) at hframeR
            change ZeroFrom memR out at hzeroR
            change IndexListAt memR lo (nextHeap+2*es.length)
              (if es = [] then tail else nextHeap) (es ++ rest) at hresultR
            have htotal : nextHeap+2*es.length = heap+2*(e :: es).length := by
              simp only [List.length_cons]; omega
            have hselectEq : selected = if es = [] then tail else nextHeap := by rw [hnextHeap]
            have hresultHead : memR heap = e.val := by
              have h := hpairs 0 (by change 0 < 2; decide)
              change memW (heap+0) = e.val at h
              rw [Nat.add_zero] at h
              exact (hframeR heap (by omega)).trans h
            have hresultNext : memR (heap+1) = if es = [] then tail else nextHeap := by
              have h := hpairs 1 (by change 1 < 2; decide)
              change memW (heap+1) = selected at h
              rw [hselectEq] at h
              exact (hframeR (heap+1) (by omega)).trans h
            have houtWord : out < 2 ^ w := by simp only [List.length_cons] at hspace; omega
            refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
            · change (heap ≤ out ∧ out ≤ heap+2*(e :: es).length ∧
                (∀ x < heap, memR x = mem x) ∧ ZeroFrom memR out ∧
                IndexListAt memR lo (heap+2*(e :: es).length) heap ((e :: es) ++ rest)) ∧
                out = heap+2*(e :: es).length
              refine ⟨⟨by omega, by omega, ?_, hzeroR, ?_⟩, by omega⟩
              · intro x hx
                exact (hframeR x (by omega)).trans (hframeW x hx)
              · exact .cons hpositive hlower (by simp only [List.length_cons]; omega)
                  hresultHead hresultNext (htotal ▸ hresultR)
            · simp only [indexListAppendContract, heapContract, wordPairContract,
                List.length_cons, argsSize_cons, argsSize_nil, Expr.size_bin, Expr.size_load,
                Expr.size_reg, Expr.size_const]; omega

/-- Arbitrary prefix and suffix lists have simultaneous layout, word, and
allocation premises, including when both are nonempty. -/
theorem exists_indexListAppend_pre {m : ℕ} (es rest : List (Fin m)) :
    ∃ w mem ptr tail heap, (∀ x ∈ [ptr, tail, es.length, heap], x < 2 ^ w) ∧
      (indexListAppendContract w 1 es rest).pre [ptr, tail, es.length, heap] mem := by
  obtain ⟨mem, heap, ptr, tail, hheap, hprefix, hrest, hzero⟩ := exists_two_indexListsAt es rest
  let w := m+heap+2*es.length+4
  have hw : m+heap+2*es.length+4 < 2 ^ w := Nat.lt_two_pow_self
  have hp := hprefix.pointer_le
  have ht := hrest.pointer_le
  refine ⟨w, mem, ptr, tail, heap, ?_, ⟨ptr, tail, heap, rfl, hprefix, hrest,
    by omega, hheap, ?_, by omega⟩, hzero, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  · intro e _
    have he := e.isLt
    omega
  · change heap+2*es.length < 2 ^ w
    omega

end MinCostFlow.Scaling.Machine
