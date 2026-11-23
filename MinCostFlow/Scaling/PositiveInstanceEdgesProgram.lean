module

public import MinCostFlow.Scaling.PositiveInstanceLayout
public import MinCostFlow.Scaling.WordFiveProgram
import WordRAM.Tactic
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# Replacing inactive residual slots by positive-capacity loops

The bounded circulation solver accepts positive capacities. This scan
retains all edge slots. It copies an active record and replaces an inactive
record by a zero-cost unit loop at the supplied new vertex. The output is
exactly the edge block of `positiveInstance`, in linear time and fresh space.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[source,count,newVertex,heap]`. -/
def positiveInstanceEdgesBody (self writer : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.reg 3))
    (.cond (.bin .eq (.load (.bin .add (.reg 0) (.const 2))) (.const 0))
      (.call 4 writer [.reg 2, .reg 2, .const 1, .const 0, .const 0, .reg 3])
      (.call 4 writer [.load (.reg 0), .load (.bin .add (.reg 0) (.const 1)),
        .load (.bin .add (.reg 0) (.const 2)), .load (.bin .add (.reg 0) (.const 3)),
        .load (.bin .add (.reg 0) (.const 4)), .reg 3]) ;;
     .call 5 self [.bin .add (.reg 0) (.const 5), .bin .sub (.reg 1) (.const 1), .reg 2, .reg 4] ;;
     .ret (.reg 5))

/-- The adapter scan and shared five-word writer. -/
def positiveInstanceEdgesModule (b : ℕ) : List Stmt :=
  [positiveInstanceEdgesBody b (b+1), wordFiveBody]

/-- Source records precede fresh output. The extra vertex is exactly `J.n`. -/
def positiveInstanceEdgesContract (w : ℕ) (J : Circulation) (es : List (Fin J.m)) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a heap, args = [a, es.length, J.n, heap] ∧
      ListAt mem a (es.flatMap J.solverEdgeWords) ∧ a+5*es.length ≤ heap ∧
      (∀ e ∈ es, ∀ x ∈ J.solverEdgeWords e, x < 2 ^ w) ∧ 8 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args) (es.flatMap J.positiveInstance.solverEdgeWords))
    (fun _ _ => 300*es.length+20) (fun _ _ => 5*es.length)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args+5*es.length }

/-- Inactive-slot replacement and its writer use no random instructions. -/
theorem positiveInstanceEdgesModule_noRand (b : ℕ) :
    ∀ body ∈ positiveInstanceEdgesModule b, body.NoRand := by
  intro body hb
  simp only [positiveInstanceEdgesModule, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · simp only [positiveInstanceEdgesBody, Stmt.NoRand, and_self]
  · exact wordFiveBody_noRand

/-- The scan computes exactly the model's positive-capacity edge block,
with no removed slots, exact allocation, and cost at most `300*count+20`. -/
theorem positiveInstanceEdges_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (positiveInstanceEdgesModule b)) (J : Circulation) (es : List (Fin J.m)) :
    MeetsContract w p b (positiveInstanceEdgesContract w J es) := by
  have hwriter : p.HasAt (b+1) wordFiveModule := by
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [positiveInstanceEdgesModule, wordFiveModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [positiveInstanceEdgesModule])
  have hkW := wordFive_meetsContract (w := w) hwriter
  induction es with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a, heap, rfl, _, _, _, hw⟩, hzero, hspace⟩ := hpre
    change ZeroFrom mem heap at hzero
    change heap+5*0 < 2 ^ w at hspace
    have hh : heap < 2 ^ w := by omega
    have hone : 1 < 2 ^ w := by omega
    apply runs_start_le
    unfold positiveInstanceEdgesBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change (heap ≤ heap ∧ heap ≤ heap+5*0 ∧ (∀ x < heap, mem x = mem x) ∧
          ZeroFrom mem heap ∧ ListAt mem heap []) ∧ heap = heap+5*0
        exact ⟨⟨le_rfl, by omega, fun _ _ => rfl, hzero, listAt_nil _ _⟩, by omega⟩
      · simp only [positiveInstanceEdgesContract, heapContract, List.length_nil,
          Expr.size_bin, Expr.size_reg, Expr.size_const]; omega
    · simp at hcond
  | cons e es ih =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a, heap, rfl, hat, hend, hinput, hw⟩, hzero, hspace⟩ := hpre
    change ZeroFrom mem heap at hzero
    change heap+5*(e :: es).length < 2 ^ w at hspace
    obtain ⟨hhead, htail⟩ := listAt_append.mp hat
    change ListAt mem a (J.solverEdgeWords e) at hhead
    change ListAt mem (a+5) (es.flatMap J.solverEdgeWords) at htail
    have hfields : ∀ j : Fin 5, mem (a+j.val) = (J.solverEdgeWords e).getD j.val 0 := by
      intro j
      rw [List.getD_eq_getElem _ _ (show j.val < (J.solverEdgeWords e).length from j.isLt)]
      exact hhead _ j.isLt
    have ht := hfields ⟨0, by decide⟩
    have hh := hfields ⟨1, by decide⟩
    have hc := hfields ⟨2, by decide⟩
    have hs := hfields ⟨3, by decide⟩
    have hm := hfields ⟨4, by decide⟩
    simp only [Circulation.solverEdgeWords, List.getD_cons_succ, List.getD_cons_zero,
      Nat.add_zero] at ht hh hc hs hm
    have hroot : J.n < 2 ^ w := hwords _ (by simp)
    have hlen : (e :: es).length < 2 ^ w := hwords _ (by simp)
    have hheap5 : heap+5 < 2 ^ w := by simp only [List.length_cons] at hspace; omega
    have hheap : heap < 2 ^ w := by omega
    have ha5 : a+5 < 2 ^ w := by simp only [List.length_cons] at hend; omega
    have ha : a < 2 ^ w := by omega
    have ha1 : a+1 < 2 ^ w := by omega
    have ha2 : a+2 < 2 ^ w := by omega
    have ha3 : a+3 < 2 ^ w := by omega
    have ha4 : a+4 < 2 ^ w := by omega
    have hone : 1 < 2 ^ w := by omega
    have houtput : ∀ x ∈ J.positiveInstance.solverEdgeWords e, x < 2 ^ w := by
      by_cases hz : J.capacity e = 0
      · rw [positiveInstance_edgeWords_zero J e hz]
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega
      · rw [positiveInstance_edgeWords_nonzero J e hz]
        exact hinput e List.mem_cons_self
    have htailWord : (J.positiveInstance.tail e).val < 2 ^ w := houtput _ (by simp [Circulation.solverEdgeWords])
    have hheadWord : (J.positiveInstance.head e).val < 2 ^ w := houtput _ (by simp [Circulation.solverEdgeWords])
    have hcapWord : J.positiveInstance.capacity e < 2 ^ w := houtput _ (by simp [Circulation.solverEdgeWords])
    have hsignWord : (if J.positiveInstance.cost e < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
    have hmagWord : (J.positiveInstance.cost e).natAbs < 2 ^ w := houtput _ (by simp [Circulation.solverEdgeWords])
    apply runs_start_le
    unfold positiveInstanceEdgesBody
    wram_step
    · simp at hcond
    · wram_step
      all_goals
        refine runs_seq_call_le hkW
          (vs := [(J.positiveInstance.tail e).val, (J.positiveInstance.head e).val,
            J.positiveInstance.capacity e, if J.positiveInstance.cost e < 0 then 1 else 0,
            (J.positiveInstance.cost e).natAbs, heap]) ?_ ?_ ?_ ?_
        · by_cases hz : J.capacity e = 0
          · simp [startState, hc, hz] at hcond
            all_goals
              simp only [Circulation.positiveInstance, hz, ↓reduceIte, Fin.val_last,
                Int.natAbs_zero, lt_self_iff_false]
              eval_expr
          · simp [startState, hc, hz] at hcond
            all_goals
              simp only [Circulation.positiveInstance, hz, ↓reduceIte, Fin.val_castSucc]
              eval_expr
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
        · exact ⟨⟨_, _, _, _, _, heap, rfl⟩, hzero, hheap5⟩
        · intro next memW posW hpostW
          obtain ⟨⟨_, _, hframeW, hzeroW, hrecordW⟩, hnext⟩ := hpostW
          change next = heap+5 at hnext
          change (∀ x < heap, memW x = mem x) at hframeW
          change ZeroFrom memW next at hzeroW
          change ListAt memW heap (J.positiveInstance.solverEdgeWords e) at hrecordW
          have htailW : ListAt memW (a+5) (es.flatMap J.solverEdgeWords) := by
            apply htail.of_agree_below (h₀ := heap)
            · rw [Circulation.solverEdgeRecords_length]
              simp only [List.length_cons] at hend; omega
            · exact hframeW
          have hnextWord : next < 2 ^ w := by omega
          have htailLen : es.length < 2 ^ w := by simp only [List.length_cons] at hlen; omega
          refine runs_seq_call_le ih (vs := [a+5, es.length, J.n, next]) ?_ ?_ ?_ ?_
          · have heq : (e :: es).length-1 = es.length := rfl
            rw [← heq]; eval_expr
          · wram_words
          · refine ⟨⟨a+5, next, rfl, htailW, ?_,
              fun e' he' => hinput e' (List.mem_cons_of_mem e he'), hw⟩, hzeroW, ?_⟩
            · simp only [List.length_cons] at hend; omega
            · change next+5*es.length < 2 ^ w
              simp only [List.length_cons] at hspace; omega
          · intro out memR posR hpostR
            obtain ⟨⟨_, _, hframeR, hzeroR, hrecordsR⟩, hout⟩ := hpostR
            change out = next+5*es.length at hout
            change (∀ x < next, memR x = memW x) at hframeR
            change ZeroFrom memR out at hzeroR
            change ListAt memR next (es.flatMap J.positiveInstance.solverEdgeWords) at hrecordsR
            have houtWord : out < 2 ^ w := by simp only [List.length_cons] at hspace; omega
            refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
            · change (heap ≤ out ∧ out ≤ heap+5*(e :: es).length ∧
                (∀ x < heap, memR x = mem x) ∧ ZeroFrom memR out ∧
                ListAt memR heap ((e :: es).flatMap J.positiveInstance.solverEdgeWords)) ∧
                out = heap+5*(e :: es).length
              refine ⟨⟨by omega, by simp only [List.length_cons]; omega, ?_, hzeroR, ?_⟩,
                by simp only [List.length_cons]; omega⟩
              · intro x hx
                exact (hframeR x (by omega)).trans (hframeW x hx)
              · rw [List.flatMap_cons]
                apply listAt_append.mpr
                refine ⟨hrecordW.of_agree_below (h₀ := next) (by change heap+5 ≤ next; omega) hframeR, ?_⟩
                simpa only [Circulation.solverEdgeWords, List.length_cons, List.length_nil,
                  Nat.reduceAdd, hnext] using hrecordsR
            · simp only [positiveInstanceEdgesContract, heapContract, wordFiveContract,
                List.length_cons, argsSize_cons, argsSize_nil, Expr.size_bin, Expr.size_load,
                Expr.size_reg, Expr.size_const]; omega

/-- All source, word, and fresh-output premises hold together for every
selected edge list, including the extra isolated vertex's index. -/
theorem exists_positiveInstanceEdges_pre (J : Circulation) (es : List (Fin J.m)) :
    ∃ w, (∀ x ∈ [0, es.length, J.n, 5*es.length], x < 2 ^ w) ∧
      (positiveInstanceEdgesContract w J es).pre [0, es.length, J.n, 5*es.length]
        (initMem (es.flatMap J.solverEdgeWords)) := by
  let input := es.flatMap J.solverEdgeWords ++ [J.n+10*es.length+10]
  let w := wordSize 1 input
  have hlarge : J.n+10*es.length+10 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_right _ List.mem_cons_self)
  refine ⟨w, ?_, ⟨0, 5*es.length, rfl, listAt_initMem _, by omega, ?_, by omega⟩, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  · intro e he x hx
    exact lt_two_pow_wordSize_of_mem (by decide)
      (List.mem_append_left _ (List.mem_flatMap.mpr ⟨e, he, hx⟩))
  · change ZeroFrom (initMem (es.flatMap J.solverEdgeWords)) (5*es.length)
    simpa only [Circulation.solverEdgeRecords_length] using zeroFrom_initMem (es.flatMap J.solverEdgeWords)
  · change 5*es.length+5*es.length < 2 ^ w
    omega

end MinCostFlow.Scaling.Machine
