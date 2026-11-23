module

public import MinCostFlow.Scaling.PositiveScanProgram
public import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory
import WordRAM.Entry

/-!
# Removing zero-capacity circulation slots on the machine

The reductions of Lemma C.1 of Chen et al., arXiv:2203.00671v2, pass only
positive-capacity edges to the scaling solver. This procedure reserves a
compacted graph block and an original-index block, runs stable compaction,
and writes the new header. The graph is exactly `withoutZeroEdges` and its
index list is exactly `positiveEdges`. Reserving maximum-size blocks keeps
both writes linear, without another pass or overlapping scratch memory.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[inputAddress,heap]`. -/
def positivePruneBody (scan : ℕ) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 4 (.bin .add (.reg 1) (.const 2)) ;;
  .assign 5 (.bin .add (.reg 4) (.bin .mul (.const 5) (.reg 3))) ;;
  .call 6 scan [.bin .add (.reg 0) (.const 2), .reg 3, .const 0, .reg 4, .reg 5] ;;
  .store (.reg 1) (.reg 2) ;;
  .store (.bin .add (.reg 1) (.const 1)) (.reg 6) ;;
  .ret (.bin .add (.reg 5) (.reg 3))

/-- Pruning entry, compaction scan, and in-place record writer. -/
def positivePruneModule (b : ℕ) : List Stmt :=
  positivePruneBody (b + 1) :: positiveScanModule (b + 1)

/-- The graph starts at the old heap. Original retained indices start at
`heap+2+5*m`. Both arrays reserve space for the original number of slots. -/
def positivePruneContract (w : ℕ) (J : Circulation) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a heap, args = [a, heap] ∧ ListAt mem a J.solverWords ∧
      a + J.solverWords.length ≤ heap ∧ (∀ x ∈ J.solverWords, x < 2 ^ w) ∧ 8 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args) J.withoutZeroEdges.solverWords ∧
      ListAt mem' (heapArg args + 2 + 5 * J.m) (J.positiveEdges.map Fin.val))
    (fun _ _ => 300 * J.m + 200) (fun _ _ => 2 + 6 * J.m)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 2 + 6 * J.m }

/-- The complete pruning module uses no random instructions. -/
theorem positivePruneModule_noRand (b : ℕ) :
    ∀ body ∈ positivePruneModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [positivePruneBody, Stmt.NoRand, and_self]
  · exact positiveScanModule_noRand _ body hb

/-- Pruning computes the exact model graph and retained-index list, with
linear cost, exact reserved space, and the standard heap frame. -/
theorem positivePrune_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (positivePruneModule b)) (J : Circulation) :
    MeetsContract w p b (positivePruneContract w J) := by
  have hk := positiveScan_meetsContract (w := w) (hasAt_tail hp) J (List.finRange J.m) 0
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, heap, rfl, hat, hend, hinput, hw⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + (2 + 6 * J.m) < 2 ^ w at hspace
  have hsize := J.solverWords_length
  have hN : mem a = J.n := by
    simpa only [Circulation.solverWords, List.getElem_cons_zero, Nat.add_zero] using hat 0 (by rw [hsize]; omega)
  have hM : mem (a + 1) = J.m := by
    simpa only [Circulation.solverWords, List.getElem_cons_succ, List.getElem_cons_zero] using hat 1 (by rw [hsize]; omega)
  have hedge : ListAt mem (a + 2) ((List.finRange J.m).flatMap J.solverEdgeWords) := by
    have hh := (listAt_cons.mp (listAt_cons.mp hat).2).2
    simpa only [Nat.add_assoc] using hh
  have ha : a < 2 ^ w := by omega
  have ha1 : a + 1 < 2 ^ w := by omega
  have ha2 : a + 2 < 2 ^ w := by omega
  have hn : J.n < 2 ^ w := hinput _ (List.mem_cons_self)
  have hm : J.m < 2 ^ w := by omega
  have hheap : heap < 2 ^ w := by omega
  have hheap1 : heap + 1 < 2 ^ w := by omega
  have hrecords : heap + 2 < 2 ^ w := by omega
  have hindices : heap + 2 + 5 * J.m < 2 ^ w := by omega
  have h5m : 5 * J.m < 2 ^ w := by omega
  have houtword : heap + 2 + 6 * J.m < 2 ^ w := by omega
  apply runs_start_le
  unfold positivePruneBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heap + 2) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heap + 2 + 5 * J.m) (by eval_expr) ?_
  refine runs_seq_call_le hk
    (vs := [a + 2, J.m, 0, heap + 2, heap + 2 + 5 * J.m]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · refine ⟨a + 2, heap + 2, heap + 2 + 5 * J.m, ?_, hedge, ?_, ?_, ?_, ?_, ?_, ?_, hw⟩
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
      exact hinput x (J.solverEdgeWord_mem e hx)
  · intro count memS posS hpostS
    obtain ⟨hcount, hrecordS, hindexS, hframeS⟩ := hpostS
    change count = J.positiveEdges.length at hcount
    change ListAt memS (heap + 2) (J.positiveEdges.flatMap J.solverEdgeWords) at hrecordS
    change ListAt memS (heap + 2 + 5 * J.m) (J.positiveEdges.map Fin.val) at hindexS
    change (∀ x, (x < heap + 2 ∨ heap + 2 + 5 * (List.finRange J.m).length ≤ x) →
      (x < heap + 2 + 5 * J.m ∨ heap + 2 + 5 * J.m + (List.finRange J.m).length ≤ x) →
      memS x = mem x) at hframeS
    simp only [List.length_finRange] at hframeS
    have hcountword : count < 2 ^ w := lt_of_le_of_lt (hcount ▸ J.positiveEdges_length_le) hm
    have hzeroS : ZeroFrom memS (heap + 2 + 6 * J.m) := by
      intro x hx
      exact (hframeS x (Or.inr (by omega)) (Or.inr (by omega))).trans (hzero x (by omega))
    refine runs_seq_store_le (by eval_expr) (v := J.n) (by eval_expr) ?_
    refine runs_seq_store_le (by eval_expr) (v := count) (by eval_expr) ?_
    refine runs_ret_le (v := heap + 2 + 6 * J.m) (by
      conv_rhs => rw [show heap + 2 + 6 * J.m = (heap + 2 + 5 * J.m) + J.m by omega]
      eval_expr) ?_ ?_
    · let memH := Function.update (Function.update memS heap J.n) (heap + 1) count
      change (heap ≤ heap + 2 + 6 * J.m ∧
          heap + 2 + 6 * J.m ≤ heap + (2 + 6 * J.m) ∧
          (∀ x < heap, memH x = mem x) ∧ ZeroFrom memH (heap + 2 + 6 * J.m) ∧
          (ListAt memH heap J.withoutZeroEdges.solverWords ∧
            ListAt memH (heap + 2 + 5 * J.m) (J.positiveEdges.map Fin.val))) ∧
          heap + 2 + 6 * J.m = heap + 2 + 6 * J.m
      refine ⟨⟨by omega, by omega, ?_, ?_, ?_⟩, rfl⟩
      · intro x hx
        change Function.update (Function.update memS heap J.n) (heap + 1) count x = mem x
        rw [Function.update_of_ne (by omega : x ≠ heap + 1), Function.update_of_ne (by omega : x ≠ heap)]
        exact hframeS x (Or.inl (by omega)) (Or.inl (by omega))
      · intro x hx
        change Function.update (Function.update memS heap J.n) (heap + 1) count x = 0
        rw [Function.update_of_ne (by omega : x ≠ heap + 1), Function.update_of_ne (by omega : x ≠ heap)]
        exact hzeroS x hx
      · have hrecordH : ListAt memH (heap + 2) (J.positiveEdges.flatMap J.solverEdgeWords) :=
          (hrecordS.update_lt (by omega : heap < heap + 2)).update_lt (by omega : heap + 1 < heap + 2)
        have hindexH : ListAt memH (heap + 2 + 5 * J.m) (J.positiveEdges.map Fin.val) :=
          (hindexS.update_lt (by omega : heap < heap + 2 + 5 * J.m)).update_lt
            (by omega : heap + 1 < heap + 2 + 5 * J.m)
        refine ⟨?_, hindexH⟩
        rw [withoutZeroEdges_solverWords, ← hcount]
        apply (listAt_append (l₁ := [J.n, count])).mpr
        refine ⟨?_, hrecordH⟩
        intro i hi
        have hi' : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
        rcases hi' with rfl | rfl <;>
          simp only [memH, Nat.add_zero, Function.update_self,
            Function.update_of_ne (by omega : heap ≠ heap + 1),
            List.getElem_cons_zero, List.getElem_cons_succ]
    · simp only [positivePruneContract, heapContract, positiveScanContract, List.length_finRange,
        argsSize_cons, argsSize_nil, Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
      omega

/-- The pruning constructor uses three procedure slots. -/
theorem positivePruneModule_length (b : ℕ) : (positivePruneModule b).length = 3 := rfl

/-- The pruning contract's layout, arithmetic, and fresh-memory premises
hold together on its canonical input at multiplier two. -/
theorem positivePrune_pre_wordSize (J : Circulation) :
    (∀ x ∈ [0, J.solverWords.length], x < 2 ^ wordSize 2 J.solverWords) ∧
      (positivePruneContract (wordSize 2 J.solverWords) J).pre
        [0, J.solverWords.length] (initMem J.solverWords) := by
  obtain ⟨_, hpre⟩ := positiveScan_pre_canonical J
  obtain ⟨a, records, indices, hargs, _, _, _, hindices, _, _, _, hw⟩ := hpre
  have hi : indices = J.solverWords.length + 2 + 5 * J.m := by
    have hh := congrArg (fun xs : List ℕ => xs.getD 4 0) hargs
    simpa only [List.getD_cons_succ, List.getD_cons_zero] using hh.symm
  rw [hi, List.length_finRange] at hindices
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> omega
  · refine ⟨⟨0, J.solverWords.length, rfl, listAt_initMem _, by omega,
      (fun x hx => lt_two_pow_wordSize_of_mem (by decide) hx), hw⟩,
      zeroFrom_initMem _, ?_⟩
    change J.solverWords.length + (2 + 6 * J.m) < 2 ^ wordSize 2 J.solverWords
    omega

end MinCostFlow.Scaling.Machine
