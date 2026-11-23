module

public import MinCostFlow.Scaling.SolverContract
public import MinCostFlow.Scaling.SolverAdapter
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Erasing solver values on dummy edge slots

The positive-capacity solver adapter restores zero flow on every original
capacity-zero slot. This procedure scans the original records and the
solver's unsigned output in parallel. It writes zero for inactive slots
and copies the solver magnitude otherwise. It allocates one word per edge,
preserves both source arrays, and costs at most `100*count+20` steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[records,flow,count,heap]`. -/
def eraseZeroFlowBody (self : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.reg 3))
    (.store (.reg 3) (.bin .mul (.load (.reg 1))
       (.bin .sub (.const 1) (.bin .eq (.load (.bin .add (.reg 0) (.const 2))) (.const 0)))) ;;
     .call 4 self [.bin .add (.reg 0) (.const 5), .bin .add (.reg 1) (.const 1),
       .bin .sub (.reg 2) (.const 1), .bin .add (.reg 3) (.const 1)] ;;
     .ret (.reg 4))

/-- Erasing dummy flows uses a single recursive procedure. -/
def eraseZeroFlowModule (b : ℕ) : List Stmt := [eraseZeroFlowBody b]

/-- Unsigned solver values and the corresponding old records lie below the
fresh output. The same edge list indexes both arrays. -/
def eraseZeroFlowContract (w : ℕ) (J : Circulation) (f : Fin J.m → ℕ)
    (es : List (Fin J.m)) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a flow heap, args = [a, flow, es.length, heap] ∧
      ListAt mem a (es.flatMap J.solverEdgeWords) ∧ ListAt mem flow (es.map f) ∧
      a+5*es.length ≤ heap ∧ flow+es.length ≤ heap ∧
      (∀ e ∈ es, J.capacity e < 2 ^ w ∧ f e < 2 ^ w) ∧ 8 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args)
      (es.map (fun e => if J.capacity e = 0 then 0 else f e)))
    (fun _ _ => 100*es.length+20) (fun _ _ => es.length)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧ out = heapArg args+es.length }

/-- Erasing dummy flows uses no random instructions. -/
theorem eraseZeroFlowBody_noRand (b : ℕ) : (eraseZeroFlowBody b).NoRand := by
  simp only [eraseZeroFlowBody, Stmt.NoRand, and_self]

/-- The machine computes the zero-slot erasure of the supplied unsigned
solver vector with linear cost and exact fresh allocation. -/
theorem eraseZeroFlow_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (eraseZeroFlowModule b)) (J : Circulation) (f : Fin J.m → ℕ)
    (es : List (Fin J.m)) : MeetsContract w p b (eraseZeroFlowContract w J f es) := by
  induction es with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a, flow, heap, rfl, _, _, _, _, _, hw⟩, hzero, hspace⟩ := hpre
    change ZeroFrom mem heap at hzero
    change heap+0 < 2 ^ w at hspace
    have hh : heap < 2 ^ w := by omega
    have hone : 1 < 2 ^ w := by omega
    apply runs_start_le
    unfold eraseZeroFlowBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change (heap ≤ heap ∧ heap ≤ heap+0 ∧ (∀ x < heap, mem x = mem x) ∧
          ZeroFrom mem heap ∧ ListAt mem heap []) ∧ heap = heap+0
        exact ⟨⟨le_rfl, by omega, fun _ _ => rfl, hzero, listAt_nil _ _⟩, by omega⟩
      · simp only [eraseZeroFlowContract, heapContract, List.length_nil,
          Expr.size_bin, Expr.size_reg, Expr.size_const]; omega
    · simp at hcond
  | cons e es ih =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a, flow, heap, rfl, hat, hflow, haend, hfend, hinput, hw⟩, hzero, hspace⟩ := hpre
    change ZeroFrom mem heap at hzero
    change heap+(e :: es).length < 2 ^ w at hspace
    obtain ⟨hhead, htail⟩ := listAt_append.mp hat
    change ListAt mem a (J.solverEdgeWords e) at hhead
    change ListAt mem (a+5) (es.flatMap J.solverEdgeWords) at htail
    obtain ⟨hvalue, hflowTail⟩ := listAt_cons.mp hflow
    change mem flow = f e at hvalue
    have hcapacity : mem (a+2) = J.capacity e := by
      simpa only [Circulation.solverEdgeWords, List.getElem_cons_succ, List.getElem_cons_zero] using
        hhead 2 (by change 2 < 5; decide)
    obtain ⟨hcapWord, hflowWord⟩ := hinput e List.mem_cons_self
    let value := if J.capacity e = 0 then 0 else f e
    have hselect : value = f e*(1-(if J.capacity e = 0 then 1 else 0)) := by
      dsimp [value]; split <;> simp
    have hvalueWord : value < 2 ^ w := by dsimp [value]; split <;> omega
    have hflag : (if J.capacity e = 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
    have hinverse : 1-(if J.capacity e = 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
    have hproduct : f e*(1-(if J.capacity e = 0 then 1 else 0)) < 2 ^ w := by rw [← hselect]; exact hvalueWord
    have hlen : (e :: es).length < 2 ^ w := hwords _ (by simp)
    have ha : a < 2 ^ w := by simp only [List.length_cons] at haend; omega
    have ha2 : a+2 < 2 ^ w := by simp only [List.length_cons] at haend; omega
    have ha5 : a+5 < 2 ^ w := by simp only [List.length_cons] at haend; omega
    have hf : flow < 2 ^ w := by simp only [List.length_cons] at hfend; omega
    have hf1 : flow+1 < 2 ^ w := by simp only [List.length_cons] at hfend; omega
    have hh : heap < 2 ^ w := by omega
    have hh1 : heap+1 < 2 ^ w := by simp only [List.length_cons] at hspace; omega
    have hone : 1 < 2 ^ w := by omega
    have htwo : 2 < 2 ^ w := by omega
    have hfive : 5 < 2 ^ w := by omega
    apply runs_start_le
    unfold eraseZeroFlowBody
    wram_step
    · simp at hcond
    · refine runs_seq_store_le (x := heap) (v := value) (by eval_expr) ?_ ?_
      · rw [hselect]; eval_expr
      let memS := Function.update mem heap value
      have hframeS : ∀ x < heap, memS x = mem x := by
        intro x hx
        exact Function.update_of_ne (by omega : x ≠ heap) _ _
      have htailS : ListAt memS (a+5) (es.flatMap J.solverEdgeWords) := by
        apply htail.of_agree_below (h₀ := heap)
        · rw [Circulation.solverEdgeRecords_length]
          simp only [List.length_cons] at haend; omega
        · exact hframeS
      have hflowS : ListAt memS (flow+1) (es.map f) := by
        apply hflowTail.of_agree_below (h₀ := heap)
        · rw [List.length_map]
          simp only [List.length_cons] at hfend; omega
        · exact hframeS
      have hzeroS : ZeroFrom memS (heap+1) := by
        intro x hx
        change Function.update mem heap value x = 0
        rw [Function.update_of_ne (by omega : x ≠ heap)]
        exact hzero x (by omega)
      have hlenTail : es.length < 2 ^ w := by simp only [List.length_cons] at hlen; omega
      refine runs_seq_call_le ih (vs := [a+5, flow+1, es.length, heap+1]) ?_ ?_ ?_ ?_
      · have heq : (e :: es).length-1 = es.length := rfl
        rw [← heq]; eval_expr
      · wram_words
      · refine ⟨⟨a+5, flow+1, heap+1, rfl, htailS, hflowS, ?_, ?_,
          fun e' he' => hinput e' (List.mem_cons_of_mem e he'), hw⟩, hzeroS, ?_⟩
        · simp only [List.length_cons] at haend; omega
        · simp only [List.length_cons] at hfend; omega
        · change heap+1+es.length < 2 ^ w
          simp only [List.length_cons] at hspace; omega
      · intro out memR posR hpostR
        obtain ⟨⟨_, _, hframeR, hzeroR, hresultR⟩, hout⟩ := hpostR
        change out = heap+1+es.length at hout
        change (∀ x < heap+1, memR x = memS x) at hframeR
        change ZeroFrom memR out at hzeroR
        change ListAt memR (heap+1) (es.map (fun e => if J.capacity e = 0 then 0 else f e)) at hresultR
        have houtWord : out < 2 ^ w := by simp only [List.length_cons] at hspace; omega
        refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
        · change (heap ≤ out ∧ out ≤ heap+(e :: es).length ∧
            (∀ x < heap, memR x = mem x) ∧ ZeroFrom memR out ∧
            ListAt memR heap ((e :: es).map (fun e => if J.capacity e = 0 then 0 else f e))) ∧
            out = heap+(e :: es).length
          refine ⟨⟨by omega, by simp only [List.length_cons]; omega, ?_, hzeroR, ?_⟩,
            by simp only [List.length_cons]; omega⟩
          · intro x hx
            exact (hframeR x (by omega)).trans (hframeS x hx)
          · apply listAt_cons.mpr
            exact ⟨(hframeR heap (by omega)).trans (Function.update_self _ _ _), hresultR⟩
        · simp only [eraseZeroFlowContract, heapContract, List.length_cons,
            argsSize_cons, argsSize_nil, Expr.size_bin, Expr.size_load, Expr.size_reg,
            Expr.size_const]; omega

/-- Casting the erased unsigned solver output back to integers gives the
model's exact zero-capacity adapter whenever the solver values are nonnegative. -/
theorem eraseZeroFlow_unsigned_eq (solve : (J : Circulation) → Fin J.m → ℤ)
    (J : Circulation) (hf : ∀ e, 0 ≤ solve J.positiveInstance e) :
    (fun e => ((if J.capacity e = 0 then 0 else (solve J.positiveInstance e).toNat : ℕ) : ℤ)) =
      Circulation.solveWithZeroCapacities solve J := by
  funext e
  by_cases hz : J.capacity e = 0
  · simp only [Circulation.solveWithZeroCapacities, hz, ↓reduceIte, Nat.cast_zero]
  · simp only [Circulation.solveWithZeroCapacities, hz, ↓reduceIte]
    exact Int.toNat_of_nonneg (hf e)

/-- Every unsigned solver array and selected edge list have simultaneous
source, word, and fresh-output premises in a concrete concatenated memory. -/
theorem exists_eraseZeroFlow_pre (J : Circulation) (f : Fin J.m → ℕ)
    (es : List (Fin J.m)) :
    ∃ w, (∀ x ∈ [0, 5*es.length, es.length, 6*es.length], x < 2 ^ w) ∧
      (eraseZeroFlowContract w J f es).pre [0, 5*es.length, es.length, 6*es.length]
        (initMem ((es.flatMap J.solverEdgeWords) ++ es.map f)) := by
  let records := es.flatMap J.solverEdgeWords
  let values := es.map f
  let input := records ++ (values ++ [7*es.length+10])
  let w := wordSize 1 input
  have hlarge : 7*es.length+10 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide)
      (List.mem_append_right _ (List.mem_append_right _ List.mem_cons_self))
  have hrecordslen : records.length = 5*es.length := J.solverEdgeRecords_length es
  have hvalueslen : values.length = es.length := List.length_map ..
  have hstored := listAt_append.mp (listAt_initMem (records ++ values))
  have hflow : ListAt (initMem (records ++ values)) (5*es.length) values := by
    simpa only [hrecordslen, Nat.zero_add] using hstored.2
  have hzero : ZeroFrom (initMem (records ++ values)) (6*es.length) := by
    have h := zeroFrom_initMem (records ++ values)
    simpa only [List.length_append, hrecordslen, hvalueslen,
      show 5*es.length+es.length = 6*es.length by omega] using h
  refine ⟨w, ?_, ⟨0, 5*es.length, 6*es.length, rfl, hstored.1, hflow,
    by omega, by omega, ?_, by omega⟩, hzero, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  · intro e he
    constructor
    · exact lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨e, he, by simp [Circulation.solverEdgeWords]⟩))
    · exact lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_right _
        (List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩)))
  · change 6*es.length+es.length < 2 ^ w
    omega

end MinCostFlow.Scaling.Machine
