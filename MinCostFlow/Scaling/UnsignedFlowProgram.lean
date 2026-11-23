module

public import MinCostFlow.Scaling.WordPairProgram
public import MinCostFlow.Scaling.SignedTableLayout
import WordRAM.Tactic
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# Converting the solver output to signed flow pairs

The circulation solver returns one unsigned word per edge because feasible
circulation values are nonnegative. The outer reductions use the statement's
signed pairs. This loop prefixes each magnitude by a zero sign. It preserves
the original array, allocates exactly two words per value, and costs at most
`100*count+20` machine steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[source,count,heap]`. -/
def unsignedFlowBody (self pair : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.reg 2))
    (.call 3 pair [.const 0, .load (.reg 0), .reg 2] ;;
     .call 4 self [.bin .add (.reg 0) (.const 1),
       .bin .sub (.reg 1) (.const 1), .reg 3] ;;
     .ret (.reg 4))

/-- The conversion loop and canonical pair writer. -/
def unsignedFlowModule (b : ℕ) : List Stmt := [unsignedFlowBody b (b + 1), wordPairBody]

/-- Source words are nonnegative magnitudes fitting one word. -/
def unsignedFlowContract (w : ℕ) (xs : List ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ src heap, args = [src, xs.length, heap] ∧
      ListAt mem src xs ∧ src + xs.length ≤ heap ∧
      (∀ x ∈ xs, x < 2 ^ w) ∧ 1 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args)
      (xs.flatMap (fun (x : ℕ) => encodeInt (x : ℤ)) ))
    (fun _ _ => 100 * xs.length + 20) (fun _ _ => 2 * xs.length)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 2 * xs.length }

/-- Conversion uses no random instructions. -/
theorem unsignedFlowModule_noRand (b : ℕ) :
    ∀ body ∈ unsignedFlowModule b, body.NoRand := by
  intro body hb
  simp only [unsignedFlowModule, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · simp only [unsignedFlowBody, Stmt.NoRand, and_self]
  · exact wordPairBody_noRand

/-- The loop converts exactly the solver's unsigned array into canonical
signed pairs, with a linear cost and exact heap increment. -/
theorem unsignedFlow_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (unsignedFlowModule b)) (xs : List ℕ) :
    MeetsContract w p b (unsignedFlowContract w xs) := by
  have hpair : p.HasAt (b + 1) wordPairModule := by
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [unsignedFlowModule, wordPairModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [unsignedFlowModule])
  have hkP := wordPair_meetsContract (w := w) hpair
  induction xs with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨src, heap, rfl, _, _, _, hw⟩, hzero, hspace⟩ := hpre
    change ZeroFrom mem heap at hzero
    change heap + 2 * 0 < 2 ^ w at hspace
    have hh : heap < 2 ^ w := by omega
    apply runs_start_le
    unfold unsignedFlowBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change (heap ≤ heap ∧ heap ≤ heap + 2 * 0 ∧
          (∀ a < heap, mem a = mem a) ∧ ZeroFrom mem heap ∧ ListAt mem heap []) ∧
          heap = heap + 2 * 0
        exact ⟨⟨le_rfl, by omega, fun _ _ => rfl, hzero, listAt_nil _ _⟩, by omega⟩
      · simp only [unsignedFlowContract, heapContract, List.length_nil,
          Expr.size_bin, Expr.size_reg, Expr.size_const]; omega
    · simp at hcond
  | cons x xs ih =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨src, heap, rfl, hat, hbefore, hxs, hw⟩, hzero, hspace⟩ := hpre
    change ZeroFrom mem heap at hzero
    change heap + 2 * (x :: xs).length < 2 ^ w at hspace
    obtain ⟨hhead, htail⟩ := listAt_cons.mp hat
    have hx : x < 2 ^ w := hxs x List.mem_cons_self
    have hlen : (x :: xs).length < 2 ^ w := hwords _ (by simp)
    have hh : heap < 2 ^ w := by omega
    have hheap2 : heap + 2 < 2 ^ w := by simp only [List.length_cons] at hspace; omega
    have hsrc1 : src + 1 < 2 ^ w := by simp only [List.length_cons] at hbefore; omega
    apply runs_start_le
    unfold unsignedFlowBody
    wram_step
    · simp at hcond
    · refine runs_seq_call_le hkP (vs := [0, x, heap]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨⟨0, x, heap, rfl⟩, hzero, hheap2⟩
      · intro next memP posP hpostP
        obtain ⟨⟨_, _, hframeP, hzeroP, hpairP⟩, hnext⟩ := hpostP
        change next = heap + 2 at hnext
        change (∀ a < heap, memP a = mem a) at hframeP
        change ZeroFrom memP next at hzeroP
        change ListAt memP heap [0, x] at hpairP
        have htailP : ListAt memP (src + 1) xs := by
          apply htail.of_agree_below (h₀ := heap)
          · simp only [List.length_cons] at hbefore; omega
          · exact hframeP
        have hnextWord : next < 2 ^ w := by omega
        have hlenTail : xs.length < 2 ^ w := by simp only [List.length_cons] at hlen; omega
        refine runs_seq_call_le ih (vs := [src + 1, xs.length, next]) ?_ ?_ ?_ ?_
        · have heq : (x :: xs).length - 1 = xs.length := rfl
          rw [← heq]; eval_expr
        · wram_words
        · refine ⟨⟨src + 1, next, rfl, htailP, ?_,
            fun y hy => hxs y (List.mem_cons_of_mem x hy), hw⟩, hzeroP, ?_⟩
          · simp only [List.length_cons] at hbefore; omega
          · change next + 2 * xs.length < 2 ^ w
            simp only [List.length_cons] at hspace; omega
        · intro out memR posR hpostR
          obtain ⟨⟨_, _, hframeR, hzeroR, hresult⟩, hout⟩ := hpostR
          change out = next + 2 * xs.length at hout
          change (∀ a < next, memR a = memP a) at hframeR
          change ZeroFrom memR out at hzeroR
          change ListAt memR next (xs.flatMap (fun (y : ℕ) => encodeInt (y : ℤ))) at hresult
          have houtWord : out < 2 ^ w := by simp only [List.length_cons] at hspace; omega
          refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
          · change (heap ≤ out ∧ out ≤ heap + 2 * (x :: xs).length ∧
              (∀ a < heap, memR a = mem a) ∧ ZeroFrom memR out ∧
              ListAt memR heap ((x :: xs).flatMap (fun (y : ℕ) => encodeInt (y : ℤ)))) ∧
              out = heap + 2 * (x :: xs).length
            refine ⟨⟨by omega, by simp only [List.length_cons]; omega, ?_, hzeroR, ?_⟩,
              by simp only [List.length_cons]; omega⟩
            · intro a ha
              exact (hframeR a (by omega)).trans (hframeP a ha)
            · rw [List.flatMap_cons]
              apply listAt_append.mpr
              refine ⟨?_, ?_⟩
              · have hcanonical : encodeInt (x : ℤ) = [0, x] := by
                  have hn : ¬ (x : ℤ) < 0 := by omega
                  simp only [encodeInt, hn, ↓reduceIte, Int.natAbs_natCast]
                rw [hcanonical]
                apply hpairP.of_agree_below (h₀ := next)
                · change heap + 2 ≤ next; omega
                · exact hframeR
              · simpa only [encodeInt, List.length_cons, List.length_nil, Nat.reduceAdd, hnext] using hresult
          · simp only [unsignedFlowContract, heapContract, wordPairContract,
              List.length_cons, argsSize_cons, argsSize_nil, Expr.size_bin,
              Expr.size_reg, Expr.size_const, Expr.size_load]; omega

/-- Every unsigned flow array admits all conversion premises together. -/
theorem exists_unsignedFlow_pre (xs : List ℕ) :
    ∃ w, (∀ x ∈ [0, xs.length, xs.length], x < 2 ^ w) ∧
      (unsignedFlowContract w xs).pre [0, xs.length, xs.length] (initMem xs) := by
  let B := xs.foldr max 0
  let w := B + 3 * xs.length + 3
  have hw : B + 3 * xs.length + 3 < 2 ^ w := Nat.lt_two_pow_self
  refine ⟨w, ?_, ⟨0, xs.length, rfl, listAt_initMem _, by omega, ?_, by omega⟩,
    zeroFrom_initMem _, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · intro x hx
    have hb : x ≤ B := Link.elem_le_foldr_max hx
    omega
  · change xs.length + 2 * xs.length < 2 ^ w
    omega

end MinCostFlow.Scaling.Machine
