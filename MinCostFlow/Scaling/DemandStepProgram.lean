module

public import MinCostFlow.Scaling.DemandScan
public import MinCostFlow.Scaling.SignedTableLayout
public import MinCostFlow.Scaling.SignedCellAddProgram
public import MinCostFlow.Scaling.SignedNegateProgram
import WordRAM.Tactic
import WordRAM.Memory
import WordRAM.Entry

/-!
# Applying one lower-capacity contribution to the demand table

The edge scan in the general-flow reduction of Lemma C.1 of Chen et al.,
arXiv:2203.00671v2, subtracts the lower capacity at the tail and adds it at
the head. The writes are sequential, so a loop cancels its own contribution.
This procedure computes exactly `FlowReduction.demandStep`, using canonical
signed negation and two proved demand-cell additions. It allocates six
scratch words and costs at most 500 steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[tail,head,lowerSign,lowerMagnitude,table,heap]`. -/
def demandStepBody (negate addCell : ℕ) : Stmt :=
  .call 6 negate [.reg 2, .reg 3, .reg 5] ;;
  .call 7 addCell [.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 0)),
    .load (.reg 5), .load (.bin .add (.reg 5) (.const 1)), .reg 6] ;;
  .call 8 addCell [.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 1)),
    .reg 2, .reg 3, .reg 7] ;;
  .ret (.reg 8)

/-- The step, signed negation and its writer, and signed demand-cell addition. -/
def demandStepModule (b : ℕ) : List Stmt :=
  demandStepBody (b + 1) (b + 3) :: signedNegateBody (b + 2) :: wordPairBody ::
    signedCellAddModule (b + 3)

/-- The two arithmetic bounds refer to the actual sequential table values.
All other memory below the heap outside the demand table is preserved. -/
def demandStepContract (w : ℕ) (I : Instance) (hv : I.IsValid)
    (s : Fin I.n → ℤ) (e : Fin I.m) : Contract where
  pre args mem := ∃ table heap,
    args = [(I.edge e).tail, (I.edge e).head,
      if (I.edge e).lower < 0 then 1 else 0, (I.edge e).lower.natAbs, table, heap] ∧
    SignedTableAt mem table s ∧ table + 2 * I.n ≤ heap ∧
    (s ((FlowReduction.shiftedGraph I hv).tail e)).natAbs + (I.edge e).lower.natAbs < 2 ^ w ∧
    ((Function.update s ((FlowReduction.shiftedGraph I hv).tail e)
      (s ((FlowReduction.shiftedGraph I hv).tail e) - (I.edge e).lower))
        ((FlowReduction.shiftedGraph I hv).head e)).natAbs + (I.edge e).lower.natAbs < 2 ^ w ∧
    ZeroFrom mem heap ∧ heap + 6 < 2 ^ w
  post args mem out mem' := out = heapArg args + 6 ∧
    SignedTableAt mem' (args.getD 4 0) (FlowReduction.demandStep I hv s e) ∧
    ZeroFrom mem' out ∧
    ∀ x < heapArg args, x < args.getD 4 0 ∨ args.getD 4 0 + 2 * I.n ≤ x → mem' x = mem x
  cost _ _ := 500

/-- All procedures of one demand step have no random instructions. -/
theorem demandStepModule_noRand (b : ℕ) :
    ∀ body ∈ demandStepModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [demandStepBody, Stmt.NoRand, and_self]
  · rcases List.mem_cons.mp hb with rfl | hb
    · simp only [signedNegateBody, Stmt.NoRand, and_self]
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact wordPairBody_noRand
      · exact signedCellAddModule_noRand _ body hb

/-- One machine step computes the model's two sequential demand writes,
including loops, with the stated scratch space and constant cost. -/
theorem demandStep_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (demandStepModule b)) (I : Instance) (hv : I.IsValid)
    (s : Fin I.n → ℤ) (e : Fin I.m) :
    MeetsContract w p b (demandStepContract w I hv s e) := by
  have hneg : p.HasAt (b + 1) (signedNegateModule (b + 1)) := by
    intro i hi
    have hi' : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    rcases hi' with rfl | rfl
    · simpa only [demandStepModule, signedNegateModule, List.getElem_cons_succ,
        List.getElem_cons_zero, Nat.add_zero, Nat.add_assoc] using hp 1 (by simp [demandStepModule])
    · simpa only [demandStepModule, signedNegateModule, List.getElem_cons_succ,
        List.getElem_cons_zero, Nat.add_assoc] using hp 2 (by simp [demandStepModule])
  have hadd : p.HasAt (b + 3) (signedCellAddModule (b + 3)) := by
    intro i hi
    have h := hp (i + 1 + 1 + 1) (by simp only [demandStepModule, List.length_cons]; omega)
    have hi' : b + (i + 1 + 1 + 1) = b + 3 + i := by omega
    rw [hi'] at h
    simpa only [demandStepModule, List.getElem_cons_succ] using h
  let tail := (FlowReduction.shiftedGraph I hv).tail e
  let head := (FlowReduction.shiftedGraph I hv).head e
  let lower := (I.edge e).lower
  let s' := Function.update s tail (s tail + -lower)
  have hkN := signedNegate_meetsContract (w := w) hneg lower
  have hkT := signedCellAdd_meetsContract (w := w) hadd (s tail) (-lower)
  have hkH := signedCellAdd_meetsContract (w := w) hadd (s' head) lower
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨table, heap, rfl, htable, htableend, htailbound, hheadbound, hzero, hspace⟩ := hpre
  change (s tail).natAbs + lower.natAbs < 2 ^ w at htailbound
  change ((Function.update s tail (s tail - lower)) head).natAbs + lower.natAbs < 2 ^ w at hheadbound
  rw [sub_eq_add_neg] at hheadbound
  change (s' head).natAbs + lower.natAbs < 2 ^ w at hheadbound
  have ht : tail.val < I.n := tail.isLt
  have hh : head.val < I.n := head.isLt
  have htailval : (I.edge e).tail = tail.val := rfl
  have hheadval : (I.edge e).head = head.val := rfl
  have htailcell : table + 2 * tail.val + 2 ≤ heap := by omega
  have hheadcell : table + 2 * head.val + 2 ≤ heap := by omega
  have htailaddr : table + 2 * tail.val < 2 ^ w := by omega
  have hheadaddr : table + 2 * head.val < 2 ^ w := by omega
  have htwotail : 2 * tail.val < 2 ^ w := by omega
  have htwohead : 2 * head.val < 2 ^ w := by omega
  have hheap : heap < 2 ^ w := by omega
  have hheap1 : heap + 1 < 2 ^ w := by omega
  have hheap2 : heap + 2 < 2 ^ w := by omega
  have htwo : 2 < 2 ^ w := by omega
  have hsign : (if lower < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hmag : lower.natAbs < 2 ^ w := by omega
  have hnegsign : (if -lower < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hnegmag : (-lower).natAbs < 2 ^ w := by simpa only [Int.natAbs_neg] using hmag
  apply runs_start_le
  unfold demandStepBody
  refine runs_seq_call_le hkN
    (vs := [if lower < 0 then 1 else 0, lower.natAbs, heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨heap, rfl⟩, hzero, hheap2⟩
  · intro heapN memN posN hpostN
    obtain ⟨⟨_, _, hframeN, hzeroN, hnegative⟩, hptrN⟩ := hpostN
    change heapN = heap + 2 at hptrN
    change (∀ x < heap, memN x = mem x) at hframeN
    change ZeroFrom memN heapN at hzeroN
    change ListAt memN heap (encodeInt (-lower)) at hnegative
    have htableN := htable.of_agree_below htableend hframeN
    have hns : memN heap = if -lower < 0 then 1 else 0 := by
      simpa only [encodeInt, List.getElem_cons_zero, Nat.add_zero] using
        hnegative 0 (by change 0 < 2; decide)
    have hnm : memN (heap + 1) = (-lower).natAbs := by
      simpa only [encodeInt, List.getElem_cons_succ, List.getElem_cons_zero] using
        hnegative 1 (by change 1 < 2; decide)
    have hheapN : heapN < 2 ^ w := by omega
    refine runs_seq_call_le hkT
      (vs := [table + 2 * tail.val, if -lower < 0 then 1 else 0, (-lower).natAbs, heapN])
      ?_ ?_ ?_ ?_
    · rw [← htailval]
      eval_expr
    · wram_words
    · exact ⟨table + 2 * tail.val, heapN, rfl, htableN tail, by omega,
        by simpa only [Int.natAbs_neg] using htailbound, hzeroN, by omega⟩
    · intro heapT memT posT hpostT
      obtain ⟨hptrT, hcellT, hzeroT, hframeT⟩ := hpostT
      change heapT = heapN + 2 at hptrT
      change ListAt memT (table + 2 * tail.val) (encodeInt (s tail + -lower)) at hcellT
      change (∀ x < heapN, x ≠ table + 2 * tail.val → x ≠ table + 2 * tail.val + 1 →
        memT x = memN x) at hframeT
      have htableT : SignedTableAt memT table s' :=
        htableN.update tail _ (by omega : table + 2 * I.n ≤ heapN) hcellT hframeT
      have hheapT : heapT < 2 ^ w := by omega
      refine runs_seq_call_le hkH
        (vs := [table + 2 * head.val, if lower < 0 then 1 else 0, lower.natAbs, heapT])
        ?_ ?_ ?_ ?_
      · rw [← hheadval]
        eval_expr
      · wram_words
      · exact ⟨table + 2 * head.val, heapT, rfl, htableT head, by omega,
          hheadbound, hzeroT, by omega⟩
      · intro out memH posH hpostH
        obtain ⟨hout, hcellH, hzeroH, hframeH⟩ := hpostH
        change out = heapT + 2 at hout
        change ListAt memH (table + 2 * head.val) (encodeInt (s' head + lower)) at hcellH
        change (∀ x < heapT, x ≠ table + 2 * head.val → x ≠ table + 2 * head.val + 1 →
          memH x = memT x) at hframeH
        have htableH := htableT.update head _ (by omega : table + 2 * I.n ≤ heapT) hcellH hframeH
        have houtword : out < 2 ^ w := by omega
        refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
        · change out = heap + 6 ∧
            SignedTableAt memH table (FlowReduction.demandStep I hv s e) ∧ ZeroFrom memH out ∧
            ∀ x < heap, x < table ∨ table + 2 * I.n ≤ x → memH x = mem x
          refine ⟨by omega, ?_, hzeroH, ?_⟩
          · simpa only [FlowReduction.demandStep, sub_eq_add_neg] using htableH
          · intro x hx hxout
            have hnet : x ≠ table + 2 * tail.val := by rcases hxout with h | h <;> omega
            have hnet' : x ≠ table + 2 * tail.val + 1 := by rcases hxout with h | h <;> omega
            have hneh : x ≠ table + 2 * head.val := by rcases hxout with h | h <;> omega
            have hneh' : x ≠ table + 2 * head.val + 1 := by rcases hxout with h | h <;> omega
            exact (hframeH x (by omega) hneh hneh').trans
              ((hframeT x (by omega) hnet hnet').trans (hframeN x hx))
        · simp only [demandStepContract, signedNegateContract, heapContract,
            signedCellAddContract, argsSize_cons, argsSize_nil, Expr.size_bin,
            Expr.size_load, Expr.size_reg, Expr.size_const]
          omega

/-- For every input edge and signed demand vector, the two sequential
arithmetic bounds, representation, and scratch premises can hold together. -/
theorem exists_demandStep_pre (I : Instance) (hv : I.IsValid)
    (s : Fin I.n → ℤ) (e : Fin I.m) :
    ∃ w mem, (∀ x ∈ [(I.edge e).tail, (I.edge e).head,
        if (I.edge e).lower < 0 then 1 else 0, (I.edge e).lower.natAbs, 0, 2 * I.n],
      x < 2 ^ w) ∧
      (demandStepContract w I hv s e).pre
        [(I.edge e).tail, (I.edge e).head, if (I.edge e).lower < 0 then 1 else 0,
          (I.edge e).lower.natAbs, 0, 2 * I.n] mem := by
  let tail := (FlowReduction.shiftedGraph I hv).tail e
  let head := (FlowReduction.shiftedGraph I hv).head e
  let lower := (I.edge e).lower
  let input := [(s tail).natAbs + lower.natAbs,
    ((Function.update s tail (s tail - lower)) head).natAbs + lower.natAbs,
    2 * I.n + 10]
  let w := wordSize 1 input
  have ht : tail.val < I.n := tail.isLt
  have hh : head.val < I.n := head.isLt
  have htail : (s tail).natAbs + lower.natAbs < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_cons_self)
  have hhead : ((Function.update s tail (s tail - lower)) head).natAbs + lower.natAbs < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_cons_of_mem _ (List.mem_cons_self))
  have hlarge : 2 * I.n + 10 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
  obtain ⟨mem, hat, hzero⟩ := exists_signedTableAt s
  refine ⟨w, mem, ?_, 0, 2 * I.n, rfl, hat, by omega, htail, hhead, hzero, by omega⟩
  intro x hx
  change x ∈ [tail.val, head.val, if lower < 0 then 1 else 0, lower.natAbs, 0, 2 * I.n] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · split <;> omega
  · omega
  · omega
  · omega

end MinCostFlow.Scaling.Machine
