module

public import MinCostFlow.Scaling.DemandArcsLayout
public import MinCostFlow.Scaling.SignedPartProgram
public import MinCostFlow.Scaling.WordFiveProgram
public import MinCostFlow.Scaling.InputLayout
import WordRAM.Tactic
import WordRAM.Memory
import WordRAM.Entry

/-!
# Writing an artificial demand-arc block

The feasibility reduction of Lemma C.1 of Chen et al., arXiv:2203.00671v2,
writes one artificial arc per vertex in each direction. This procedure scans
a canonical signed demand block and writes exactly `demandArcRecords`.
The direction is fixed by its procedure body. Selecting the unsigned part
and writing each record use proved constant-cost procedures. The scan costs
at most `250*vertexCount+20` and allocates exactly five words per vertex.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[demands,vertexCount,firstVertex,root,heap]`. -/
def demandArcsBody (negative : Bool) (self part writer : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.reg 4))
    (.call 5 part [.load (.reg 0), .load (.bin .add (.reg 0) (.const 1))] ;;
    .call 6 writer [if negative then .reg 2 else .reg 3,
      if negative then .reg 3 else .reg 2, .reg 5, .const 1, .const 1, .reg 4] ;;
    .call 7 self [.bin .add (.reg 0) (.const 2), .bin .sub (.reg 1) (.const 1),
      .bin .add (.reg 2) (.const 1), .reg 3, .reg 6] ;;
    .ret (.reg 7))

/-- One directed arc scan, unsigned-part selection, and edge-record writing. -/
def demandArcsModule (negative : Bool) (b : ℕ) : List Stmt :=
  [demandArcsBody negative b (b + 1) (b + 2), signedPartBody negative, wordFiveBody]

/-- The stored canonical demand block is read without modification, and
its artificial edge records are written at the old heap. -/
def demandArcsContract (w : ℕ) (negative : Bool) (root vertex : ℕ) (zs : List ℤ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a heap, args = [a, zs.length, vertex, root, heap] ∧
      ListAt mem a (zs.flatMap encodeInt) ∧ a + 2 * zs.length ≤ heap ∧
      root + vertex + zs.length + 2 < 2 ^ w ∧
      (∀ z ∈ zs, z.natAbs < 2 ^ w) ∧ 8 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args) (demandArcRecords root negative vertex zs))
    (fun _ _ => 250 * zs.length + 20) (fun _ _ => 5 * zs.length)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 5 * zs.length }

/-- Artificial-arc generation and all helpers have no random instructions. -/
theorem demandArcsModule_noRand (negative : Bool) (b : ℕ) :
    ∀ body ∈ demandArcsModule negative b, body.NoRand := by
  simp only [demandArcsModule, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨by simp only [demandArcsBody, Stmt.NoRand, and_self],
    signedPartBody_noRand _, wordFiveBody_noRand⟩

private theorem reg_ite_size (negative : Bool) (a b : ℕ) :
    (if negative then Expr.reg a else Expr.reg b).size = 1 := by
  cases negative <;> rfl

/-- The machine writes precisely the model's artificial arc block, in
vertex order, with linear cost and exact heap allocation. -/
theorem demandArcs_meetsContract {w b : ℕ} {p : Program} (negative : Bool)
    (hp : p.HasAt b (demandArcsModule negative b)) (root vertex : ℕ) (zs : List ℤ) :
    MeetsContract w p b (demandArcsContract w negative root vertex zs) := by
  have hpart : p.HasAt (b + 1) (signedPartModule negative) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [demandArcsModule, signedPartModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [demandArcsModule])
  have hwriter : p.HasAt (b + 2) wordFiveModule := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [demandArcsModule, wordFiveModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 2 (by simp [demandArcsModule])
  have hkW := wordFive_meetsContract (w := w) hwriter
  induction zs generalizing vertex with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a, heap, rfl, _, _, _, _, hw⟩, hzero, hspace⟩ := hpre
    change ZeroFrom mem heap at hzero
    change heap + 0 < 2 ^ w at hspace
    have hh : heap < 2 ^ w := by omega
    have hone : 1 < 2 ^ w := by omega
    apply runs_start_le
    unfold demandArcsBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change (heap ≤ heap ∧ heap ≤ heap + 0 ∧ (∀ x < heap, mem x = mem x) ∧
          ZeroFrom mem heap ∧ ListAt mem heap []) ∧ heap = heap + 0
        exact ⟨⟨le_rfl, by omega, fun _ _ => rfl, hzero, listAt_nil _ _⟩, by omega⟩
      · simp only [demandArcsContract, heapContract, List.length_nil,
          Expr.size_bin, Expr.size_reg, Expr.size_const]
        omega
    · simp at hcond
  | cons z zs ih =>
    have hkP := signedPart_meetsContract (w := w) negative hpart z
    have hkR := ih (vertex + 1)
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a, heap, rfl, hat, hend, hvertices, hmags, hw⟩, hzero, hspace⟩ := hpre
    change ZeroFrom mem heap at hzero
    change heap + 5 * (z :: zs).length < 2 ^ w at hspace
    obtain ⟨hhead, htail⟩ := listAt_append.mp hat
    change ListAt mem a (encodeInt z) at hhead
    change ListAt mem (a + 2) (zs.flatMap encodeInt) at htail
    have hsign : mem a = if z < 0 then 1 else 0 := by
      simpa only [encodeInt, List.getElem_cons_zero, Nat.add_zero] using hhead 0 (by change 0 < 2; decide)
    have hmag : mem (a + 1) = z.natAbs := by
      simpa only [encodeInt, List.getElem_cons_succ, List.getElem_cons_zero] using hhead 1 (by change 1 < 2; decide)
    have hzword := hmags z (List.mem_cons_self)
    have hsignword : (if z < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
    have hroot : root < 2 ^ w := by omega
    have hvertex : vertex < 2 ^ w := by omega
    have hvertex1 : vertex + 1 < 2 ^ w := by omega
    have hheap5 : heap + 5 < 2 ^ w := by simp only [List.length_cons, Nat.mul_succ] at hspace; omega
    have hheap : heap < 2 ^ w := by omega
    have ha : a < 2 ^ w := by omega
    have ha1 : a + 1 < 2 ^ w := by simp only [List.length_cons, Nat.mul_succ] at hend; omega
    have ha2 : a + 2 < 2 ^ w := by simp only [List.length_cons, Nat.mul_succ] at hend; omega
    have hlength : (z :: zs).length = zs.length + 1 := rfl
    have hlen : (z :: zs).length < 2 ^ w := by omega
    have hone : 1 < 2 ^ w := by omega
    have hpartword : (if negative then (-z).toNat else z.toNat) < 2 ^ w := by
      have hbound : (if negative then (-z).toNat else z.toNat) ≤ z.natAbs := by cases negative <;> dsimp <;> omega
      exact lt_of_le_of_lt hbound hzword
    apply runs_start_le
    unfold demandArcsBody
    wram_step
    refine runs_seq_call_le hkP (vs := [if z < 0 then 1 else 0, z.natAbs])
      (by eval_expr) ?_ ⟨rfl, hone⟩ ?_
    · wram_words
    · intro capacity memP posP hpostP
      obtain ⟨hmemP, hcapacity⟩ := hpostP
      change memP = mem at hmemP
      subst memP
      change capacity = if negative then (-z).toNat else z.toNat at hcapacity
      have hcapword : capacity < 2 ^ w := hcapacity ▸ hpartword
      refine runs_seq_call_le hkW
        (vs := [if negative then vertex else root, if negative then root else vertex,
          capacity, 1, 1, heap]) ?_ ?_ ?_ ?_
      · cases negative <;> (try simp only [Bool.false_eq_true, ↓reduceIte]) <;> eval_expr
      · cases negative <;> (try simp only [Bool.false_eq_true, ↓reduceIte]) <;> wram_words
      · exact ⟨⟨_, _, _, _, _, heap, rfl⟩, hzero, hheap5⟩
      · intro nextHeap memW posW hpostW
        obtain ⟨⟨_, _, hframeW, hzeroW, hrecord⟩, hptr⟩ := hpostW
        change nextHeap = heap + 5 at hptr
        change (∀ x < heap, memW x = mem x) at hframeW
        change ZeroFrom memW nextHeap at hzeroW
        change ListAt memW heap [if negative then vertex else root,
          if negative then root else vertex, capacity, 1, 1] at hrecord
        have hrecord' : ListAt memW heap (demandArcWords root negative vertex z) := by
          rw [hcapacity] at hrecord
          cases negative <;> exact hrecord
        have htailW : ListAt memW (a + 2) (zs.flatMap encodeInt) := by
          apply htail.of_agree_below (h₀ := heap)
          · rw [integers_encode_length]
            simp only [List.length_cons, Nat.mul_succ] at hend
            omega
          · exact hframeW
        have hnextword : nextHeap < 2 ^ w := by omega
        refine runs_seq_call_le hkR
          (vs := [a + 2, zs.length, vertex + 1, root, nextHeap]) ?_ ?_ ?_ ?_
        · have heq : (z :: zs).length - 1 = zs.length := rfl
          rw [← heq]; eval_expr
        · wram_words
        · refine ⟨⟨a + 2, nextHeap, rfl, htailW, ?_, ?_,
            (fun z' hz' => hmags z' (List.mem_cons_of_mem z hz')), hw⟩, hzeroW, ?_⟩
          · simp only [List.length_cons, Nat.mul_succ] at hend
            omega
          · simp only [List.length_cons] at hvertices
            omega
          · change nextHeap + 5 * zs.length < 2 ^ w
            simp only [List.length_cons, Nat.mul_succ] at hspace
            omega
        · intro out memR posR hpostR
          obtain ⟨⟨_, _, hframeR, hzeroR, hrecords⟩, hout⟩ := hpostR
          change (∀ x < nextHeap, memR x = memW x) at hframeR
          change ZeroFrom memR out at hzeroR
          change ListAt memR nextHeap (demandArcRecords root negative (vertex + 1) zs) at hrecords
          change out = nextHeap + 5 * zs.length at hout
          have houtword : out < 2 ^ w := by simp only [List.length_cons, Nat.mul_succ] at hspace; omega
          refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
          · change (heap ≤ out ∧ out ≤ heap + 5 * (z :: zs).length ∧
              (∀ x < heap, memR x = mem x) ∧ ZeroFrom memR out ∧
              ListAt memR heap (demandArcRecords root negative vertex (z :: zs))) ∧
              out = heap + 5 * (z :: zs).length
            refine ⟨⟨by omega, by simp only [List.length_cons, Nat.mul_succ]; omega,
              ?_, hzeroR, ?_⟩, by simp only [List.length_cons, Nat.mul_succ]; omega⟩
            · intro x hx
              exact (hframeR x (by omega)).trans (hframeW x hx)
            · rw [demandArcRecords_cons]
              apply listAt_append.mpr
              refine ⟨hrecord'.of_agree_below ?_ hframeR, ?_⟩
              · rw [demandArcWords_length]
                omega
              · simpa only [demandArcWords_length, hptr] using hrecords
          · simp only [demandArcsContract, heapContract, wordFiveContract, signedPartContract,
              List.length_cons, argsSize_cons, argsSize_nil, Expr.size_load, Expr.size_bin,
              Expr.size_reg, Expr.size_const, reg_ite_size]
            omega
/-- Every demand list and root have simultaneous witnesses for the full layout, arithmetic, and
fresh-memory preconditions at one sufficiently large host width. -/
theorem exists_demandArcs_pre (negative : Bool) (root vertex : ℕ) (zs : List ℤ) :
    ∃ w, (∀ x ∈ [0, zs.length, vertex, root, 2 * zs.length], x < 2 ^ w) ∧
      (demandArcsContract w negative root vertex zs).pre
        [0, zs.length, vertex, root, 2 * zs.length] (initMem (zs.flatMap encodeInt)) := by
  let input := [root + vertex + 7 * zs.length + 10] ++ zs.map Int.natAbs
  let w := wordSize 1 input
  have hlarge : root + vertex + 7 * zs.length + 10 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_cons_self)
  refine ⟨w, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega
  · refine ⟨⟨0, 2 * zs.length, rfl, listAt_initMem _, by omega, by omega,
      ?_, by omega⟩, ?_, ?_⟩
    · intro z hz
      exact lt_two_pow_wordSize_of_mem (by decide)
        (List.mem_append_right _ (List.mem_map.mpr ⟨z, hz, rfl⟩))
    · change ZeroFrom (initMem (zs.flatMap encodeInt)) (2 * zs.length)
      simpa only [integers_encode_length] using zeroFrom_initMem (zs.flatMap encodeInt)
    · change 2 * zs.length + 5 * zs.length < 2 ^ w
      omega

end MinCostFlow.Scaling.Machine
