module

public import MinCostFlow.Scaling.ScaledDifferenceProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Computing an integer reduced-cost numerator

The integer cost-scaling representation subtracts a scaled potential
difference from a scaled edge cost. This procedure performs those three
operations using the proved signed arithmetic. It computes
`c*b-(x-y)*d`, allocates eight cells including scratch, and stores the
result in the last pair. It costs at most 700 steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[costSign,costMagnitude,tailSign,tailMagnitude,headSign,
headMagnitude,costFactor,potentialFactor,heap]`. -/
def reducedNumeratorBody (scale difference subtract : ℕ) : Stmt :=
  .call 9 scale [.reg 0, .reg 1, .reg 6, .reg 8] ;;
  .call 10 difference [.reg 2, .reg 3, .reg 4, .reg 5, .reg 7, .reg 9] ;;
  .call 11 subtract [.load (.reg 8), .load (.bin .add (.reg 8) (.const 1)),
    .load (.bin .add (.reg 8) (.const 4)), .load (.bin .add (.reg 8) (.const 5)), .reg 10] ;;
  .ret (.reg 11)

/-- The numerator entry and its three arithmetic modules. -/
def reducedNumeratorModule (b : ℕ) : List Stmt :=
  reducedNumeratorBody (b + 1) (b + 3) (b + 9) ::
    (signedScaleModule (b + 1) ++ scaledDifferenceModule (b + 3) ++ signedSubtractModule (b + 9))

/-- Magnitude budgets for each arithmetic operation, rather than a premise
about the desired output or an invariant of a future state. -/
def reducedNumeratorContract (w : ℕ) (c x y : ℤ) (b d : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ heap, args =
      [if c < 0 then 1 else 0, c.natAbs, if x < 0 then 1 else 0, x.natAbs,
        if y < 0 then 1 else 0, y.natAbs, b, d, heap] ∧
      c.natAbs * b < 2 ^ w ∧ x.natAbs + y.natAbs < 2 ^ w ∧
      (x-y).natAbs * d < 2 ^ w ∧
      (c*(b : ℤ)).natAbs + ((x-y)*(d : ℤ)).natAbs < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args + 6)
      (encodeInt (c*(b : ℤ) - (x-y)*(d : ℤ))))
    (fun _ _ => 700) (fun _ _ => 8)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧ out = heapArg args + 8 }

/-- The numerator and every called arithmetic procedure are deterministic. -/
theorem reducedNumeratorModule_noRand (b : ℕ) :
    ∀ body ∈ reducedNumeratorModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [reducedNumeratorBody, Stmt.NoRand, and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact signedScaleModule_noRand _ body hb
      · exact scaledDifferenceModule_noRand _ body hb
    · exact signedSubtractModule_noRand _ body hb

/-- The composed procedure computes the exact reduced-cost numerator,
with eight allocated cells, a zero tail, and constant cost. -/
theorem reducedNumerator_meetsContract {w base : ℕ} {p : Program}
    (hp : p.HasAt base (reducedNumeratorModule base)) (c x y : ℤ) (b d : ℕ) :
    MeetsContract w p base (reducedNumeratorContract w c x y b d) := by
  have htail := hasAt_tail hp
  have hleft := hasAt_append_left htail
  have hscale := hasAt_append_left hleft
  have hdiff : p.HasAt (base + 3) (scaledDifferenceModule (base + 3)) := by
    have h := hasAt_append_right hleft
    simpa only [signedScaleModule, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_assoc] using h
  have hsub : p.HasAt (base + 9) (signedSubtractModule (base + 9)) := by
    have h := hasAt_append_right htail
    simpa only [List.length_append, signedScaleModule, scaledDifferenceModule,
      signedSubtractModule, signedAddModule, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.add_assoc] using h
  have hkA := signedScale_meetsContract (w := w) hscale c b
  have hkP := scaledDifference_meetsContract (w := w) hdiff x y d
  have hkR := signedSubtract_meetsContract (w := w) hsub (c*(b : ℤ)) ((x-y)*(d : ℤ))
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨heap, rfl, hcost, hxy, hpot, hsum⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + 8 < 2 ^ w at hspace
  have hc : c.natAbs < 2 ^ w := hwords _ (by simp)
  have hx : x.natAbs < 2 ^ w := by omega
  have hy : y.natAbs < 2 ^ w := by omega
  have hb : b < 2 ^ w := hwords _ (by simp)
  have hd : d < 2 ^ w := hwords _ (by simp)
  have hh : heap < 2 ^ w := by omega
  have hh1 : heap + 1 < 2 ^ w := by omega
  have hh2 : heap + 2 < 2 ^ w := by omega
  have hh4 : heap + 4 < 2 ^ w := by omega
  have hh5 : heap + 5 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have hfour : 4 < 2 ^ w := by omega
  have hfive : 5 < 2 ^ w := by omega
  have hsc : (if c < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hsx : (if x < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hsy : (if y < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hca : (c*(b : ℤ)).natAbs < 2 ^ w := by omega
  have hpa : ((x-y)*(d : ℤ)).natAbs < 2 ^ w := by omega
  have hcSign : (if c*(b : ℤ) < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hpSign : (if (x-y)*(d : ℤ) < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  apply runs_start_le
  unfold reducedNumeratorBody
  refine runs_seq_call_le hkA (vs := [if c < 0 then 1 else 0, c.natAbs, b, heap])
    (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨heap, rfl, hcost⟩, hzero, hh2⟩
  · intro next memA posA hpostA
    obtain ⟨⟨_, _, hframeA, hzeroA, hpairA⟩, hnext⟩ := hpostA
    change next = heap + 2 at hnext
    change (∀ a < heap, memA a = mem a) at hframeA
    change ZeroFrom memA next at hzeroA
    change ListAt memA heap (encodeInt (c*(b : ℤ))) at hpairA
    have hnextword : next < 2 ^ w := by omega
    refine runs_seq_call_le hkP
      (vs := [if x < 0 then 1 else 0, x.natAbs, if y < 0 then 1 else 0, y.natAbs, d, next])
      (by eval_expr) ?_ ?_ ?_
    · wram_words
    · refine ⟨⟨next, rfl, hxy, hpot⟩, hzeroA, ?_⟩
      change next + 4 < 2 ^ w
      omega
    · intro nextP memP posP hpostP
      obtain ⟨⟨_, _, hframeP, hzeroP, hpairP⟩, hnextP⟩ := hpostP
      change nextP = next + 4 at hnextP
      change (∀ a < next, memP a = memA a) at hframeP
      change ZeroFrom memP nextP at hzeroP
      change ListAt memP (next + 2) (encodeInt ((x-y)*(d : ℤ))) at hpairP
      have hcostP : ListAt memP heap (encodeInt (c*(b : ℤ))) := by
        apply hpairA.of_agree_below (h₀ := next)
        · change heap + 2 ≤ next; omega
        · exact hframeP
      have hcostSign : memP heap = if c*(b : ℤ) < 0 then 1 else 0 := by
        simpa only [encodeInt, Nat.add_zero, List.getElem_cons_zero] using
          hcostP 0 (by change 0 < 2; decide)
      have hcostMag : memP (heap + 1) = (c*(b : ℤ)).natAbs := by
        simpa only [encodeInt, List.getElem_cons_succ, List.getElem_cons_zero] using
          hcostP 1 (by change 1 < 2; decide)
      have hpotAt : ListAt memP (heap + 4) (encodeInt ((x-y)*(d : ℤ))) := by
        simpa only [hnext, Nat.add_assoc] using hpairP
      have hpotSign : memP (heap + 4) = if (x-y)*(d : ℤ) < 0 then 1 else 0 := by
        simpa only [encodeInt, Nat.add_zero, List.getElem_cons_zero] using
          hpotAt 0 (by change 0 < 2; decide)
      have hpotMag : memP (heap + 5) = ((x-y)*(d : ℤ)).natAbs := by
        simpa only [encodeInt, List.getElem_cons_succ, List.getElem_cons_zero,
          show heap + 4 + 1 = heap + 5 by omega] using hpotAt 1 (by change 1 < 2; decide)
      have hnextPword : nextP < 2 ^ w := by omega
      refine runs_seq_call_le hkR
        (vs := [if c*(b : ℤ) < 0 then 1 else 0, (c*(b : ℤ)).natAbs,
          if (x-y)*(d : ℤ) < 0 then 1 else 0, ((x-y)*(d : ℤ)).natAbs, nextP])
        (by eval_expr) ?_ ?_ ?_
      · wram_words
      · refine ⟨⟨nextP, rfl, hsum⟩, hzeroP, ?_⟩
        change nextP + 2 < 2 ^ w
        omega
      · intro out memR posR hpostR
        obtain ⟨⟨_, _, hframeR, hzeroR, hpairR⟩, hout⟩ := hpostR
        change out = nextP + 2 at hout
        change (∀ a < nextP, memR a = memP a) at hframeR
        change ZeroFrom memR out at hzeroR
        change ListAt memR nextP (encodeInt (c*(b : ℤ) - (x-y)*(d : ℤ))) at hpairR
        have houtword : out < 2 ^ w := by omega
        refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
        · change (heap ≤ out ∧ out ≤ heap + 8 ∧ (∀ a < heap, memR a = mem a) ∧
            ZeroFrom memR out ∧ ListAt memR (heap + 6)
              (encodeInt (c*(b : ℤ) - (x-y)*(d : ℤ)))) ∧ out = heap + 8
          refine ⟨⟨by omega, by omega, ?_, hzeroR, ?_⟩, by omega⟩
          · intro a ha
            exact (hframeR a (by omega)).trans ((hframeP a (by omega)).trans (hframeA a ha))
          · have heq : nextP = heap + 6 := by omega
            simpa only [heq] using hpairR
        · simp only [reducedNumeratorContract, heapContract, signedScaleContract,
            scaledDifferenceContract, signedSubtractContract, argsSize_cons, argsSize_nil,
            Expr.size_bin, Expr.size_load, Expr.size_reg, Expr.size_const]; omega

/-- All numerator arithmetic budgets can hold at once for arbitrary operands. -/
theorem exists_reducedNumerator_pre (c x y : ℤ) (b d : ℕ) :
    ∃ w, (∀ a ∈ [if c < 0 then 1 else 0, c.natAbs,
        if x < 0 then 1 else 0, x.natAbs, if y < 0 then 1 else 0, y.natAbs, b, d, 0], a < 2 ^ w) ∧
      (reducedNumeratorContract w c x y b d).pre
        [if c < 0 then 1 else 0, c.natAbs, if x < 0 then 1 else 0, x.natAbs,
          if y < 0 then 1 else 0, y.natAbs, b, d, 0] (fun _ => 0) := by
  let w := c.natAbs + x.natAbs + y.natAbs + c.natAbs*b + (x-y).natAbs*d + b + d + 9
  have hw : c.natAbs + x.natAbs + y.natAbs + c.natAbs*b + (x-y).natAbs*d + b + d + 9 < 2 ^ w :=
    Nat.lt_two_pow_self
  refine ⟨w, ?_, ⟨0, rfl, by omega, by omega, by omega, ?_⟩, (fun _ _ => rfl), ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · split <;> omega
    · omega
    · split <;> omega
    · omega
    · split <;> omega
    all_goals omega
  · simp only [Int.natAbs_mul, Int.natAbs_natCast]
    omega
  · change 0 + 8 < 2 ^ w
    omega

end MinCostFlow.Scaling.Machine
