module

public import MinCostFlow.Num.DivisionStep
public import MinCostFlow.Num.DivisionLoopFacts
import MinCostFlow.Num.SignFacts
import MinCostFlow.Num.DivisionStepFacts
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic

/-!
# The quotient-digit loop

The loop visits numerator limbs from highest to lowest. Each step writes one quotient
digit into a preallocated block and puts its new remainder at the end of fresh memory.
The recursive problem has one fewer pending limb. Exact quotient and remainder
recurrences prove the full result. There are `i` steps at cost at most
`i*(300*K+644)+6`, and the loop allocates `5*i*(K+1)` fresh cells.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[a, d, n, K, i, quotient, remainder, heap]`. -/
def divisionLoopBody (self step : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 4) (.const 0)) (.ret (.reg 7))
    (.call 8 step [.reg 6, .reg 1, .reg 2, .reg 3,
       .load (.bin .add (.reg 0) (.bin .sub (.reg 4) (.const 1))), .reg 7] ;;
     .store (.bin .add (.reg 5) (.bin .sub (.reg 4) (.const 1))) (.load (.reg 7)) ;;
     .call 9 self [.reg 0, .reg 1, .reg 2, .reg 3, .bin .sub (.reg 4) (.const 1), .reg 5,
       .bin .sub (.reg 8) (.bin .add (.reg 3) (.const 1)), .reg 8] ;;
     .ret (.reg 9))

/-- The quotient loop, linked to the owned division-step procedure. -/
def divisionLoopModule (b step : ℕ) : List Stmt := [divisionLoopBody b step]

/-- The remainder block ends at the heap. The quotient buffer is below it and both
source blocks lie below the quotient buffer. Only pending quotient cells and fresh
memory can change. The final remainder again ends at the returned heap pointer. -/
def divisionLoopContract (w h : ℕ) : Contract where
  pre args mem := ∃ a d n K i q r heap, args = [a, d, n, K, i, q, r, heap] ∧
    i ≤ K ∧ 0 < n ∧ n ≤ K ∧ a + K ≤ q ∧ d + (K + 1) ≤ q ∧ q + K ≤ r ∧ r + (K + 1) = heap ∧
    Valid mem a h K ∧ Valid mem d h (K + 1) ∧ Valid mem q h i ∧ Valid mem r h (K + 1) ∧
    0 < mem (d + (n - 1)) ∧ (∀ j, n ≤ j → j < K + 1 → mem (d + j) = 0) ∧
    unsignedVal mem r h (K + 1) < unsignedVal mem d h (K + 1) ∧
    ZeroFrom mem heap ∧ heap + 5 * i * (K + 1) < 2 ^ w
  post args mem v mem' := v = args.getD 7 0 + 5 * args.getD 4 0 * (args.getD 3 0 + 1) ∧
    ZeroFrom mem' v ∧
    (∀ z < args.getD 7 0, z < args.getD 5 0 ∨ args.getD 5 0 + args.getD 4 0 ≤ z → mem' z = mem z) ∧
    Valid mem' (args.getD 5 0) h (args.getD 4 0) ∧
    unsignedVal mem' (args.getD 5 0) h (args.getD 4 0) =
      loopNumerator mem (args.getD 0 0) (args.getD 6 0) h (args.getD 3 0) (args.getD 4 0) /
        unsignedVal mem (args.getD 1 0) h (args.getD 3 0 + 1) ∧
    Valid mem' (v - (args.getD 3 0 + 1)) h (args.getD 3 0 + 1) ∧
    unsignedVal mem' (v - (args.getD 3 0 + 1)) h (args.getD 3 0 + 1) =
      loopNumerator mem (args.getD 0 0) (args.getD 6 0) h (args.getD 3 0) (args.getD 4 0) %
        unsignedVal mem (args.getD 1 0) h (args.getD 3 0 + 1)
  cost args _ := args.getD 4 0 * (300 * args.getD 3 0 + 644) + 6

/-- The digit loop itself has no random statement. -/
theorem divisionLoopBody_noRand (self step : ℕ) : (divisionLoopBody self step).NoRand := by
  simp [divisionLoopBody, Stmt.NoRand]

private theorem divisionLoop_cost (K S : ℕ) :
    (300 * K + 600) + 44 + (S * (300 * K + 644) + 6) ≤
      (S + 1) * (300 * K + 644) + 6 := by
  rw [Nat.add_mul, one_mul]
  omega

/-- The quotient loop meets its exact division contract using the verified step. -/
theorem divisionLoop_meetsContract {w h b step : ℕ} {p : Program}
    (hw : 1 < 2 ^ w) (hb : base h < 2 ^ w)
    (hp : p.HasAt b (divisionLoopModule b step))
    (hs : MeetsContract w p step (divisionStepContract w h)) :
    MeetsContract w p b (divisionLoopContract w h) := by
  apply meetsContract_of_rec (fun args _ => args.getD 4 0) hp.head
  intro t ih args mem pos ω hwords hpre ht
  rcases hpre with ⟨a, d, n, K, i, q, r, heap, rfl, hiK, hn, hnK, ha, hd, hqr, hr,
    hva, hvd, hvq, hvr, htop, hzeros, hR, hz, hbound⟩
  change i = t at ht
  subst t
  have haw : a < 2 ^ w := hwords a (by simp)
  have hdw : d < 2 ^ w := hwords d (by simp)
  have hnw : n < 2 ^ w := hwords n (by simp)
  have hKw : K < 2 ^ w := hwords K (by simp)
  have hqw : q < 2 ^ w := hwords q (by simp)
  have hrw : r < 2 ^ w := hwords r (by simp)
  have hheapw : heap < 2 ^ w := hwords heap (by simp)
  have hMw : K + 1 < 2 ^ w := by omega
  have hVpos : 0 < unsignedVal mem d h (K + 1) := by omega
  apply runs_start_le
  unfold divisionLoopBody
  wram_step
  · have hi0 : i = 0 := by simpa [startState] using hcond
    subst i
    have hloop : loopNumerator mem a r h K 0 = unsignedVal mem r h (K + 1) := by
      simp [loopNumerator, capacity, unsignedVal]
    refine runs_ret_le (by eval_expr) ?_ ?_
    · change heap = heap + 5 * 0 * (K + 1) ∧ ZeroFrom mem heap ∧
        (∀ z < heap, z < q ∨ q + 0 ≤ z → mem z = mem z) ∧ Valid mem q h 0 ∧
        unsignedVal mem q h 0 = loopNumerator mem a r h K 0 / unsignedVal mem d h (K + 1) ∧
        Valid mem (heap - (K + 1)) h (K + 1) ∧
        unsignedVal mem (heap - (K + 1)) h (K + 1) =
          loopNumerator mem a r h K 0 % unsignedVal mem d h (K + 1)
      refine ⟨by omega, hz, fun _ _ _ => rfl, fun j hj => by omega, ?_, ?_, ?_⟩
      · rw [hloop, unsignedVal, Nat.div_eq_of_lt hR]
      · simpa only [show heap - (K + 1) = r by omega] using hvr
      · rw [hloop, Nat.mod_eq_of_lt hR, show heap - (K + 1) = r by omega]
    · simp only [divisionLoopContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size_bin,
        Expr.size_reg, Expr.size_const, zero_mul]
      omega
  · have hin : i ≠ 0 := by simpa [startState] using hcond
    obtain ⟨S, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hin
    have hspace : 5 * (S + 1) * (K + 1) = 5 * (K + 1) + 5 * S * (K + 1) := by ring
    rw [hspace] at hbound
    have hstepbound : heap + 5 * (K + 1) < 2 ^ w := by omega
    have hdigit : mem (a + S) < base h := hva S (by omega)
    have hdigitw : mem (a + S) < 2 ^ w := lt_trans hdigit hb
    refine runs_seq_call_le hs (vs := [r, d, n, K, mem (a + S), heap])
      (by eval_expr)
      (by wram_words) ?_ ?_
    · exact ⟨⟨r, d, n, K, _, heap, rfl, hn, hnK, by omega, by omega, hvr, hvd, htop,
        hzeros, hR, hdigit⟩, hz, hstepbound⟩
    · intro vStep mem₁ pos₁ hp₁
      rcases hp₁ with ⟨hvStep, hlo₁, hhi₁, hf₁, hz₁, hhead, hvalidR₁, hvalueR₁⟩
      change vStep = heap + 5 * (K + 1) at hvStep
      clear hlo₁ hhi₁
      change (∀ z < heap, mem₁ z = mem z) at hf₁
      change mem₁ heap = stepNumerator mem r h K (mem (a + S)) / unsignedVal mem d h (K + 1) at hhead
      change Valid mem₁ (heap + 4 * (K + 1)) h (K + 1) at hvalidR₁
      change unsignedVal mem₁ (heap + 4 * (K + 1)) h (K + 1) =
        stepNumerator mem r h K (mem (a + S)) % unsignedVal mem d h (K + 1) at hvalueR₁
      have hqB : stepNumerator mem r h K (mem (a + S)) / unsignedVal mem d h (K + 1) < base h := by
        apply (Nat.div_lt_iff_lt_mul hVpos).mpr
        simpa only [stepNumerator, Nat.mul_comm] using remainder_append_lt hR hdigit
      have hqword : stepNumerator mem r h K (mem (a + S)) / unsignedVal mem d h (K + 1) < 2 ^ w := lt_trans hqB hb
      have hvStepw : vStep < 2 ^ w := by omega
      refine runs_seq_store_le (x := q + S)
        (v := stepNumerator mem r h K (mem (a + S)) / unsignedVal mem d h (K + 1))
        (by eval_expr; simp [Expr.eval, BinOp.eval, startState, hw, show S < 2 ^ w by omega]) (by eval_expr) ?_
      let mem₂ := Function.update mem₁ (q + S)
        (stepNumerator mem r h K (mem (a + S)) / unsignedVal mem d h (K + 1))
      have hA : ∀ j < K, mem₂ (a + j) = mem (a + j) := by
        intro j hj
        dsimp only [mem₂]
        rw [Function.update_of_ne (by omega), hf₁ (a + j) (by omega)]
      have hD : ∀ j < K + 1, mem₂ (d + j) = mem (d + j) := by
        intro j hj
        dsimp only [mem₂]
        rw [Function.update_of_ne (by omega), hf₁ (d + j) (by omega)]
      have hDvalue : unsignedVal mem₂ d h (K + 1) = unsignedVal mem d h (K + 1) := unsignedVal_congr hD
      have hRvalid : Valid mem₂ (vStep - (K + 1)) h (K + 1) := by
        intro j hj
        dsimp only [mem₂]
        rw [Function.update_of_ne (by omega)]
        simpa only [show vStep - (K + 1) = heap + 4 * (K + 1) by omega] using hvalidR₁ j hj
      have hRvalue : unsignedVal mem₂ (vStep - (K + 1)) h (K + 1) =
          stepNumerator mem r h K (mem (a + S)) % unsignedVal mem d h (K + 1) := by
        rw [← hvalueR₁]
        apply unsignedVal_congr
        intro j hj
        dsimp only [mem₂]
        rw [Function.update_of_ne (by omega)]
        congr 1
        omega
      have hQvalid : Valid mem₂ q h S := by
        intro j hj
        dsimp only [mem₂]
        rw [Function.update_of_ne (by omega), hf₁ (q + j) (by omega)]
        exact hvq j (by omega)
      have hzero₂ : ZeroFrom mem₂ vStep := hz₁.update_lt (by omega)
      have hnewNum : loopNumerator mem₂ a (vStep - (K + 1)) h K S =
          (stepNumerator mem r h K (mem (a + S)) % unsignedVal mem d h (K + 1)) * capacity h S +
            unsignedVal mem a h S := by
        unfold loopNumerator
        rw [hRvalue, unsignedVal_congr (fun j hj => hA j (by omega))]
      refine runs_seq_call_le ih (vs := [a, d, n, K, S, q, vStep - (K + 1), vStep])
        (by eval_expr; simp [Expr.eval, BinOp.eval, startState, hw, show S < 2 ^ w by omega])
        (by wram_words) ?_ ?_
      · change (∃ a' d' n' K' i' q' r' heap',
            [a, d, n, K, S, q, vStep - (K + 1), vStep] = [a', d', n', K', i', q', r', heap'] ∧
            i' ≤ K' ∧ 0 < n' ∧ n' ≤ K' ∧ a' + K' ≤ q' ∧ d' + (K' + 1) ≤ q' ∧ q' + K' ≤ r' ∧
            r' + (K' + 1) = heap' ∧ Valid mem₂ a' h K' ∧ Valid mem₂ d' h (K' + 1) ∧
            Valid mem₂ q' h i' ∧ Valid mem₂ r' h (K' + 1) ∧ 0 < mem₂ (d' + (n' - 1)) ∧
            (∀ j, n' ≤ j → j < K' + 1 → mem₂ (d' + j) = 0) ∧
            unsignedVal mem₂ r' h (K' + 1) < unsignedVal mem₂ d' h (K' + 1) ∧
            ZeroFrom mem₂ heap' ∧ heap' + 5 * i' * (K' + 1) < 2 ^ w) ∧ S < S + 1
        refine ⟨⟨a, d, n, K, S, q, _, vStep, rfl, by omega, hn, hnK, ha, hd, by omega,
          by omega, ?_, ?_, hQvalid, hRvalid, ?_, ?_, ?_, hzero₂, by omega⟩, by omega⟩
        · intro j hj
          rw [hA j hj]
          exact hva j hj
        · intro j hj
          rw [hD j hj]
          exact hvd j hj
        · rw [hD (n - 1) (by omega)]
          exact htop
        · intro j hj hk
          rw [hD j hk]
          exact hzeros j hj hk
        · rw [hRvalue, hDvalue]
          exact Nat.mod_lt _ hVpos
      · intro vend mem₃ pos₃ hp₃
        rcases hp₃ with ⟨hvend, hz₃, hf₃, hQvalid₃, hQvalue₃, hRvalid₃, hRvalue₃⟩
        change vend = vStep + 5 * S * (K + 1) at hvend
        change (∀ z < vStep, z < q ∨ q + S ≤ z → mem₃ z = mem₂ z) at hf₃
        change Valid mem₃ q h S at hQvalid₃
        change unsignedVal mem₃ q h S = loopNumerator mem₂ a (vStep - (K + 1)) h K S /
          unsignedVal mem₂ d h (K + 1) at hQvalue₃
        change Valid mem₃ (vend - (K + 1)) h (K + 1) at hRvalid₃
        change unsignedVal mem₃ (vend - (K + 1)) h (K + 1) = loopNumerator mem₂ a (vStep - (K + 1)) h K S %
          unsignedVal mem₂ d h (K + 1) at hRvalue₃
        rw [hnewNum, hDvalue] at hQvalue₃ hRvalue₃
        have hlast : mem₃ (q + S) = stepNumerator mem r h K (mem (a + S)) / unsignedVal mem d h (K + 1) := by
          rw [hf₃ (q + S) (by omega) (Or.inr le_rfl)]
          dsimp only [mem₂]
          exact Function.update_self _ _ _
        have hrec := long_division_recurrence (stepNumerator mem r h K (mem (a + S)))
          (capacity h S) (unsignedVal mem a h S) (unsignedVal mem d h (K + 1)) hVpos
        have hvendw : vend < 2 ^ w := by omega
        refine runs_ret_le (v := vend) (by eval_expr) ?_ ?_
        · change vend = heap + 5 * (S + 1) * (K + 1) ∧ ZeroFrom mem₃ vend ∧
            (∀ z < heap, z < q ∨ q + (S + 1) ≤ z → mem₃ z = mem z) ∧ Valid mem₃ q h (S + 1) ∧
            unsignedVal mem₃ q h (S + 1) = loopNumerator mem a r h K (S + 1) / unsignedVal mem d h (K + 1) ∧
            Valid mem₃ (vend - (K + 1)) h (K + 1) ∧
            unsignedVal mem₃ (vend - (K + 1)) h (K + 1) = loopNumerator mem a r h K (S + 1) % unsignedVal mem d h (K + 1)
          refine ⟨by rw [hspace]; omega, hz₃, ?_, ?_, ?_, hRvalid₃, ?_⟩
          · intro z hz' houtside
            rw [hf₃ z (by omega) (by omega)]
            dsimp only [mem₂]
            rw [Function.update_of_ne (by omega), hf₁ z hz']
          · intro j hj
            by_cases he : j < S
            · exact hQvalid₃ j he
            · have heq : j = S := by omega
              subst j
              rw [hlast]
              exact hqB
          · rw [unsignedVal_snoc, hlast, hQvalue₃, loopNumerator_step, hrec.1]
          · rw [hRvalue₃, loopNumerator_step, hrec.2]
        · simp only [divisionLoopContract, Contract.below, divisionStepContract, heapContract,
            List.getD_cons_zero, List.getD_cons_succ, Expr.size_bin, Expr.size_reg,
            Expr.size_const, Expr.size_load, argsSize_cons, argsSize_nil]
          nlinarith only [divisionLoop_cost K S]

end MinCostFlow.Num
