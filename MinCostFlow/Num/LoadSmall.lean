module

public import MinCostFlow.Num.Encoding
public import WordRAM.Layout
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Loading a one-word nonnegative integer

Repeated division by the limb base writes the low digit and then the remaining digits.
The recursive call uses one fewer limb and the next heap cell. The result is the input
modulo the block capacity. The contract records the actual digit list, so callers can
recover either the unsigned or the signed value. The cost is at most `23 * L + 6`.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[n, L, heap]`, recursive entry `b`, limb width `h`. -/
def loadSmallBody (b h : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0))
    (.ret (.reg 2))
    (.store (.reg 2) (.bin .mod (.reg 0) (.const (base h))) ;;
     .call 3 b [.bin .div (.reg 0) (.const (base h)),
       .bin .sub (.reg 1) (.const 1), .bin .add (.reg 2) (.const 1)] ;;
     .ret (.reg 3))

/-- A module whose recursive call targets its own entry. -/
def loadSmallModule (b h : ℕ) : List Stmt := [loadSmallBody b h]

/-- Load the low `L` limbs of a one-word integer. Overflow wraps modulo capacity.
The signed result is `signedVal h L (n % capacity h L)`. -/
def loadSmallContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ n L heap, args = [n, L, heap])
    (fun args _ mem' => ListAt mem' (heapArg args)
      (digits h (args.getD 1 0) (args.getD 0 0)))
    (fun args _ => 23 * args.getD 1 0 + 6) (fun args _ => args.getD 1 0)
  { C with post := fun args mem v mem' =>
      v = heapArg args + args.getD 1 0 ∧ C.post args mem v mem' }

/-- The recursive loader contains no random statement. -/
theorem loadSmallBody_noRand (b h : ℕ) : (loadSmallBody b h).NoRand := by
  simp [loadSmallBody, Stmt.NoRand]

/-- Loading terminates for every length, with a linear cost and the shared heap discipline. -/
theorem loadSmall_meetsContract {w h b : ℕ} {p : Program}
    (hw : 1 < 2 ^ w) (hb : base h < 2 ^ w)
    (hp : p.HasAt b (loadSmallModule b h)) :
    MeetsContract w p b (loadSmallContract w h) := by
  apply meetsContract_of_rec (fun args _ => args.getD 1 0) hp.head
  intro k ih args mem pos ω hwords hpre hk
  rcases hpre with ⟨⟨n, L, heap, rfl⟩, hz, hbound⟩
  change L = k at hk
  subst k
  change ZeroFrom mem heap at hz
  change heap + L < 2 ^ w at hbound
  have hn : n < 2 ^ w := hwords n (by simp)
  have hL : L < 2 ^ w := hwords L (by simp)
  have hheap : heap < 2 ^ w := hwords heap (by simp)
  have hquot : n / base h < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) hn
  apply runs_start_le
  unfold loadSmallBody
  wram_step
  · have hzero : L = 0 := by simpa [startState] using hcond
    subst L
    refine runs_ret_le (by eval_expr) ?_ ?_
    · refine ⟨rfl, ?_⟩
      change heap ≤ heap ∧ heap ≤ heap + 0 ∧
        (∀ x < heap, mem x = mem x) ∧ ZeroFrom mem heap ∧ ListAt mem heap []
      exact ⟨le_rfl, le_rfl, fun _ _ => rfl, hz, listAt_nil _ _⟩
    · simp only [loadSmallContract, heapContract, List.getD_cons_zero, List.getD_cons_succ,
        Expr.size_bin, Expr.size_reg, Expr.size_const]
      omega
  · have hnonzero : L ≠ 0 := by simpa [startState] using hcond
    have hdec : L - 1 < L := by simpa using (show L - 1 < L by omega)
    have hpred : L - 1 < 2 ^ w := by omega
    have hnext : heap + 1 < 2 ^ w := by omega
    refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
    have hz' : ZeroFrom (Function.update mem heap (n % base h)) (heap + 1) :=
      hz.update_head _
    have hcall : MeetsContract w p b
        ((loadSmallContract w h).below (fun args _ => args.getD 1 0) L) := ih
    refine runs_seq_call_le hcall (by eval_expr) ?_ ?_ ?_
    · wram_words
    · change ((∃ n' L' heap', [n / base h, L - 1, heap + 1] = [n', L', heap']) ∧
        ZeroFrom (Function.update mem heap (n % base h)) (heap + 1) ∧
        heap + 1 + (L - 1) < 2 ^ w) ∧ L - 1 < L
      exact ⟨⟨⟨_, _, _, rfl⟩, hz', by omega⟩, hdec⟩
    · intro v mem' pos' hpost
      rcases hpost with ⟨hvexact, hvlo, hvhi, hf, hzero, hlist⟩
      change v = heap + 1 + (L - 1) at hvexact
      change heap + 1 ≤ v at hvlo
      change v ≤ heap + 1 + (L - 1) at hvhi
      change (∀ x < heap + 1, mem' x = Function.update mem heap (n % base h) x) at hf
      change ListAt mem' (heap + 1) (digits h (L - 1) (n / base h)) at hlist
      have hvword : v < 2 ^ w := by omega
      refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
      · refine ⟨by change v = heap + L; omega, ?_⟩
        change heap ≤ v ∧ v ≤ heap + L ∧ (∀ x < heap, mem' x = mem x) ∧
          ZeroFrom mem' v ∧ ListAt mem' heap (digits h L n)
        refine ⟨by omega, by omega, ?_, hzero, ?_⟩
        · intro x hx
          rw [hf x (by omega), Function.update_of_ne (by omega)]
        · obtain ⟨M, he⟩ := Nat.exists_eq_succ_of_ne_zero hnonzero
          subst L
          rw [digits, listAt_cons]
          refine ⟨?_, ?_⟩
          · rw [hf heap (by omega), Function.update_self]
          · simpa using hlist
      · simp only [loadSmallContract, Contract.below, heapContract,
          List.getD_cons_zero, List.getD_cons_succ, Expr.size_bin, Expr.size_reg,
          Expr.size_const, argsSize_cons, argsSize_nil]
        omega

/-- The loader's stored list has the required unsigned value and valid limbs. -/
theorem loadSmall_value {h L n heap : ℕ} {mem : ℕ → ℕ}
    (hx : ListAt mem heap (digits h L n)) :
    Valid mem heap h L ∧ unsignedVal mem heap h L = n % capacity h L ∧
      intVal mem heap h L = signedVal h L (n % capacity h L) := by
  have hv := valid_listAt hx (digits_lt h L n)
  have hu := unsignedVal_listAt (h := h) hx
  rw [digits_length, listVal_digits] at hu
  refine ⟨by simpa using hv, hu, ?_⟩
  rw [intVal, hu]

end MinCostFlow.Num
