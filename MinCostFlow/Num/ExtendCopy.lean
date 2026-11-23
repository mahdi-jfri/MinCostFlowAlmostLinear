module

public import MinCostFlow.Num.Encoding
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic

/-!
# Copying a block and filling its high limbs

Arithmetic right shifts need a copy of the remaining source limbs followed by copies
of the sign limb. This helper copies `M` source cells into a fresh block of `K ≥ M`
cells, then fills the rest with one supplied limb. It costs at most `30*K + 6`.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Copy up to `M` source limbs, then fill the high cells to length `K`. -/
def extendedLimbs (mem : ℕ → ℕ) (a fill : ℕ) : ℕ → ℕ → List ℕ
  | _, 0 => []
  | 0, K + 1 => fill :: extendedLimbs mem a fill 0 K
  | M + 1, K + 1 => mem a :: extendedLimbs mem (a + 1) fill M K

@[simp] theorem extendedLimbs_length (mem : ℕ → ℕ) (a fill M K : ℕ) :
    (extendedLimbs mem a fill M K).length = K := by
  induction K generalizing a M with
  | zero => rfl
  | succ K ih => cases M <;> simp [extendedLimbs, ih]

/-- Only the copied source cells affect the extended list. -/
theorem extendedLimbs_congr {mem mem' : ℕ → ℕ} {a fill M K : ℕ}
    (he : ∀ i < M, mem (a + i) = mem' (a + i)) :
    extendedLimbs mem a fill M K = extendedLimbs mem' a fill M K := by
  induction K generalizing a M with
  | zero => rfl
  | succ K ih =>
    cases M with
    | zero => rw [extendedLimbs, extendedLimbs, ih (a := a) (M := 0) (fun i hi => by omega)]
    | succ M =>
      have hh : mem a = mem' a := by simpa using he 0 (by omega)
      rw [extendedLimbs, extendedLimbs, hh, ih]
      intro i hi
      simpa only [Nat.add_assoc, Nat.add_comm 1] using he (i + 1) (by omega)

/-- Valid source and fill limbs give a valid extended list. -/
theorem extendedLimbs_lt {mem : ℕ → ℕ} {a h fill M K : ℕ}
    (hv : Valid mem a h M) (hf : fill < base h) :
    ∀ x ∈ extendedLimbs mem a fill M K, x < base h := by
  induction K generalizing a M with
  | zero => simp [extendedLimbs]
  | succ K ih =>
    cases M with
    | zero =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hf
      · exact ih hv _ hx
    | succ M =>
      obtain ⟨hh, ht⟩ := valid_succ.mp hv
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hh
      · exact ih ht _ hx

/-- Arguments `[a, M, K, fill, heap]`. -/
def extendCopyBody (b : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.reg 4))
    (.cond (.bin .eq (.reg 1) (.const 0))
      (.store (.reg 4) (.reg 3) ;;
       .call 5 b [.reg 0, .const 0, .bin .sub (.reg 2) (.const 1), .reg 3,
         .bin .add (.reg 4) (.const 1)] ;; .ret (.reg 5))
      (.store (.reg 4) (.load (.reg 0)) ;;
       .call 5 b [.bin .add (.reg 0) (.const 1), .bin .sub (.reg 1) (.const 1),
         .bin .sub (.reg 2) (.const 1), .reg 3, .bin .add (.reg 4) (.const 1)] ;;
       .ret (.reg 5)))

/-- The copy-and-fill helper. -/
def extendCopyModule (b : ℕ) : List Stmt := [extendCopyBody b]

/-- Copy `M` valid limbs and fill the high `K-M` cells of a fresh block. -/
def extendCopyContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a M K fill heap, args = [a, M, K, fill, heap] ∧
      M ≤ K ∧ a + M ≤ heap ∧ fill < base h ∧ Valid mem a h M)
    (fun args mem mem' => ListAt mem' (heapArg args)
      (extendedLimbs mem (args.getD 0 0) (args.getD 3 0) (args.getD 1 0) (args.getD 2 0)))
    (fun args _ => 30 * args.getD 2 0 + 6) (fun args _ => args.getD 2 0)
  { C with post := fun args mem v mem' =>
      v = heapArg args + args.getD 2 0 ∧ C.post args mem v mem' }

/-- Copy-and-fill uses no random bits. -/
theorem extendCopyBody_noRand (b : ℕ) : (extendCopyBody b).NoRand := by
  simp [extendCopyBody, Stmt.NoRand]

/-- Copy-and-fill meets its heap contract with a linear cost. -/
theorem extendCopy_meetsContract {w h b : ℕ} {p : Program} (hw : 1 < 2 ^ w)
    (hp : p.HasAt b (extendCopyModule b)) : MeetsContract w p b (extendCopyContract w h) := by
  apply meetsContract_of_rec (fun args _ => args.getD 2 0) hp.head
  intro k ih args mem pos ω hwords hpre hk
  rcases hpre with ⟨⟨a, M, K, fill, heap, rfl, hMK, ha, hf, hv⟩, hz, hb⟩
  change K = k at hk
  subst k
  change ZeroFrom mem heap at hz
  change heap + K < 2 ^ w at hb
  have hfw : fill < 2 ^ w := hwords fill (by simp)
  apply runs_start_le
  unfold extendCopyBody
  wram_step
  · have hK : K = 0 := by simpa [startState] using hcond
    subst K
    refine runs_ret_le (by eval_expr) ?_ ?_
    · refine ⟨rfl, ?_⟩
      change heap ≤ heap ∧ heap ≤ heap + 0 ∧ (∀ x < heap, mem x = mem x) ∧
        ZeroFrom mem heap ∧ ListAt mem heap []
      exact ⟨le_rfl, le_rfl, fun _ _ => rfl, hz, listAt_nil _ _⟩
    · simp only [extendCopyContract, heapContract, List.getD_cons_zero,
        List.getD_cons_succ, Expr.size_bin, Expr.size_reg, Expr.size_const]
      omega
  · have hK : K ≠ 0 := by simpa [startState] using hcond
    wram_step
    · have hM : M = 0 := by simpa [startState] using hcond
      subst M
      refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
      refine runs_seq_call_le ih (vs := [a, 0, K - 1, fill, heap + 1])
        (by eval_expr) (by wram_words) ?_ ?_
      · change ((∃ a' M' K' fill' heap', [a, 0, K - 1, fill, heap + 1] = [a', M', K', fill', heap'] ∧
            M' ≤ K' ∧ a' + M' ≤ heap' ∧ fill' < base h ∧
            Valid (Function.update mem heap fill) a' h M') ∧
          ZeroFrom (Function.update mem heap fill) (heap + 1) ∧ heap + 1 + (K - 1) < 2 ^ w) ∧ K - 1 < K
        exact ⟨⟨⟨a, 0, K - 1, fill, heap + 1, rfl, by omega, by omega, hf,
          fun i hi => by omega⟩, hz.update_head fill, by omega⟩, by omega⟩
      · intro v mem' pos' hpst
        rcases hpst with ⟨he, hlo, hhi, hframe, hzero, hlist⟩
        change v = heap + 1 + (K - 1) at he
        change (∀ x < heap + 1, mem' x = Function.update mem heap fill x) at hframe
        have hvw : v < 2 ^ w := by omega
        refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
        · refine ⟨by change v = heap + K; omega, ?_⟩
          change heap ≤ v ∧ v ≤ heap + K ∧ (∀ x < heap, mem' x = mem x) ∧ ZeroFrom mem' v ∧
            ListAt mem' heap (extendedLimbs mem a fill 0 K)
          refine ⟨by omega, by omega, ?_, hzero, ?_⟩
          · intro x hx
            rw [hframe x (by omega), Function.update_of_ne (by omega)]
          · obtain ⟨T, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK
            rw [extendedLimbs, listAt_cons]
            refine ⟨by rw [hframe heap (by omega), Function.update_self], ?_⟩
            change ListAt mem' (heap + 1) (extendedLimbs (Function.update mem heap fill) a fill 0 T) at hlist
            rw [extendedLimbs_congr (mem' := mem) (fun i hi => by omega)] at hlist
            exact hlist
        · simp only [extendCopyContract, Contract.below, heapContract, List.getD_cons_zero,
            List.getD_cons_succ, Expr.size_bin, Expr.size_reg, Expr.size_const,
            argsSize_cons, argsSize_nil]
          omega
    · have hM : M ≠ 0 := by simpa [startState] using hcond
      obtain ⟨S, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM
      obtain ⟨hhead, htail⟩ := valid_succ.mp hv
      refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
      refine runs_seq_call_le ih (vs := [a + 1, S, K - 1, fill, heap + 1])
        (by eval_expr; simp [Expr.eval, BinOp.eval, startState, hw, show S < 2 ^ w by omega])
        (by wram_words) ?_ ?_
      · change ((∃ a' M' K' fill' heap', [a + 1, S, K - 1, fill, heap + 1] = [a', M', K', fill', heap'] ∧
            M' ≤ K' ∧ a' + M' ≤ heap' ∧ fill' < base h ∧
            Valid (Function.update mem heap (mem a)) a' h M') ∧
          ZeroFrom (Function.update mem heap (mem a)) (heap + 1) ∧ heap + 1 + (K - 1) < 2 ^ w) ∧ K - 1 < K
        refine ⟨⟨⟨a + 1, S, K - 1, fill, heap + 1, rfl, by omega, by omega, hf, ?_⟩,
          hz.update_head _, by omega⟩, by omega⟩
        intro i hi
        rw [Function.update_of_ne (by omega)]
        exact htail i hi
      · intro v mem' pos' hpst
        rcases hpst with ⟨he, hlo, hhi, hframe, hzero, hlist⟩
        change v = heap + 1 + (K - 1) at he
        change (∀ x < heap + 1, mem' x = Function.update mem heap (mem a) x) at hframe
        have hvw : v < 2 ^ w := by omega
        refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
        · refine ⟨by change v = heap + K; omega, ?_⟩
          change heap ≤ v ∧ v ≤ heap + K ∧ (∀ x < heap, mem' x = mem x) ∧ ZeroFrom mem' v ∧
            ListAt mem' heap (extendedLimbs mem a fill (S + 1) K)
          refine ⟨by omega, by omega, ?_, hzero, ?_⟩
          · intro x hx
            rw [hframe x (by omega), Function.update_of_ne (by omega)]
          · obtain ⟨T, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK
            rw [extendedLimbs, listAt_cons]
            refine ⟨by rw [hframe heap (by omega), Function.update_self], ?_⟩
            change ListAt mem' (heap + 1)
              (extendedLimbs (Function.update mem heap (mem a)) (a + 1) fill S T) at hlist
            have heq : extendedLimbs (Function.update mem heap (mem a)) (a + 1) fill S T =
                extendedLimbs mem (a + 1) fill S T := by
              apply extendedLimbs_congr
              intro i hi
              exact Function.update_of_ne (by omega) _ _
            rwa [heq] at hlist
        · simp only [extendCopyContract, Contract.below, heapContract, List.getD_cons_zero,
            List.getD_cons_succ, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
            argsSize_cons, argsSize_nil]
          omega

end MinCostFlow.Num
