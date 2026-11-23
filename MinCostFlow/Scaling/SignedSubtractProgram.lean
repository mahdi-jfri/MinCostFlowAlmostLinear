module

public import MinCostFlow.Scaling.SignedAddProgram
import MinCostFlow.Scaling.ResidualLayout
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Exact subtraction of signed flow and potential values

Cost scaling subtracts residual updates and potential values. Subtraction
adds the negated second operand. Its sign flips only when that operand is
nonzero. The procedure forms that sign in registers and calls the proved
signed addition, so it uses only the result's two fresh cells. Its cost is
at most 120 steps and it has no random instructions.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[xSign,xMagnitude,ySign,yMagnitude,heap]`. -/
def signedSubtractBody (add : ℕ) : Stmt :=
  .call 5 add [.reg 0, .reg 1,
    .bin .mul (.bin .sub (.const 1) (.reg 2)) (.bin .lt (.const 0) (.reg 3)),
    .reg 3, .reg 4] ;; .ret (.reg 5)

/-- Subtraction followed by signed addition and the pair writer. -/
def signedSubtractModule (b : ℕ) : List Stmt :=
  signedSubtractBody (b + 1) :: signedAddModule (b + 1)

/-- The operand magnitudes' sum must fit, just as for signed addition. -/
def signedSubtractContract (w : ℕ) (x y : ℤ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ heap, args =
      [if x < 0 then 1 else 0, x.natAbs, if y < 0 then 1 else 0, y.natAbs, heap] ∧
      x.natAbs + y.natAbs < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args) (encodeInt (x - y)))
    (fun _ _ => 120) (fun _ _ => 2)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧
      out = heapArg args + 2 }

/-- Neither subtraction nor its helpers use random instructions. -/
theorem signedSubtractModule_noRand (b : ℕ) :
    ∀ body ∈ signedSubtractModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [signedSubtractBody, Stmt.NoRand, and_self]
  · exact signedAddModule_noRand _ body hb

/-- The procedure computes canonical signed subtraction with two allocated
cells and constant cost, including subtraction of zero. -/
theorem signedSubtract_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (signedSubtractModule b)) (x y : ℤ) :
    MeetsContract w p b (signedSubtractContract w x y) := by
  have hadd : p.HasAt (b + 1) (signedAddModule (b + 1)) := by
    intro i hi
    have h := hp (i + 1) (by simp only [signedSubtractModule, List.length_cons]; omega)
    have heq : b + (i + 1) = b + 1 + i := by omega
    rw [heq] at h
    simpa only [signedSubtractModule, List.getElem_cons_succ] using h
  have hk := signedAdd_meetsContract (w := w) hadd x (-y)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨heap, rfl, hsum⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + 2 < 2 ^ w at hspace
  have hx : x.natAbs < 2 ^ w := by omega
  have hy : y.natAbs < 2 ^ w := by omega
  have hh : heap < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have hsx : (if x < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hsy : (if y < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hsneg : (if -y < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hflip : 1 - (if y < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hnonzero : (if 0 < y.natAbs then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hproduct : (1 - (if y < 0 then 1 else 0 : ℕ)) *
      (if 0 < y.natAbs then 1 else 0) < 2 ^ w := by
    rw [← negatedCostSign_eq]
    exact hsneg
  apply runs_start_le
  unfold signedSubtractBody
  refine runs_seq_call_le hk
    (vs := [if x < 0 then 1 else 0, x.natAbs, if -y < 0 then 1 else 0, (-y).natAbs, heap]) ?_ ?_ ?_ ?_
  · rw [negatedCostSign_eq, Int.natAbs_neg]
    eval_expr
  · simp only [Int.natAbs_neg]
    wram_words
  · exact ⟨⟨heap, rfl, by simpa only [Int.natAbs_neg] using hsum⟩, hzero, hspace⟩
  · intro out memS posS hpostS
    have hptr := hpostS.2
    change out = heap + 2 at hptr
    have hout : out < 2 ^ w := by omega
    refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
    · change (heap ≤ out ∧ out ≤ heap + 2 ∧ (∀ a < heap, memS a = mem a) ∧
        ZeroFrom memS out ∧ ListAt memS heap (encodeInt (x - y))) ∧ out = heap + 2
      change (heap ≤ out ∧ out ≤ heap + 2 ∧ (∀ a < heap, memS a = mem a) ∧
        ZeroFrom memS out ∧ ListAt memS heap (encodeInt (x + -y))) ∧ out = heap + 2 at hpostS
      simpa only [sub_eq_add_neg] using hpostS
    · simp only [signedSubtractContract, heapContract, signedAddContract,
        argsSize_cons, argsSize_nil, Expr.size_bin, Expr.size_const, Expr.size_reg]; omega

/-- All subtraction premises hold together for every pair of integers. -/
theorem exists_signedSubtract_pre (x y : ℤ) :
    ∃ w, (∀ a ∈ [if x < 0 then 1 else 0, x.natAbs,
        if y < 0 then 1 else 0, y.natAbs, 0], a < 2 ^ w) ∧
      (signedSubtractContract w x y).pre
        [if x < 0 then 1 else 0, x.natAbs, if y < 0 then 1 else 0, y.natAbs, 0] (fun _ => 0) := by
  obtain ⟨w, hwords, hpre⟩ := exists_signedAdd_pre x y
  exact ⟨w, hwords, hpre⟩

end MinCostFlow.Scaling.Machine
