module

public import MinCostFlow.Scaling.WordPairProgram
public import MinCostFlow.Statement.Problem
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Scaling one-word-magnitude signed integers

The cost-scaling loop multiplies signed costs and potentials by natural
factors. This procedure multiplies the magnitude, retains the sign when the
product is nonzero, and writes canonical zero otherwise. It allocates two
words and costs at most 100 steps, with no random instructions.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Zero magnitude product has the canonical zero encoding. -/
theorem encodeInt_mul_nat_zero (z : ℤ) (d : ℕ) (hq : z.natAbs * d = 0) :
    encodeInt (z * (d : ℤ)) = [0, 0] := by
  have hz : z * (d : ℤ) = 0 := by
    have hh : (z * (d : ℤ)).natAbs = 0 := by
      simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hq
    exact Int.natAbs_eq_zero.mp hh
  rw [hz]
  rfl

/-- A nonzero natural factor preserves the sign of a nonzero integer. -/
theorem encodeInt_mul_nat_nonzero (z : ℤ) (d : ℕ) (hq : z.natAbs * d ≠ 0) :
    encodeInt (z * (d : ℤ)) = [if z < 0 then 1 else 0, z.natAbs * d] := by
  have hd : 0 < (d : ℤ) := by
    have hn : d ≠ 0 := fun h => hq (by rw [h, Nat.mul_zero])
    exact Int.natCast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hsign : z * (d : ℤ) < 0 ↔ z < 0 := by
    constructor
    · intro hz
      by_contra hn
      have hz0 : 0 ≤ z := le_of_not_gt hn
      exact (not_lt_of_ge (mul_nonneg hz0 (le_of_lt hd))) hz
    · intro hz
      exact mul_neg_of_neg_of_pos hz hd
  simp only [encodeInt, hsign, Int.natAbs_mul, Int.natAbs_natCast]

/-- Arguments `[sign,magnitude,factor,heap]`. -/
def signedScaleBody (writer : ℕ) : Stmt :=
  .assign 4 (.bin .mul (.reg 1) (.reg 2)) ;;
  .cond (.bin .eq (.reg 4) (.const 0))
    (.call 5 writer [.const 0, .const 0, .reg 3] ;; .ret (.reg 5))
    (.call 5 writer [.reg 0, .reg 4, .reg 3] ;; .ret (.reg 5))

/-- Exact signed scaling followed by its canonical pair writer. -/
def signedScaleModule (b : ℕ) : List Stmt := [signedScaleBody (b + 1), wordPairBody]

/-- The magnitude product must fit
as well as the supplied argument words. -/
def signedScaleContract (w : ℕ) (z : ℤ) (d : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ heap, args = [if z < 0 then 1 else 0, z.natAbs, d, heap] ∧
      z.natAbs * d < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args) (encodeInt (z * (d : ℤ))))
    (fun _ _ => 100) (fun _ _ => 2)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧ out = heapArg args + 2 }

/-- Both exact scaling procedures have no random instructions. -/
theorem signedScaleModule_noRand (b : ℕ) :
    ∀ body ∈ signedScaleModule b, body.NoRand := by
  simp only [signedScaleModule, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨by simp only [signedScaleBody, Stmt.NoRand, and_self], wordPairBody_noRand⟩

/-- The procedure computes exactly the signed-product function,
with canonical zero, exact allocation, and constant machine cost. -/
theorem signedScale_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (signedScaleModule b)) (z : ℤ) (d : ℕ) :
    MeetsContract w p b (signedScaleContract w z d) := by
  have hwriter : p.HasAt (b + 1) wordPairModule := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [signedScaleModule, wordPairModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [signedScaleModule])
  have hk := wordPair_meetsContract (w := w) hwriter
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨heap, rfl, hsum⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + 2 < 2 ^ w at hspace
  have hz : z.natAbs < 2 ^ w := hwords _ (by simp)
  have hdword : d < 2 ^ w := hwords _ (by simp)
  have hqword : z.natAbs * d < 2 ^ w := hsum
  have hsword : (if z < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hh : heap < 2 ^ w := by omega
  have htwo : 2 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  apply runs_start_le
  unfold signedScaleBody
  wram_step
  wram_step
  · have hq : z.natAbs * d = 0 := by simpa [startState] using hcond
    have hencoding := encodeInt_mul_nat_zero z d hq
    refine runs_seq_call_le hk (vs := [0, 0, heap]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨0, 0, heap, rfl⟩, hzero, hspace⟩
    · intro out mem' pos' hpost
      have hptr := hpost.2
      change out = heap + 2 at hptr
      have hout : out < 2 ^ w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change (heap ≤ out ∧ out ≤ heap + 2 ∧ (∀ x < heap, mem' x = mem x) ∧
          ZeroFrom mem' out ∧ ListAt mem' heap (encodeInt (z * (d : ℤ)))) ∧ out = heap + 2
        rw [hencoding]
        exact hpost
      · simp only [signedScaleContract, heapContract, wordPairContract,
          Expr.size_bin, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil]
        omega
  · have hq : z.natAbs * d ≠ 0 := by simpa [startState] using hcond
    have hencoding := encodeInt_mul_nat_nonzero z d hq
    refine runs_seq_call_le hk
      (vs := [if z < 0 then 1 else 0, z.natAbs * d, heap]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨_, _, heap, rfl⟩, hzero, hspace⟩
    · intro out mem' pos' hpost
      have hptr := hpost.2
      change out = heap + 2 at hptr
      have hout : out < 2 ^ w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change (heap ≤ out ∧ out ≤ heap + 2 ∧ (∀ x < heap, mem' x = mem x) ∧
          ZeroFrom mem' out ∧ ListAt mem' heap (encodeInt (z * (d : ℤ)))) ∧ out = heap + 2
        rw [hencoding]
        exact hpost
      · simp only [signedScaleContract, heapContract, wordPairContract,
          Expr.size_bin, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil]
        omega

/-- Every integer and natural factor have simultaneous witnesses for all premises together. -/
theorem exists_signedScale_pre (z : ℤ) (d : ℕ) :
    ∃ w, (∀ x ∈ [if z < 0 then 1 else 0, z.natAbs, d, 0], x < 2 ^ w) ∧
      (signedScaleContract w z d).pre
        [if z < 0 then 1 else 0, z.natAbs, d, 0] (fun _ => 0) := by
  let w := z.natAbs * d + z.natAbs + d + 3
  have hw : z.natAbs * d + z.natAbs + d + 3 < 2 ^ w := Nat.lt_two_pow_self
  refine ⟨w, ?_, ⟨0, rfl, by omega⟩, (fun _ _ => rfl), ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · split <;> omega
    · omega
    · omega
    · omega
  · change 0 + 2 < 2 ^ w
    omega

end MinCostFlow.Scaling.Machine
