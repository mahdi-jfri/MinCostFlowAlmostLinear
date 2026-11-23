module

public import MinCostFlow.Scaling.WordPairProgram
import WordRAM.Tactic
import WordRAM.Entry
import Mathlib.Tactic.Ring

/-!
# The shared cost-rounding powers

The cost-scaling model uses `B^8` and `B^9`, with `B=2*m`, for its
numerator and clipping bounds. Repeated squaring computes these once
before the edge scan. The procedure writes the two natural powers in
consecutive fresh cells. It costs at most 80 steps and allocates two cells.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[B,heap]`. -/
def costPowersBody (writer : ℕ) : Stmt :=
  .assign 2 (.bin .mul (.reg 0) (.reg 0)) ;;
  .assign 3 (.bin .mul (.reg 2) (.reg 2)) ;;
  .assign 4 (.bin .mul (.reg 3) (.reg 3)) ;;
  .assign 5 (.bin .mul (.reg 4) (.reg 0)) ;;
  .call 6 writer [.reg 4, .reg 5, .reg 1] ;; .ret (.reg 6)

/-- Shared powers followed by the two-word writer. -/
def costPowersModule (b : ℕ) : List Stmt := [costPowersBody (b+1), wordPairBody]

/-- The largest power fits, which also bounds every intermediate product. -/
def costPowersContract (w B : ℕ) : Contract :=
  let C := heapContract w (fun args _ => ∃ heap, args = [B, heap] ∧ B^9 < 2 ^ w)
    (fun args _ mem' => ListAt mem' (heapArg args) [B^8, B^9])
    (fun _ _ => 80) (fun _ _ => 2)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧ out = heapArg args+2 }

private theorem cost_power_le (B k : ℕ) (hk : k ≤ 9) (hpos : 0 < k) : B^k ≤ B^9 := by
  by_cases hB : B = 0
  · subst B
    simp only [Nat.zero_pow hpos, Nat.zero_pow (by decide : 0 < 9)]
    exact le_rfl
  · exact Nat.pow_le_pow_right (by omega) hk

/-- Computing both cost-rounding powers is deterministic. -/
theorem costPowersModule_noRand (b : ℕ) : ∀ body ∈ costPowersModule b, body.NoRand := by
  intro body hb
  simp only [costPowersModule, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · simp only [costPowersBody, Stmt.NoRand, and_self]
  · exact wordPairBody_noRand

/-- Repeated squaring computes exactly the shared cost-rounding constants,
with two fresh words, the heap frame, and constant cost. -/
theorem costPowers_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (costPowersModule b)) (B : ℕ) :
    MeetsContract w p b (costPowersContract w B) := by
  have hpair : p.HasAt (b+1) wordPairModule := by
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [costPowersModule, wordPairModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [costPowersModule])
  have hk := wordPair_meetsContract (w := w) hpair
  have h2 : B*B = B^2 := by ring
  have h4 : B^2*B^2 = B^4 := by ring
  have h8 : B^4*B^4 = B^8 := by ring
  have h9 : B^8*B = B^9 := by ring
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨heap, rfl, hbound⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+2 < 2 ^ w at hspace
  have hB : B < 2 ^ w := hwords _ (by simp)
  have hh : heap < 2 ^ w := by omega
  have hB2 : B^2 < 2 ^ w := (cost_power_le B 2 (by decide) (by decide)).trans_lt hbound
  have hB4 : B^4 < 2 ^ w := (cost_power_le B 4 (by decide) (by decide)).trans_lt hbound
  have hB8 : B^8 < 2 ^ w := (cost_power_le B 8 (by decide) (by decide)).trans_lt hbound
  apply runs_start_le
  unfold costPowersBody
  refine runs_seq_assign_le (v := B^2) ?_ ?_
  · rw [← h2]; eval_expr
  refine runs_seq_assign_le (v := B^4) ?_ ?_
  · rw [← h4]; eval_expr
  refine runs_seq_assign_le (v := B^8) ?_ ?_
  · rw [← h8]; eval_expr
  refine runs_seq_assign_le (v := B^9) ?_ ?_
  · rw [← h9]; eval_expr
  refine runs_seq_call_le hk (vs := [B^8, B^9, heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨_, _, heap, rfl⟩, hzero, hspace⟩
  · intro out memP posP hpost
    have hptr := hpost.2
    change out = heap+2 at hptr
    have hout : out < 2 ^ w := by omega
    refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
    · exact hpost
    · simp only [costPowersContract, heapContract, wordPairContract, argsSize_cons,
        argsSize_nil, Expr.size_bin, Expr.size_reg]; omega

/-- Every base has simultaneous argument, power, and allocation bounds. -/
theorem exists_costPowers_pre (B : ℕ) :
    ∃ w, (∀ a ∈ [B, 0], a < 2 ^ w) ∧
      (costPowersContract w B).pre [B, 0] (fun _ => 0) := by
  let w := B+B^9+3
  have hw : B+B^9+3 < 2 ^ w := Nat.lt_two_pow_self
  refine ⟨w, ?_, ⟨0, rfl, by omega⟩, (fun _ _ => rfl), ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> omega
  · change 0+2 < 2 ^ w
    omega

end MinCostFlow.Scaling.Machine
