module

public import WordRAM.CopyWords

/-!
# Copying the final answer to address zero

The answer pointer may lie inside the input range. Copying forward is
safe whenever the destination starts no later than the source: every
write is behind the next unread source cell. This proves the library's
copy procedure under that weaker ordering condition. Its linear cost is
unchanged, including when the source and destination coincide.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- A forward copy permits overlapping ranges when the destination
starts no later than the source. -/
def forwardCopyWordsContract (w : ℕ) : Contract :=
  { copyWordsContract w with
    pre := fun args _ => ∃ src dst len,args=[src,dst,len] ∧ 1<2^w ∧
      src+len≤2^w ∧ dst+len≤2^w ∧ dst≤src }

/-- Hoare triple for the copy loop inside `copyWords`. -/
theorem forwardCopyWordsLoop_triple {w src dst len : ℕ} (p : Program) (mem₀ : ℕ → ℕ) (pos : ℕ)
    (hw : 1 < 2 ^ w) (hlen : len < 2 ^ w)
    (hsrc : src + len ≤ 2 ^ w) (_hdst : dst + len ≤ 2 ^ w)
    (hnov : dst ≤ src) :
    Triple w p (fun st => st = startState [src, dst, len] mem₀ pos)
      (forRange 3 (.const 0) (.reg 2)
        (.store (.bin .add (.reg 1) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3)))))
      (normalPost fun st' =>
        (∀ i < len, st'.mem (dst + i) = mem₀ (src + i)) ∧
        (∀ x, x < dst ∨ dst + len ≤ x → st'.mem x = mem₀ x))
      (fun _ => 17 * len + 7) := by
  have hloop := Triple.forRange_const (p := p) (r := 3) (lo := .const 0) (hi := .reg 2)
    (body := .store (.bin .add (.reg 1) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3))))
    (P := fun st => st = startState [src, dst, len] mem₀ pos)
    (Inv := fun i st =>
      st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = len ∧ st.regs 3 = i ∧
      (∀ j < i, st.mem (dst + j) = mem₀ (src + j)) ∧
      (∀ x, x < dst ∨ dst + i ≤ x → st.mem x = mem₀ x))
    8 0 len (Nat.zero_le len) hw (fun _ => hlen)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, ?_, ?_, ?_, ?_, fun _ h => False.elim (Nat.not_lt_zero _ h),
        fun _ _ => rfl⟩ <;> simp [startState])
    (fun _ st _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => by
      have h2 : st.regs 2 = len := hi.2.2.1
      eval_expr)
    (fun i _ hilt => by
      intro st ω ⟨h0, h1, h2, h3, hcopied, hframe⟩
      have hsrc_word : src + i < 2 ^ w := by omega
      have hdst_word : dst + i < 2 ^ w := by omega
      have hsrc_mem : st.mem (src + i) = mem₀ (src + i) := hframe (src + i) (by omega)
      refine ⟨.normal, { st with mem := Function.update st.mem (dst + i) (mem₀ (src + i)) },
        8, ?_, ?_, by simp⟩
      · refine runs_store_iff.mpr
          ⟨dst + i, mem₀ (src + i), by eval_expr, ?_, rfl, rfl, by simp⟩
        rw [← hsrc_mem]
        eval_expr
      · refine ⟨⟨h0, h1, h2, by simp, ?_, ?_⟩, h3⟩
        · intro j hj
          dsimp only
          by_cases hji : j = i
          · subst hji
            rw [Function.update_self]
          · rw [Function.update_of_ne (by omega)]
            exact hcopied j (by omega)
        · intro x hx
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hframe x (by omega))
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st' h
    cases o with
    | returned u => exact False.elim h
    | normal => exact h.2.2.2.2
  · intro _ _
    simp only [Nat.sub_zero, Expr.size_const, Expr.size_reg]
    omega

/-- `copyWords` placed at index `b` in `p` meets `forwardCopyWordsContract w`. -/
theorem forwardCopyWords_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b [copyWords]) :
    MeetsContract w p b (forwardCopyWordsContract w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨src, dst, len, rfl, hw, hsrc, hdst, hnov⟩
  have hlen : len < 2 ^ w := hwords len (by simp)
  refine runs_start_le ?_
  dsimp only [copyWords]
  refine runs_seq_triple_le (forwardCopyWordsLoop_triple p mem pos hw hlen hsrc hdst hnov) rfl ?_
  intro st₁ ⟨hcopied, hframe⟩
  refine runs_ret_le (by eval_expr) ⟨src, dst, len, rfl, rfl, hcopied, hframe⟩ ?_
  dsimp [forwardCopyWordsContract,copyWordsContract]
  omega

end MinCostFlow.Scaling.Machine
