module

public import WordRAM.Logic
public import WordRAM.Tactic

/-!
# Copying a block of words

A matching in a parent host uses terminal numbers. A child game graph uses
numbers relative to its own interval. This procedure subtracts the child offset
from every endpoint in the returned matching and writes the words directly into
the child graph's edge array.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Copy parent terminal numbers to the destination, subtracting register 3. -/
def buildLocalEndsProc : Stmt :=
  .seq (forRange 4 (.const 0) (.reg 1)
      (.store (.bin .add (.reg 2) (.reg 4))
        (.bin .sub (.load (.bin .add (.reg 0) (.reg 4))) (.reg 3))))
    (.ret (.const 0))

/-- The contract of `buildLocalEndsProc`. -/
def buildLocalEndsContract (w : ℕ) : Contract where
  pre args mem := ∃ src n dst off, args = [src, n, dst, off] ∧ (src + n ≤ dst ∨ dst + n ≤ src) ∧
    src + n < 2 ^ w ∧ dst + n < 2 ^ w ∧ 1 < 2 ^ w ∧
    ∀ j < n, off ≤ mem (src + j) ∧ mem (src + j) < 2 ^ w
  post args mem _ mem' := ∃ src n dst off, args = [src, n, dst, off] ∧
    (∀ j < n, mem' (dst + j) = mem (src + j) - off) ∧
    ∀ x, (x < dst ∨ dst + n ≤ x) → mem' x = mem x
  cost args _ := 19 * args.getD 1 0 + 12

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM

private theorem localEnds_triple {w src n dst off : ℕ} (p : Program) (mem₀ : ℕ → ℕ)
    (hw : 1 < 2 ^ w) (hsd : src + n ≤ dst ∨ dst + n ≤ src)
    (hsn : src + n < 2 ^ w) (hdn : dst + n < 2 ^ w)
    (hFit : ∀ j < n, mem₀ (src + j) < 2 ^ w) :
    Triple w p (fun st => st.regs 0 = src ∧ st.regs 1 = n ∧ st.regs 2 = dst ∧ st.regs 3 = off ∧ st.mem = mem₀)
      (forRange 4 (.const 0) (.reg 1)
        (.store (.bin .add (.reg 2) (.reg 4))
        (.bin .sub (.load (.bin .add (.reg 0) (.reg 4))) (.reg 3))))
      (normalPost fun st' => (∀ j < n, st'.mem (dst + j) = mem₀ (src + j) - off) ∧
        ∀ x, (x < dst ∨ dst + n ≤ x) → st'.mem x = mem₀ x)
      (fun _ => 19 * n + 7) := by
  have hloop := Triple.forRange_const (p := p) (r := 4) (lo := .const 0) (hi := .reg 1)
    (body := .store (.bin .add (.reg 2) (.reg 4))
          (.bin .sub (.load (.bin .add (.reg 0) (.reg 4))) (.reg 3)))
    (P := fun st => st.regs 0 = src ∧ st.regs 1 = n ∧ st.regs 2 = dst ∧ st.regs 3 = off ∧ st.mem = mem₀)
    (Inv := fun i st =>
      st.regs 0 = src ∧ st.regs 1 = n ∧ st.regs 2 = dst ∧ st.regs 3 = off ∧ st.regs 4 = i ∧
      (∀ j < i, st.mem (dst + j) = mem₀ (src + j) - off) ∧
      (∀ x, (x < dst ∨ dst + i ≤ x) → st.mem x = mem₀ x))
    10 0 n (Nat.zero_le _) hw (fun _ => by omega)
    (fun st ⟨h0, h1, h2, hOff, hm⟩ => by
      refine ⟨by eval_expr, ?_⟩
      exact ⟨by simp [h0], by simp [h1], by simp [h2], by simp [hOff], by simp,
        fun _ hj => False.elim (Nat.not_lt_zero _ hj), fun x _ => by simp [hm]⟩)
    (fun _ st _ _ hi => hi.2.2.2.2.1)
    (fun _ st _ _ hi => by
      have h1 : st.regs 1 = n := hi.2.1
      simp [Expr.eval, h1])
    (fun i _ hilt => by
      intro st ω ⟨h0, h1, h2, hOff, h3, hz, hf⟩
      have hsi : st.mem (src + i) = mem₀ (src + i) := hf _ (by omega)
      refine ⟨.normal, { st with mem := Function.update st.mem (dst + i) (mem₀ (src + i) - off) },
        10, ?_, ?_, by simp⟩
      · have hsw : src + i < 2 ^ w := by omega
        have hdw : dst + i < 2 ^ w := by omega
        refine runs_store_iff.mpr ⟨dst + i, mem₀ (src + i) - off, ?_, ?_, rfl, rfl, by simp⟩
        · simp [Expr.eval, h2, h3, hdw]
        · have hiFit := (Nat.sub_le (mem₀ (src + i)) off).trans_lt (hFit i hilt)
          simp [Expr.eval, h0, h3, hOff, hsw, hsi, hiFit]
      · refine ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using hOff, by simp, ?_, ?_⟩, h3⟩
        · intro j hj
          dsimp only
          by_cases hji : j = i
          · rw [hji, Function.update_self]
          · rw [Function.update_of_ne (by omega)]
            exact hz j (by omega)
        · intro x hx
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hf x (by omega))
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st' hpost
    cases o with
    | returned u => exact False.elim hpost
    | normal =>
      obtain ⟨_, _, _, _, _, hz, hf⟩ := hpost
      exact ⟨hz, hf⟩
  · intro _ _
    simp only [Nat.sub_zero, Expr.size_const, Expr.size_reg]
    omega

/-- **`buildLocalEndsProc` meets its contract.** -/
theorem buildLocalEndsProc_meetsContract {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some buildLocalEndsProc) :
    MeetsContract w p f (buildLocalEndsContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨src, n, dst, off, rfl, hsd, hsn, hdn, hw, hFit⟩
  refine runs_start_le ?_
  dsimp only [buildLocalEndsProc]
  refine runs_seq_triple_le (localEnds_triple (off := off) p mem hw hsd hsn hdn (fun i hi => (hFit i hi).2))
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState], rfl⟩ ?_
  intro st₁ ⟨hz, hf⟩
  refine runs_ret_le (v := 0) ?_ ⟨src, n, dst, off, rfl, hz, hf⟩ ?_
  · eval_expr
  · simp only [buildLocalEndsContract, List.getD_cons_succ, List.getD_cons_zero, Expr.size_const]
    omega

end MinCostFlow.HierPaths
