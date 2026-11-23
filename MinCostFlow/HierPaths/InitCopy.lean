module

public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.HierPaths.InitLayout

/-!
# Copying a section of the static output into the block

Some sections of the block of `Init` are sections of the static output: the owners
(`initConcrete_section_owner`). The builder writes the block above the static output, so it can
copy them word by word, front to back. `copyUp`, called with `[dst, src, n]` and
`src + n ≤ dst`, copies the words `src, …, src + n − 1` to `dst, …, dst + n − 1` and returns
`dst + n`; memory outside `[dst, dst + n)` is unchanged (`copyUp_meetsContract`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner

/-- Copy `n` words from `src` up to `dst`; return `dst + n`. -/
def copyUp : Stmt :=
  .seq (forRange 3 (.const 0) (.reg 2)
      (.store (.bin .add (.reg 0) (.reg 3)) (.load (.bin .add (.reg 1) (.reg 3)))))
    (.ret (.bin .add (.reg 0) (.reg 2)))

/-- The contract of `copyUp`. -/
def copyUpContract (w : ℕ) : Contract where
  pre args _ := ∃ dst src n, args = [dst, src, n] ∧ src + n ≤ dst ∧ dst + n < 2 ^ w ∧ 1 < 2 ^ w
  post args mem v mem' := ∃ dst src n, args = [dst, src, n] ∧ v = dst + n ∧
    (∀ i < n, mem' (dst + i) = mem (src + i)) ∧ (∀ x, x < dst ∨ dst + n ≤ x → mem' x = mem x)
  cost args _ := 17 * args.getD 2 0 + 20

/-- The copy loop. -/
theorem copyUp_triple {w dst src n : ℕ} (p : Program) (mem₀ : ℕ → ℕ)
    (hw : 1 < 2 ^ w) (hsd : src + n ≤ dst) (he : dst + n < 2 ^ w) :
    Triple w p (fun st => st.regs 0 = dst ∧ st.regs 1 = src ∧ st.regs 2 = n ∧ st.mem = mem₀)
      (forRange 3 (.const 0) (.reg 2)
        (.store (.bin .add (.reg 0) (.reg 3)) (.load (.bin .add (.reg 1) (.reg 3)))))
      (normalPost fun st' => st'.regs 0 = dst ∧ st'.regs 2 = n ∧
        (∀ j < n, st'.mem (dst + j) = mem₀ (src + j)) ∧
        (∀ x, x < dst ∨ dst + n ≤ x → st'.mem x = mem₀ x))
      (fun _ => 17 * n + 7) := by
  have hloop := Triple.forRange_const (p := p) (r := 3) (lo := .const 0) (hi := .reg 2)
    (body := .store (.bin .add (.reg 0) (.reg 3)) (.load (.bin .add (.reg 1) (.reg 3))))
    (P := fun st => st.regs 0 = dst ∧ st.regs 1 = src ∧ st.regs 2 = n ∧ st.mem = mem₀)
    (Inv := fun i st =>
      st.regs 0 = dst ∧ st.regs 1 = src ∧ st.regs 2 = n ∧ st.regs 3 = i ∧
      (∀ j < i, st.mem (dst + j) = mem₀ (src + j)) ∧
      (∀ x, x < dst ∨ dst + i ≤ x → st.mem x = mem₀ x))
    8 0 n (Nat.zero_le _) hw (fun _ => by omega)
    (fun st ⟨h0, h1, h2, hm⟩ => by
      refine ⟨by eval_expr, ?_⟩
      refine ⟨by simp [h0], by simp [h1], by simp [h2], by simp,
        fun _ hj => False.elim (Nat.not_lt_zero _ hj), fun x _ => by simp [hm]⟩)
    (fun _ st _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => by
      have h2 : st.regs 2 = n := hi.2.2.1
      eval_expr)
    (fun i _ hilt => by
      intro st ω ⟨h0, h1, h2, h3, hcopied, hframe⟩
      have hsrc_mem : st.mem (src + i) = mem₀ (src + i) := hframe (src + i) (by omega)
      refine ⟨.normal, { st with mem := Function.update st.mem (dst + i) (mem₀ (src + i)) },
        8, ?_, ?_, by simp⟩
      · refine runs_store_iff.mpr
          ⟨dst + i, mem₀ (src + i), by eval_expr, ?_, rfl, rfl, by simp⟩
        rw [← hsrc_mem]
        eval_expr
      · refine ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2,
          by simp, ?_, ?_⟩, h3⟩
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
  · intro o st' hpost
    cases o with
    | returned u => exact False.elim hpost
    | normal =>
      obtain ⟨h0, _, h2, _, hc, hf⟩ := hpost
      exact ⟨h0, h2, hc, hf⟩
  · intro _ _
    simp only [Nat.sub_zero, Expr.size_const, Expr.size_reg]
    omega

/-- **`copyUp` meets its contract.** -/
theorem copyUp_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some copyUp) :
    MeetsContract w p b (copyUpContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨dst, src, n, rfl, hsd, he, hw⟩
  refine runs_start_le ?_
  dsimp only [copyUp]
  refine runs_seq_triple_le (copyUp_triple p mem hw hsd he)
    ⟨by simp [startState], by simp [startState], by simp [startState], rfl⟩ ?_
  intro st₁ ⟨h0, h2, hc, hf⟩
  refine runs_ret_le (v := dst + n) ?_ ⟨dst, src, n, rfl, rfl, hc, hf⟩ ?_
  · eval_expr
  · simp only [copyUpContract, List.getD_cons_succ, List.getD_cons_zero, Expr.size_bin,
      Expr.size_reg]
    omega

theorem copyUp_noRand : copyUp.NoRand := by
  simp [copyUp, forRange, forUp, Stmt.NoRand]

/-- **The owner section of the block is that of the static output.** -/
theorem initConcrete_section_owner (S : StaticData) (a : ℕ) (s : PathDSAbsState) :
    (initConcrete S a s).sections.getD 1 [] = S.sections.getD 1 [] := by
  simp [HierConcrete.sections, StaticData.sections, initConcrete, StaticData.model, staticArrays,
    connSystem, StaticData.numTerm]

/-- **The owner section by `copyUp`.** If memory holds the static output at `addr`, and `mem'`
holds at `c` the `2^x` words of its owner section (what `copyUp` leaves with
`src = addr + 7 + mem (addr + 1)` and `n = 2^x`), then `mem'` holds the owner section of the
block at `c`. -/
theorem listAt_owner_of_copy {S : StaticData} {a : ℕ} {s : PathDSAbsState} {mem mem' : ℕ → ℕ}
    {addr c : ℕ} (hS : StaticOut mem addr S)
    (hcopy : ∀ i < 2 ^ S.x, mem' (c + i) = mem (addr + 7 + mem (addr + 1) + i)) :
    ListAt mem' c ((initConcrete S a s).sections.getD 1 []) := by
  rw [initConcrete_section_owner]
  have hsec := hS.section (i := 1) (by omega)
  intro i hi
  have hlen : (S.sections.getD 1 []).length = 2 ^ S.x := by
    simp [StaticData.sections, StaticData.numTerm]
  rw [hcopy i (hlen ▸ hi)]
  exact hsec i hi

end MinCostFlow.HierPaths
