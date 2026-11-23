module

public import WordRAM.Logic
public import WordRAM.Tactic

/-!
# Moving a block down

The rest of `Init` builds the block above the static output and then moves it down to the heap
pointer of `Init`. `moveDown`, called with `[h, src, e]` (`h ≤ src ≤ e`), copies the words
`src, …, e − 1` to `h, h + 1, …` (front to back, which is safe since `h ≤ src`), sets the words
from `h + (e − src)` to `e − 1` to zero, and returns `h + (e − src)`. Memory below `h` and from
`e` on is unchanged (`moveDown_meetsContract`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- `r3 := e − src`; copy `r3` words from `src` to `h`; zero `[h + r3, e)`; return `h + r3`. -/
def moveDown : Stmt :=
  .seq (.assign 3 (.bin .sub (.reg 2) (.reg 1)))
    (.seq (forRange 4 (.const 0) (.reg 3)
        (.store (.bin .add (.reg 0) (.reg 4)) (.load (.bin .add (.reg 1) (.reg 4)))))
      (.seq (forRange 5 (.bin .add (.reg 0) (.reg 3)) (.reg 2) (.store (.reg 5) (.const 0)))
        (.ret (.bin .add (.reg 0) (.reg 3)))))

/-- The contract of `moveDown`. -/
def moveDownContract (w : ℕ) : Contract where
  pre args _ := ∃ h src e, args = [h, src, e] ∧ h ≤ src ∧ src ≤ e ∧ e < 2 ^ w ∧ 1 < 2 ^ w
  post args mem v mem' := ∃ h src e, args = [h, src, e] ∧ v = h + (e - src) ∧
    (∀ i < e - src, mem' (h + i) = mem (src + i)) ∧ (∀ x < h, mem' x = mem x) ∧
    (∀ x, h + (e - src) ≤ x → x < e → mem' x = 0) ∧ (∀ x, e ≤ x → mem' x = mem x)
  cost args _ := 17 * (args.getD 2 0 - args.getD 0 0) + 40

/-- The copy loop. -/
theorem moveDown_copy_triple {w h src e : ℕ} (p : Program) (mem₀ : ℕ → ℕ)
    (hw : 1 < 2 ^ w) (hhs : h ≤ src) (hse : src ≤ e) (he : e < 2 ^ w) :
    Triple w p (fun st => st.regs 0 = h ∧ st.regs 1 = src ∧ st.regs 2 = e ∧
        st.regs 3 = e - src ∧ st.mem = mem₀)
      (forRange 4 (.const 0) (.reg 3)
        (.store (.bin .add (.reg 0) (.reg 4)) (.load (.bin .add (.reg 1) (.reg 4)))))
      (normalPost fun st' => st'.regs 0 = h ∧ st'.regs 1 = src ∧ st'.regs 2 = e ∧
        st'.regs 3 = e - src ∧
        (∀ j < e - src, st'.mem (h + j) = mem₀ (src + j)) ∧
        (∀ x, x < h ∨ h + (e - src) ≤ x → st'.mem x = mem₀ x))
      (fun _ => 17 * (e - src) + 7) := by
  have hloop := Triple.forRange_const (p := p) (r := 4) (lo := .const 0) (hi := .reg 3)
    (body := .store (.bin .add (.reg 0) (.reg 4)) (.load (.bin .add (.reg 1) (.reg 4))))
    (P := fun st => st.regs 0 = h ∧ st.regs 1 = src ∧ st.regs 2 = e ∧
        st.regs 3 = e - src ∧ st.mem = mem₀)
    (Inv := fun i st =>
      st.regs 0 = h ∧ st.regs 1 = src ∧ st.regs 2 = e ∧ st.regs 3 = e - src ∧ st.regs 4 = i ∧
      (∀ j < i, st.mem (h + j) = mem₀ (src + j)) ∧
      (∀ x, x < h ∨ h + i ≤ x → st.mem x = mem₀ x))
    8 0 (e - src) (Nat.zero_le _) hw (fun _ => by omega)
    (fun st ⟨h0, h1, h2, h3, hm⟩ => by
      refine ⟨by eval_expr, ?_⟩
      refine ⟨by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp,
        fun _ hj => False.elim (Nat.not_lt_zero _ hj), fun x _ => by simp [hm]⟩)
    (fun _ st _ _ hi => hi.2.2.2.2.1)
    (fun _ st _ _ hi => by
      have h3 : st.regs 3 = e - src := hi.2.2.2.1
      eval_expr)
    (fun i _ hilt => by
      intro st ω ⟨h0, h1, h2, h3, h4, hcopied, hframe⟩
      have hsrc_mem : st.mem (src + i) = mem₀ (src + i) := hframe (src + i) (by omega)
      refine ⟨.normal, { st with mem := Function.update st.mem (h + i) (mem₀ (src + i)) },
        8, ?_, ?_, by simp⟩
      · refine runs_store_iff.mpr
          ⟨h + i, mem₀ (src + i), by eval_expr, ?_, rfl, rfl, by simp⟩
        rw [← hsrc_mem]
        eval_expr
      · refine ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
          by simp, ?_, ?_⟩, h4⟩
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
      obtain ⟨h0, h1, h2, h3, _, hc, hf⟩ := hpost
      exact ⟨h0, h1, h2, h3, hc, hf⟩
  · intro _ _
    simp only [Nat.sub_zero, Expr.size_const, Expr.size_reg]
    omega

/-- The zero loop. -/
theorem moveDown_zero_triple {w h src e : ℕ} (p : Program) (mem₀ : ℕ → ℕ)
    (hw : 1 < 2 ^ w) (hhs : h ≤ src) (hse : src ≤ e) (he : e < 2 ^ w) :
    Triple w p (fun st => st.regs 0 = h ∧ st.regs 1 = src ∧ st.regs 2 = e ∧
        st.regs 3 = e - src ∧
        (∀ j < e - src, st.mem (h + j) = mem₀ (src + j)) ∧
        (∀ x, x < h ∨ h + (e - src) ≤ x → st.mem x = mem₀ x))
      (forRange 5 (.bin .add (.reg 0) (.reg 3)) (.reg 2) (.store (.reg 5) (.const 0)))
      (normalPost fun st' => st'.regs 0 = h ∧ st'.regs 3 = e - src ∧
        (∀ j < e - src, st'.mem (h + j) = mem₀ (src + j)) ∧ (∀ x < h, st'.mem x = mem₀ x) ∧
        (∀ x, h + (e - src) ≤ x → x < e → st'.mem x = 0) ∧ (∀ x, e ≤ x → st'.mem x = mem₀ x))
      (fun _ => 12 * (e - (h + (e - src))) + 9) := by
  have hloop := Triple.forRange_const (p := p) (r := 5) (lo := .bin .add (.reg 0) (.reg 3))
    (hi := .reg 2) (body := .store (.reg 5) (.const 0))
    (P := fun st => st.regs 0 = h ∧ st.regs 1 = src ∧ st.regs 2 = e ∧
        st.regs 3 = e - src ∧
        (∀ j < e - src, st.mem (h + j) = mem₀ (src + j)) ∧
        (∀ x, x < h ∨ h + (e - src) ≤ x → st.mem x = mem₀ x))
    (Inv := fun i st =>
      st.regs 0 = h ∧ st.regs 2 = e ∧ st.regs 3 = e - src ∧ st.regs 5 = i ∧
      (∀ j < e - src, st.mem (h + j) = mem₀ (src + j)) ∧ (∀ x < h, st.mem x = mem₀ x) ∧
      (∀ x, h + (e - src) ≤ x → x < i → st.mem x = 0) ∧ (∀ x, i ≤ x → st.mem x = mem₀ x))
    3 (h + (e - src)) e (by omega) hw (fun _ => he)
    (fun st ⟨h0, h1, h2, h3, hc, hf⟩ => by
      refine ⟨?_, ?_⟩
      · have : h + (e - src) < 2 ^ w := by omega
        eval_expr
      refine ⟨by simp [h0], by simp [h2], by simp [h3], by simp, hc,
        fun x hx => hf x (Or.inl hx), fun x h1 h2 => by omega,
        fun x hx => hf x (Or.inr hx)⟩)
    (fun _ st _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => by
      have h2 : st.regs 2 = e := hi.2.1
      eval_expr)
    (fun i hlo hilt => by
      intro st ω ⟨h0, h2, h3, h5, hc, hb, hz, hf⟩
      refine ⟨.normal, { st with mem := Function.update st.mem i 0 }, 3, ?_, ?_, by simp⟩
      · exact runs_store_iff.mpr ⟨i, 0, by eval_expr, by eval_expr, rfl, rfl, by simp⟩
      · refine ⟨⟨by simpa using h0, by simpa using h2, by simpa using h3, by simp, ?_, ?_, ?_, ?_⟩,
          h5⟩
        · intro j hj
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hc j hj
        · intro x hx
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hb x hx
        · intro x hx1 hx2
          dsimp only
          by_cases hxi : x = i
          · subst hxi; rw [Function.update_self]
          · rw [Function.update_of_ne hxi]
            exact hz x hx1 (by omega)
        · intro x hx
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hf x (by omega))
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st' hpost
    cases o with
    | returned u => exact False.elim hpost
    | normal =>
      obtain ⟨h0, _, h3, _, hc, hb, hz, hf⟩ := hpost
      exact ⟨h0, h3, hc, hb, hz, hf⟩
  · intro _ _
    simp only [Expr.size_bin, Expr.size_reg]
    omega

/-- **`moveDown` meets its contract.** -/
theorem moveDown_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some moveDown) :
    MeetsContract w p b (moveDownContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨h, src, e, rfl, hhs, hse, he, hw⟩
  refine runs_start_le ?_
  dsimp only [moveDown]
  refine runs_seq_assign_le (v := e - src) (by eval_expr) ?_
  refine runs_seq_triple_le (moveDown_copy_triple p mem hw hhs hse he)
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp, rfl⟩ ?_
  intro st₁ hst₁
  refine runs_seq_triple_le (moveDown_zero_triple p mem hw hhs hse he) hst₁ ?_
  intro st₂ ⟨h0, h3, hc, hb, hz, hf⟩
  refine runs_ret_le (v := h + (e - src)) ?_ ⟨h, src, e, rfl, rfl, hc, hb, hz, hf⟩ ?_
  · have : h + (e - src) < 2 ^ w := by omega
    eval_expr
  · simp only [moveDownContract, List.getD_cons_succ, List.getD_cons_zero, Expr.size_bin,
      Expr.size_reg]
    omega

/-- `r3 := e − src`; copy `r3` words from `src` to `h`; return `e`. -/
def copyDown : Stmt :=
  .seq (.assign 3 (.bin .sub (.reg 2) (.reg 1)))
    (.seq (forRange 4 (.const 0) (.reg 3)
        (.store (.bin .add (.reg 0) (.reg 4)) (.load (.bin .add (.reg 1) (.reg 4)))))
      (.ret (.reg 2)))

theorem copyDown_noRand : copyDown.NoRand := by
  simp [copyDown, forRange, forUp, Stmt.NoRand]

/-- The contract of `copyDown`: copies `[src, e)` down to `[h, h + (e - src))` without zeroing
the trailing gap `[h + (e - src), e)`, returning the bump pointer `e` in time `O(e - src)`. -/
def copyDownContract (w : ℕ) : Contract where
  pre args _ := ∃ h src e, args = [h, src, e] ∧ h ≤ src ∧ src ≤ e ∧ e < 2 ^ w ∧ 1 < 2 ^ w
  post args mem v mem' := ∃ h src e, args = [h, src, e] ∧ v = e ∧
    (∀ i < e - src, mem' (h + i) = mem (src + i)) ∧ (∀ x < h, mem' x = mem x) ∧
    (∀ x, e ≤ x → mem' x = mem x)
  cost args _ := 17 * (args.getD 2 0 - args.getD 1 0) + 25

/-- **`copyDown` meets its contract.** -/
theorem copyDown_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some copyDown) :
    MeetsContract w p b (copyDownContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨h, src, e, rfl, hhs, hse, he, hw⟩
  refine runs_start_le ?_
  dsimp only [copyDown]
  refine runs_seq_assign_le (v := e - src) (by eval_expr) ?_
  refine runs_seq_triple_le (moveDown_copy_triple p mem hw hhs hse he)
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp, rfl⟩ ?_
  intro st₁ ⟨_, _, h2, _, hc, hf⟩
  refine runs_ret_le (v := e) (Expr.eval_reg_of_eq h2)
    ⟨h, src, e, rfl, rfl, hc, fun x hx => hf x (Or.inl hx), fun x hx => hf x (Or.inr (by omega))⟩ ?_
  simp only [copyDownContract, List.getD_cons_succ, List.getD_cons_zero, Expr.size_bin, Expr.size_reg]
  omega

end MinCostFlow.HierPaths
