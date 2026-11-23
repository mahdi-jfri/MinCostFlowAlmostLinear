module

public import MinCostFlow.HierPaths.InitSections

/-!
# Filling a short table with one word

A connector row contributes its pair number once per connector. This procedure writes
the repetitions into the next part of the pair-number column.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Write `n` copies of `word` at `dst`. -/
def initFillWord : Stmt :=
  forRange 3 (.const 0) (.reg 1) (.store (.bin .add (.reg 0) (.reg 3)) (.reg 2)) ;;
  .ret (.bin .add (.reg 0) (.reg 1))

theorem initFillWord_noRand : initFillWord.NoRand := by
  simp [initFillWord, forRange, forUp, Stmt.NoRand]

/-- The repeated word is the only change to memory. -/
def initFillWordContract (w : ℕ) : Contract where
  pre args _ := ∃ dst n word, args = [dst, n, word] ∧ dst + n < 2 ^ w ∧ 1 < 2 ^ w
  post args mem v mem' := ∃ dst n word, args = [dst, n, word] ∧ v = dst + n ∧
    ListAt mem' dst (List.replicate n word) ∧
    ∀ y, y < dst ∨ dst + n ≤ y → mem' y = mem y
  cost args _ := 15 * args.getD 1 0 + 15

theorem initFillWord_meetsContract {w j : ℕ} {p : Program}
    (hp : p.procs[j]? = some initFillWord) :
    MeetsContract w p j (initFillWordContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  obtain ⟨dst, n, word, rfl, hw, h1⟩ := hpre
  let initial := startState [dst, n, word] mem pos
  let Inv := fun i (s : State) =>
    s.regs 0 = dst ∧ s.regs 1 = n ∧ s.regs 2 = word ∧ s.regs 3 = i ∧
    (∀ j < i, s.mem (dst + j) = word) ∧ ∀ y, y < dst ∨ dst + i ≤ y → s.mem y = mem y
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 3) (lo := .const 0)
    (hi := .reg 1) (body := .store (.bin .add (.reg 0) (.reg 3)) (.reg 2))
    (P := fun s => s = initial) (Inv := Inv) 6 0 n (Nat.zero_le _) h1 (fun _ => by omega)
    (fun s hs => by
      subst s
      exact ⟨Expr.eval_const (Nat.two_pow_pos _), rfl, rfl, rfl, by simp, fun _ hj => by omega,
        fun _ _ => rfl⟩)
    (fun _ _ _ _ hI => hI.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.1)
    (fun i _ hi => by
      intro s ω ⟨r0, r1, r2, r3, hwds, hfr⟩
      refine runs_start_le ?_
      refine runs_store_le
        (Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq r3) (by omega))
        (Expr.eval_reg_of_eq r2) ?_ ?_
      · refine ⟨⟨by simpa using r0, by simpa using r1, by simpa using r2, by simp, ?_, ?_⟩, r3⟩
        · intro j hj
          change Function.update s.mem (dst + i) word (dst + j) = word
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj' | rfl
          · rw [Function.update_of_ne (by omega)]
            exact hwds _ hj'
          · exact Function.update_self ..
        · intro y hy
          change Function.update s.mem (dst + i) word y = mem y
          rw [Function.update_of_ne (by omega)]
          exact hfr _ (by omega)
      · simp [Expr.size])
  refine runs_start_le ?_
  unfold initFillWord
  refine runs_seq_triple_le hloop rfl ?_
  intro s ⟨r0, r1, _, _, hwds, hfr⟩
  refine runs_ret_le (Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq r1) hw)
    ⟨dst, n, word, rfl, rfl, ?_, hfr⟩ ?_
  · intro i hi
    have hil : i < n := by simpa using hi
    simpa using hwds i hil
  · simp [initFillWordContract, Expr.size]
    omega

end MinCostFlow.HierPaths

end
