module

public import WordRAM.Logic
public import WordRAM.Tactic

/-!
# Writing one value along a list

`fillAtP`, called with `[O, L, lo, hi, val]`, writes `val` to `L + O[j]` for each `j` with
`lo ≤ j < hi` (`fillAtP_spec`). The split walk uses it to relabel the leaves of a light child:
`O` is the leaf order of the merge tree, `L` the label array, and `[lo, hi)` the interval of the
child. The cells written must not lie in `O[lo .. hi)`, so that the reads stay right. The cost is
linear in `hi - lo`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The body: `L[O[j]] := val`, with `j` in register `5`. -/
def fillAtIn : Stmt :=
  .store (.bin .add (.reg 1) (.load (.bin .add (.reg 0) (.reg 5)))) (.reg 4)

/-- `fillAtP` with `args = [O, L, lo, hi, val]`. -/
def fillAtP : Stmt :=
  .seq (forRange 5 (.reg 2) (.reg 3) fillAtIn) (.ret (.const 0))

theorem fillAtP_noRand : fillAtP.NoRand := by
  simp [fillAtP, fillAtIn, forRange, forUp, Stmt.NoRand]

/-- The cells written by `fillAtP`: `L + O[j]` for `lo ≤ j < hi`. -/
def FillHit (mem : ℕ → ℕ) (O L lo hi a : ℕ) : Prop := ∃ j, lo ≤ j ∧ j < hi ∧ a = L + mem (O + j)

/-- The contract of `fillAtP`. -/
def fillAtC (w : ℕ) : Contract where
  pre args mem := ∃ O L lo hi val, args = [O, L, lo, hi, val] ∧ 1 < 2 ^ w ∧ lo ≤ hi ∧
    O + hi < 2 ^ w ∧
    (∀ j, lo ≤ j → j < hi → L + mem (O + j) < 2 ^ w) ∧
    ∀ j j', lo ≤ j → j < hi → lo ≤ j' → j' < hi → L + mem (O + j) ≠ O + j'
  post args mem _ mem' := ∀ O L lo hi val, args = [O, L, lo, hi, val] →
    (∀ j, lo ≤ j → j < hi → mem' (L + mem (O + j)) = val) ∧
    ∀ a, ¬ FillHit mem O L lo hi a → mem' a = mem a
  cost args _ := 30 * (args.getD 3 0 - args.getD 2 0) + 20

/-- The contract of `fillAtP` holds. -/
theorem fillAtP_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [fillAtP]) :
    MeetsContract w p b (fillAtC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨O, L, lo, hi, val, rfl, hw1, hle, hO, hL, hdis⟩ := hpre
  have hproc : p.procs[b]? = some fillAtP := hp 0 (by simp)
  clear hp
  -- `R st` : the registers that never change
  let R : State → Prop := fun st => st.regs 0 = O ∧ st.regs 1 = L ∧ st.regs 2 = lo ∧
    st.regs 3 = hi ∧ st.regs 4 = val
  have Rupd : ∀ st, R st → ∀ v, R { st with regs := Function.update st.regs 5 v } := by
    intro st ⟨a0, a1, a2, a3, a4⟩ v
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Function.update_apply] <;>
      rwa [ite_eq_right (by omega)]
  -- `D M j` : the positions before `j` are written, and nothing else
  let D : (ℕ → ℕ) → ℕ → Prop := fun M j =>
    (∀ i, lo ≤ i → i < j → M (L + mem (O + i)) = val) ∧
      ∀ a, ¬ FillHit mem O L lo j a → M a = mem a
  have hloop := Triple.forRange_const (p := p) (r := 5) (lo := .reg 2) (hi := .reg 3)
    (body := fillAtIn) (P := fun st => st = startState [O, L, lo, hi, val] mem pos)
    (Inv := fun j st => R st ∧ st.regs 5 = j ∧ D st.mem j)
    20 lo hi hle hw1 (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, Rupd _ ⟨rfl, rfl, rfl, rfl, rfl⟩ _, by simp,
        fun i h1 h2 => by omega, fun a _ => rfl⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.2.2.1; eval_expr)
    (fun j hj1 hj2 st ω hI => by
      obtain ⟨hr, h5, hd⟩ := hI
      have hr' := hr
      obtain ⟨a0, a1, a2, a3, a4⟩ := hr
      have eO : st.mem (O + j) = mem (O + j) :=
        hd.2 _ fun ⟨i, hi1, hi2, he⟩ => hdis i j hi1 (by omega) hj1 hj2 he.symm
      have b1 : st.regs 0 + st.regs 5 < 2 ^ w := by rw [a0, h5]; omega
      have b2 : st.regs 1 + st.mem (st.regs 0 + st.regs 5) < 2 ^ w := by
        rw [a1, a0, h5, eO]; exact hL j hj1 hj2
      have b3 : L + st.mem (O + j) < 2 ^ w := by rw [eO]; exact hL j hj1 hj2
      refine runs_start_le ?_
      dsimp only [fillAtIn]
      wram_run
      · refine ⟨⟨Rupd _ hr' _, by simp, ?_, fun a ha => ?_⟩, h5⟩
        · intro i hi1 hi2
          dsimp only
          rw [eO]
          by_cases e : L + mem (O + i) = L + mem (O + j)
          · rw [e, Function.update_self]
          · have : i ≠ j := fun h => e (h ▸ rfl)
            rw [Function.update_of_ne e]; exact hd.1 i hi1 (by omega)
        · dsimp only
          rw [eO]
          have h1 : a ≠ L + mem (O + j) := fun he => ha ⟨j, hj1, by omega, he⟩
          rw [Function.update_of_ne h1]
          exact hd.2 a fun ⟨i, hi1, hi2, he⟩ => ha ⟨i, hi1, by omega, he⟩
      · wram_cost)
  refine ⟨fillAtP, hproc, ?_⟩
  dsimp only [fillAtP]
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop rfl (fun st hI => ?_)
  obtain ⟨-, -, hd⟩ := hI
  refine runs_ret_le (by eval_expr) ?_ ?_
  · intro O' L' lo' hi' val' he
    simp only [List.cons.injEq, and_true] at he
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
    exact hd
  · simp only [fillAtC, Expr.size, List.getD_cons_zero, List.getD_cons_succ]
    have : (hi - lo) * (20 + 1 + 8) ≤ 30 * (hi - lo) := by nlinarith
    omega

end MinCostFlow.LowStretch
