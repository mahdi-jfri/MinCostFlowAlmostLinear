module

public import MinCostFlow.LSF.Program.Utils

/-!
# Writing a header from the arguments

The handle of the data structure starts with a header of fixed words (`lsfHeaderAt`), and the aux
block starts with one too (`AuxAt`). The driver computes these words and passes them as
arguments. `storeArgsStmt 0 m` stores argument `i + 1` at `base + i` for each `i < m`, where
`base` is argument `0`. The offsets `i` are fixed numbers of the program, not inputs.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow

@[expose] public section

/-- Stores registers `k + 1, …, k + m` at `base + k, …, base + k + m - 1` (register `0` is
`base`), then returns `0`. -/
def storeArgsStmt : ℕ → ℕ → Stmt
  | _, 0 => .ret (.const 0)
  | k, m + 1 => .store (.bin .add (.reg 0) (.const k)) (.reg (k + 1)) ;; storeArgsStmt (k + 1) m

lemma storeArgsStmt_noRand (k m : ℕ) : (storeArgsStmt k m).NoRand := by
  induction m generalizing k with
  | zero => simp [storeArgsStmt, Stmt.NoRand]
  | succ m ih => simp [storeArgsStmt, Stmt.NoRand, ih]

lemma storeArgs_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} (m : ℕ) :
    ∀ (k : ℕ) (st : State) (base K T : ℕ) (Q : Outcome → State → Prop),
      st.regs 0 = base → base + k + m < 2 ^ w →
      (∀ st' : State, st'.regs = st.regs → (∀ a, st'.mem a =
        if base + k ≤ a ∧ a < base + k + m then st.regs (a - base + 1) else st.mem a) →
        Q (.returned 0) st') →
      K + (6 * m + 2) ≤ T →
      ∃ o st' c, Runs w p ω (storeArgsStmt k m) st o st' c ∧ Q o st' ∧ K + c ≤ T := by
  induction m with
  | zero =>
    intro k st base K T Q _ hb hq hc
    refine runs_ret_le (v := 0) (by eval_expr) (hq st rfl fun a => ?_) (by simp; omega)
    rw [if_neg (by omega)]
  | succ m ih =>
    intro k st base K T Q h0 hb hq hc
    unfold storeArgsStmt
    have hkw : k < 2 ^ w := by omega
    refine runs_seq_store_le (x := base + k) (v := st.regs (k + 1)) (by eval_expr) (by eval_expr)
      ?_
    refine ih (k + 1) _ base _ T Q h0 (by omega) (fun st' hr hm => hq st' hr fun a => ?_)
      (by simp; omega)
    rw [hm a]
    dsimp only
    by_cases ha : a = base + k
    · subst ha
      rw [if_neg (by omega), Function.update_self, if_pos (by omega)]
      congr 1
      omega
    · rw [Function.update_of_ne ha]
      split_ifs <;> first | rfl | omega

/-- The contract of `storeArgsStmt 0 m`. -/
def storeArgsContract (w m : ℕ) : Contract where
  pre args _ := ∃ (base : ℕ) (vs : List ℕ), args = base :: vs ∧ vs.length = m ∧ base + m < 2 ^ w
  post args mem ret mem' := ∃ (base : ℕ) (vs : List ℕ), args = base :: vs ∧ ret = 0 ∧
    (∀ i < m, mem' (base + i) = vs.getD i 0) ∧ ∀ a, a < base ∨ base + m ≤ a → mem' a = mem a
  cost _ _ := 6 * m + 10

theorem storeArgs_meetsContract {w m : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some (storeArgsStmt 0 m)) :
    MeetsContract w p b (storeArgsContract w m) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨base, vs, rfl, hlen, hb⟩ := hpre
  refine runs_start_le ?_
  refine storeArgs_runs m 0 _ base 0 _ (fun o st' => (storeArgsContract w m).post (base :: vs) mem
      o.value st'.mem) (by simp [startState]) (by omega)
    (fun st' hr hm => ⟨base, vs, rfl, rfl, fun i hi => ?_, fun a ha => ?_⟩)
    (by simp only [storeArgsContract]; omega)
  · rw [hm, if_pos (by omega)]
    simp [startState, show base + i - base + 1 = i + 1 by omega]
  · rw [hm, if_neg (by omega)]
    rfl

end

end MinCostFlow.LSF.Program
