module

public import MinCostFlow.MinRatio.WireSelectHeapRebal
import WordRAM.Tactic

/-!
# One row of the select metadata table (`SelectMetaTableRow`)

The metadata table of the select state (`SelectMetaTableAt`, `SelectLevelBlocks.lean`) has eight
rows of `d + 1` words, one word per level. Each row is of one of two kinds: a copy of a solver
pointer for the levels below `d` and a fixed pointer at the levels from `d` on (the graph, the
core lengths and the active core of a level), or an affine function of the level (the caps and
the pointers into the level blocks). One procedure writes both kinds.

* `selTableRowBody` (`[dst, n, src, k, c, step]`): for `j < n`, it writes
  `mem (src + j)` to `dst + j` if `j < k`, and `c + j · step` otherwise.
* `selTableRow_meetsContract`: it meets `selTableRowContract` in `20 n + 20` steps.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Write one row of the metadata table: for `j < n` (`reg 1`), write `mem (src + j)` if `j < k`
and `c + j · step` otherwise to `dst + j`. Arguments `[dst, n, src, k, c, step]`. -/
def selTableRowBody : Stmt :=
  forRange 6 (.const 0) (.reg 1)
    (.cond (.bin .lt (.reg 6) (.reg 3))
      (.store (.bin .add (.reg 0) (.reg 6)) (.load (.bin .add (.reg 2) (.reg 6))))
      (.store (.bin .add (.reg 0) (.reg 6)) (.bin .add (.reg 4) (.bin .mul (.reg 6) (.reg 5))))) ;;
  .ret (.const 0)

theorem selTableRowBody_noRand : selTableRowBody.NoRand := by
  simp [selTableRowBody, forRange, forUp, Stmt.NoRand]

/-- The value that a row writes at position `j`. -/
def selTableRowVal (mem : ℕ → ℕ) (src k c step j : ℕ) : ℕ :=
  if j < k then mem (src + j) else c + j * step

/-- Contract of `selTableRowBody`. The words read lie off the words written, and every written
value fits in a word. -/
def selTableRowContract (w : ℕ) : Contract where
  pre args _ :=
    ∃ dst n src k c step, args = [dst, n, src, k, c, step] ∧
      1 < 2 ^ w ∧ dst + n < 2 ^ w ∧ src + k < 2 ^ w ∧ n < 2 ^ w ∧
      (∀ j < n, c + j * step < 2 ^ w) ∧
      (src + k ≤ dst ∨ dst + n ≤ src)
  post args mem ret mem' :=
    ret = 0 ∧
    (∀ j < args.getD 1 0, mem' (args.getD 0 0 + j) =
      selTableRowVal mem (args.getD 2 0) (args.getD 3 0) (args.getD 4 0) (args.getD 5 0) j) ∧
    (∀ a, (a < args.getD 0 0 ∨ args.getD 0 0 + args.getD 1 0 ≤ a) → mem' a = mem a)
  cost args _ := 30 * args.getD 1 0 + 20

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- `selTableRowBody` meets `selTableRowContract`. -/
theorem selTableRow_meetsContract {w proc : ℕ} {p : Program}
    (hp : p.procs[proc]? = some selTableRowBody) :
    MeetsContract w p proc (selTableRowContract w) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨dst, n, src, k, c, step, rfl, hw1, hdstW, hsrcW, hnW, hvalW, hdisj⟩ := hpre
  have hloop := Triple.forRange_const (p := p) (r := 6) (lo := .const 0) (hi := .reg 1)
    (body := .cond (.bin .lt (.reg 6) (.reg 3))
      (.store (.bin .add (.reg 0) (.reg 6)) (.load (.bin .add (.reg 2) (.reg 6))))
      (.store (.bin .add (.reg 0) (.reg 6)) (.bin .add (.reg 4) (.bin .mul (.reg 6) (.reg 5)))))
    (P := fun st => st = startState [dst, n, src, k, c, step] mem pos)
    (Inv := fun i st => st.regs 0 = dst ∧ st.regs 1 = n ∧ st.regs 2 = src ∧ st.regs 3 = k ∧
      st.regs 4 = c ∧ st.regs 5 = step ∧ st.regs 6 = i ∧
      (∀ j < i, st.mem (dst + j) = selTableRowVal mem src k c step j) ∧
      (∀ a, (a < dst ∨ dst + i ≤ a) → st.mem a = mem a))
    16 0 n (Nat.zero_le n) hw1 (fun _ => hnW)
    (fun st hst => by subst st; exact ⟨by eval_expr, by simp [startState]⟩)
    (fun _ _ _ _ hi => hi.2.2.2.2.2.2.1)
    (fun _ st _ _ hi => by have h1 := hi.2.1; eval_expr)
    (fun i _ hi => by
      intro st ω' hst
      rcases hst with ⟨h0, h1, h2, h3, h4, h5, h6, hdone, hout⟩
      have hiw : i < 2 ^ w := by omega
      have hdi : dst + i < 2 ^ w := by omega
      apply runs_start_le
      refine runs_cond_le (v := if i < k then 1 else 0) (by
          simp only [Expr.eval, h6, h3, BinOp.eval]
          split <;> simp [show (0 : ℕ) < 2 ^ w by omega]) ?_ ?_
      · intro hc
        have hik : i < k := by by_contra h; simp [h] at hc
        have hsi : src + i < 2 ^ w := by omega
        have hread : st.mem (src + i) = mem (src + i) := hout _ (by omega)
        refine runs_store_le (x := dst + i) (v := st.mem (src + i))
          (by simp [Expr.eval, h0, h6, BinOp.eval, hdi]) (by simp [Expr.eval, h2, h6, BinOp.eval, hsi]) ?_ ?_
        · refine ⟨⟨h0, h1, h2, h3, h4, h5, by simp, fun j hj => ?_, fun a ha => ?_⟩, h6⟩
          · dsimp only
            by_cases hji : j = i
            · subst hji; simp [hread, selTableRowVal, hik]
            · rw [Function.update_of_ne (by omega)]; exact hdone j (by omega)
          · dsimp only
            rw [Function.update_of_ne (by omega)]; exact hout a (by omega)
        · simp only [Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
      · intro hc
        have hik : ¬ i < k := by intro h; simp [h] at hc
        have hv := hvalW i hi
        have hmul : i * step < 2 ^ w := by omega
        refine runs_store_le (x := dst + i) (v := c + i * step)
          (by simp [Expr.eval, h0, h6, BinOp.eval, hdi])
          (by simp [Expr.eval, h4, h5, h6, BinOp.eval, hmul, hv]) ?_ ?_
        · refine ⟨⟨h0, h1, h2, h3, h4, h5, by simp, fun j hj => ?_, fun a ha => ?_⟩, h6⟩
          · dsimp only
            by_cases hji : j = i
            · subst hji; simp [selTableRowVal, hik]
            · rw [Function.update_of_ne (by omega)]; exact hdone j (by omega)
          · dsimp only
            rw [Function.update_of_ne (by omega)]; exact hout a (by omega)
        · simp only [Expr.size_reg, Expr.size_bin]; omega)
  apply runs_start_le
  unfold selTableRowBody
  refine runs_seq_triple_le hloop rfl ?_
  intro st1 ⟨_, _, _, _, _, _, _, hdone, hout⟩
  refine WordRAM.runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_ ?_
  · exact ⟨rfl, hdone, hout⟩
  · simp only [selTableRowContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size,
      Nat.sub_zero]
    omega

end MinCostFlow.MinRatio
