module

public import WordRAM.Logic
public import WordRAM.Tactic

/-!
# An arithmetic index array

`iotaP` writes `IDX[i] := a · i + b` for `i < cnt` (`iotaP_spec`). The split walk leaves the
`x`-nodes of a reset child in a column of stride `3`; with `a = 3` this array lets `ncP` read
them as it reads the nodes of a raw child. Each entry costs a constant.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- `iotaP` with `args = [cnt, IDX, a, b]`. -/
def iotaP : Stmt :=
  .seq (forRange 4 (.const 0) (.reg 0)
    (.store (.bin .add (.reg 1) (.reg 4)) (.bin .add (.bin .mul (.reg 2) (.reg 4)) (.reg 3))))
  (.ret (.const 0))

theorem iotaP_noRand : iotaP.NoRand := by
  simp [iotaP, forRange, forUp, Stmt.NoRand]

/-- The contract of `iotaP`. -/
def iotaC (w : ℕ) : Contract where
  pre args _ := ∃ cnt IDX a b, args = [cnt, IDX, a, b] ∧ IDX + cnt + 1 < 2 ^ w ∧
    a * cnt + b < 2 ^ w
  post args mem _ mem' := ∀ cnt IDX a b, args = [cnt, IDX, a, b] →
    (∀ i < cnt, mem' (IDX + i) = a * i + b) ∧ ∀ x, (x < IDX ∨ IDX + cnt ≤ x) → mem' x = mem x
  cost args _ := 30 * (args.getD 0 0 + 1)

theorem iotaP_spec {w : ℕ} {p : Program} {bb : ℕ} (hp : p.HasAt bb [iotaP]) :
    MeetsContract w p bb (iotaC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨cnt, IDX, a, b, rfl, h1, h2⟩ := hpre
  have hproc : p.procs[bb]? = some iotaP := hp 0 (by simp)
  clear hp
  have hw1 : 1 < 2 ^ w := by omega
  let Done : ℕ → (ℕ → ℕ) → Prop := fun j M =>
    (∀ i < j, M (IDX + i) = a * i + b) ∧ ∀ x, (x < IDX ∨ IDX + j ≤ x) → M x = mem x
  have hloop := Triple.forRange_const (p := p) (r := 4) (lo := .const 0) (hi := .reg 0)
    (body := .store (.bin .add (.reg 1) (.reg 4)) (.bin .add (.bin .mul (.reg 2) (.reg 4)) (.reg 3)))
    (P := fun st => st = startState [cnt, IDX, a, b] mem pos)
    (Inv := fun j st => (st.regs 0 = cnt ∧ st.regs 1 = IDX ∧ st.regs 2 = a ∧ st.regs 3 = b) ∧
      st.regs 4 = j ∧ Done j st.mem)
    12 0 cnt (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, ⟨by simp [startState], by simp [startState], by simp [startState],
        by simp [startState]⟩, by simp, fun i hi => by omega, fun x _ => rfl⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.1; eval_expr)
    (fun j _ hj st ω hI => by
      obtain ⟨⟨a0, a1, a2, a3⟩, h4, hd1, hd2⟩ := hI
      have b1 : st.regs 1 + st.regs 4 < 2 ^ w := by rw [a1, h4]; omega
      have b2 : st.regs 2 * st.regs 4 + st.regs 3 < 2 ^ w := by
        rw [a2, a3, h4]
        have : a * j ≤ a * cnt := Nat.mul_le_mul_left _ hj.le
        omega
      have b3 : st.regs 2 * st.regs 4 < 2 ^ w := by omega
      have e1 : st.regs 1 + st.regs 4 = IDX + j := by rw [a1, h4]
      have e2 : st.regs 2 * st.regs 4 + st.regs 3 = a * j + b := by rw [a2, a3, h4]
      have hR : (st.regs 0 = cnt ∧ st.regs 1 = IDX ∧ st.regs 2 = a ∧ st.regs 3 = b) ∧
          st.regs 4 = j := ⟨⟨a0, a1, a2, a3⟩, h4⟩
      clear a0 a1 a2 a3 h4
      refine runs_start_le ?_
      wram_run
      all_goals try wram_cost
      refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, by simp, ?_, ?_⟩, hR.2⟩
      · simp only [Function.update_apply, ite_eq_right (show (0 : ℕ) ≠ 4 by omega)]; exact hR.1.1
      · simp only [Function.update_apply, ite_eq_right (show (1 : ℕ) ≠ 4 by omega)]; exact hR.1.2.1
      · simp only [Function.update_apply, ite_eq_right (show (2 : ℕ) ≠ 4 by omega)]; exact hR.1.2.2.1
      · simp only [Function.update_apply, ite_eq_right (show (3 : ℕ) ≠ 4 by omega)]; exact hR.1.2.2.2
      · intro i hi
        dsimp only
        rw [e1, e2]
        by_cases hij : i = j
        · subst hij; exact Function.update_self _ _ _
        · rw [Function.update_of_ne (by omega)]; exact hd1 i (by omega)
      · intro x hx
        dsimp only
        rw [e1, Function.update_of_ne (by omega)]; exact hd2 x (by omega))
  refine ⟨iotaP, hproc, ?_⟩
  dsimp only [iotaP]
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop rfl (fun st hI => ?_)
  obtain ⟨-, -, hd1, hd2⟩ := hI
  refine runs_ret_le (by eval_expr) ?_ ?_
  · intro cnt' IDX' a' b' he
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl, -⟩ := he
    exact ⟨hd1, hd2⟩
  · simp only [iotaC, Expr.size, List.getD_cons_zero] at *
    omega
