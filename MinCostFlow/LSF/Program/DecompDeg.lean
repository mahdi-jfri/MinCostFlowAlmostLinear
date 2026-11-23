module

public import MinCostFlow.LSF.Program.Utils
public import MinCostFlow.LSF.Program.DecompBridge

/-!
# The degree pass of the tree decomposition

For unit weights, the weight `vWeight G₀ 1 v` of a vertex is its degree (a self-loop counts
twice). `decompDegProc` counts, for every vertex index `x < n`, how many of the endpoint indices
`eu t`, `ev t` (`t < m0`, from `endpointIdxProc`) equal `x` (`degCount`). It then writes the
weight used by the decomposition: `0` when the degree is above `θ` (a heavy vertex), and the
degree otherwise. The cost is `O(m0 + n)`. `degCount_eq_vWeight` shows that the count is the
degree.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF

@[expose] public section

/-- The number of endpoints of the first `t` listed edges with index `x`. -/
def degCount (eu ev : ℕ → ℕ) (t x : ℕ) : ℕ :=
  ((Finset.range t).filter (fun i => eu i = x)).card +
    ((Finset.range t).filter (fun i => ev i = x)).card

lemma degCount_zero (eu ev : ℕ → ℕ) (x : ℕ) : degCount eu ev 0 x = 0 := by
  simp [degCount]

lemma degCount_succ (eu ev : ℕ → ℕ) (t x : ℕ) :
    degCount eu ev (t + 1) x =
      degCount eu ev t x + (if eu t = x then 1 else 0) + (if ev t = x then 1 else 0) := by
  unfold degCount
  rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert]
  have h1 : t ∉ (Finset.range t).filter (fun i => eu i = x) := by simp
  have h2 : t ∉ (Finset.range t).filter (fun i => ev i = x) := by simp
  split_ifs with ha hb hb <;>
    (try simp only [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2]) <;> omega

lemma degCount_le (eu ev : ℕ → ℕ) (t x : ℕ) : degCount eu ev t x ≤ 2 * t := by
  unfold degCount
  have h1 := Finset.card_filter_le (Finset.range t) (fun i => eu i = x)
  have h2 := Finset.card_filter_le (Finset.range t) (fun i => ev i = x)
  simp only [Finset.card_range] at h1 h2
  omega

/-- The weight of the decomposition: the degree, or `0` above `θ`. -/
def degNu (θ d : ℕ) : ℕ := if θ < d then 0 else d

/-- Edge `t` (register `7`): add one at both endpoint indices. -/
def decompDegBody1 : Stmt :=
  .assign 9 (.load (.bin .add (.reg 1) (.reg 7))) ;;
  .store (.bin .add (.reg 5) (.reg 9)) (.bin .add (.load (.bin .add (.reg 5) (.reg 9))) (.const 1)) ;;
  .assign 10 (.load (.bin .add (.reg 2) (.reg 7))) ;;
  .store (.bin .add (.reg 5) (.reg 10))
    (.bin .add (.load (.bin .add (.reg 5) (.reg 10))) (.const 1))

/-- Index `x` (register `8`): write `[d ≤ θ] d`. -/
def decompDegBody2 : Stmt :=
  .assign 9 (.load (.bin .add (.reg 5) (.reg 8))) ;;
  .store (.bin .add (.reg 6) (.reg 8))
    (.bin .mul (.bin .sub (.const 1) (.bin .lt (.reg 4) (.reg 9))) (.reg 9))

/-- Args: `[m0, euPtr, evPtr, n, θ, degPtr, nuPtr]`. -/
def decompDegProc : Stmt :=
  forRange 7 (.const 0) (.reg 0) decompDegBody1 ;;
  forRange 8 (.const 0) (.reg 3) decompDegBody2 ;;
  .ret (.const 0)

lemma decompDegProc_noRand : decompDegProc.NoRand := by
  simp [decompDegProc, decompDegBody1, decompDegBody2, forRange, forUp, Stmt.NoRand]

/-- The contract of `decompDegProc`. The count array `deg` starts at `0`. -/
def decompDegContract (w : ℕ) : Contract where
  pre args mem := ∃ (m0 euPtr evPtr n θ degPtr nuPtr : ℕ),
    args = [m0, euPtr, evPtr, n, θ, degPtr, nuPtr] ∧ 16 ≤ 2 ^ w ∧ 2 * m0 < 2 ^ w ∧
    euPtr + m0 ≤ degPtr ∧ evPtr + m0 ≤ degPtr ∧ degPtr + n ≤ nuPtr ∧ nuPtr + n < 2 ^ w ∧
    (∀ t < m0, mem (euPtr + t) < n ∧ mem (evPtr + t) < n) ∧ (∀ x < n, mem (degPtr + x) = 0)
  post args mem ret mem' := ∃ (m0 euPtr evPtr n θ degPtr nuPtr : ℕ),
    args = [m0, euPtr, evPtr, n, θ, degPtr, nuPtr] ∧ ret = 0 ∧
    (∀ a, a < degPtr ∨ nuPtr + n ≤ a → mem' a = mem a) ∧
    ∀ x < n, mem' (degPtr + x) = degCount (fun t => mem (euPtr + t)) (fun t => mem (evPtr + t)) m0 x ∧
      mem' (nuPtr + x) =
        degNu θ (degCount (fun t => mem (euPtr + t)) (fun t => mem (evPtr + t)) m0 x)
  cost args _ := 60 * args.getD 0 0 + 40 * args.getD 3 0 + 40

theorem decompDeg_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some decompDegProc) :
    MeetsContract w p b (decompDegContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨m0, euPtr, evPtr, n, θ, degPtr, nuPtr, rfl, hw, hm0, h1, h2, h3, h4, hlt, hz⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  set args := [m0, euPtr, evPtr, n, θ, degPtr, nuPtr] with hargs
  set eu : ℕ → ℕ := fun t => mem (euPtr + t) with heu
  set ev : ℕ → ℕ := fun t => mem (evPtr + t) with hev
  have hθw : θ < 2 ^ w := hwords θ (by simp [hargs])
  let Inv1 : ℕ → State → Prop := fun j st =>
    (∀ i < 7, st.regs i = args.getD i 0) ∧ st.regs 7 = j ∧
    (∀ a, a < degPtr ∨ nuPtr + n ≤ a → st.mem a = mem a) ∧
    ∀ x < n, st.mem (degPtr + x) = degCount eu ev j x
  have hloop1 : Triple w p (fun st => st = startState args mem pos)
      (forRange 7 (.const 0) (.reg 0) decompDegBody1) (normalPost (Inv1 m0))
      (fun _ => (m0 - 0) * (40 + (Expr.reg 0).size + 8) +
        ((Expr.const 0).size + (Expr.reg 0).size + 5)) := by
    refine Triple.forRange_const 40 0 m0 (Nat.zero_le _) hw1 (fun _ => by omega) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, fun i hi => ?_, by simp, fun a _ => rfl, fun x hx => ?_⟩
      · simp only [Function.update_of_ne (show i ≠ 7 by omega)]
        interval_cases i <;> simp [startState, hargs]
      · rw [degCount_zero]; exact hz x hx
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = m0 := hI.1 0 (by omega)
      eval_expr
    · intro t _ ht st ω' hI
      obtain ⟨hR, h7, hfr, hD⟩ := hI
      have r1 : st.regs 1 = euPtr := hR 1 (by omega)
      have r2 : st.regs 2 = evPtr := hR 2 (by omega)
      have r5 : st.regs 5 = degPtr := hR 5 (by omega)
      obtain ⟨hut, hvt⟩ := hlt t ht
      have hut' : eu t < n := hut
      have hvt' : ev t < n := hvt
      have hmu : st.mem (euPtr + t) = eu t := hfr _ (Or.inl (by omega))
      have hmv : st.mem (evPtr + t) = ev t := hfr _ (Or.inl (by omega))
      have hdu : st.mem (degPtr + eu t) = degCount eu ev t (eu t) := hD _ hut
      have hle1 := degCount_le eu ev t (eu t)
      set d1 := degCount eu ev t (eu t) with hd1
      have hm1v : Function.update st.mem (degPtr + eu t) (d1 + 1) (degPtr + ev t) =
          degCount eu ev t (ev t) + (if eu t = ev t then 1 else 0) := by
        by_cases he : eu t = ev t
        · rw [← he, Function.update_self, ite_eq_left rfl]
        · rw [Function.update_of_ne (by omega), ite_eq_right he, add_zero, hD _ hvt]
      have hle2 := degCount_le eu ev t (ev t)
      set d2 := degCount eu ev t (ev t) + (if eu t = ev t then 1 else 0) with hd2
      have hd2le : d2 ≤ 2 * t + 1 := by rw [hd2]; split_ifs <;> omega
      refine runs_start_le ?_
      unfold decompDegBody1
      refine runs_seq_assign_le (v := eu t) (by rw [← hmu]; eval_expr) ?_
      refine runs_seq_store_le (x := degPtr + eu t) (v := d1 + 1) (by eval_expr)
        (by rw [← hdu]; eval_expr) ?_
      refine runs_seq_assign_le (v := ev t) (by
        have : Function.update st.mem (degPtr + eu t) (d1 + 1) (evPtr + t) = ev t := by
          rw [Function.update_of_ne (by omega)]; exact hmv
        eval_expr) ?_
      refine runs_store_le (x := degPtr + ev t) (v := d2 + 1) (by eval_expr)
        (by eval_expr) ⟨⟨fun i hi => ?_, by simp, ?_, ?_⟩, by simpa using h7⟩ ?_
      · simp only [Function.update_of_ne (show i ≠ 7 by omega),
          Function.update_of_ne (show i ≠ 9 by omega), Function.update_of_ne (show i ≠ 10 by omega)]
        exact hR i hi
      · intro a ha
        dsimp only
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hfr a ha
      · intro x hx
        dsimp only
        rw [degCount_succ]
        by_cases hxv : ev t = x
        · subst hxv
          rw [Function.update_self, hd2, ite_eq_left rfl]
        · rw [Function.update_of_ne (by omega), ite_eq_right hxv, add_zero]
          by_cases hxu : eu t = x
          · subst hxu; rw [Function.update_self, ite_eq_left rfl]
          · rw [Function.update_of_ne (by omega), ite_eq_right hxu, add_zero, hD x hx]
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
  let Inv2 : ℕ → State → Prop := fun j st =>
    (∀ i < 7, st.regs i = args.getD i 0) ∧ st.regs 8 = j ∧
    (∀ a, a < degPtr ∨ nuPtr + n ≤ a → st.mem a = mem a) ∧
    (∀ x < n, st.mem (degPtr + x) = degCount eu ev m0 x) ∧
    ∀ x < j, st.mem (nuPtr + x) = degNu θ (degCount eu ev m0 x)
  have hloop2 : Triple w p (Inv1 m0)
      (forRange 8 (.const 0) (.reg 3) decompDegBody2) (normalPost (Inv2 n))
      (fun _ => (n - 0) * (30 + (Expr.reg 3).size + 8) +
        ((Expr.const 0).size + (Expr.reg 3).size + 5)) := by
    have hnw : n < 2 ^ w := by omega
    refine Triple.forRange_const 30 0 n (Nat.zero_le _) hw1 (fun _ => hnw) ?_ ?_ ?_ ?_
    · rintro st ⟨hR, -, hfr, hD⟩
      refine ⟨by eval_expr, fun i hi => ?_, by simp, hfr, hD, fun x hx => absurd hx (by omega)⟩
      simp only [Function.update_of_ne (show i ≠ 8 by omega)]
      exact hR i hi
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r3 : st.regs 3 = n := hI.1 3 (by omega)
      eval_expr
    · intro x _ hx st ω' hI
      obtain ⟨hR, h8, hfr, hD, hN⟩ := hI
      have r4 : st.regs 4 = θ := hR 4 (by omega)
      have r5 : st.regs 5 = degPtr := hR 5 (by omega)
      have r6 : st.regs 6 = nuPtr := hR 6 (by omega)
      have hdx := hD x hx
      have hle := degCount_le eu ev m0 x
      set d := degCount eu ev m0 x with hd
      refine runs_start_le ?_
      unfold decompDegBody2
      refine runs_seq_assign_le (v := d) (by rw [← hdx]; eval_expr) ?_
      refine runs_store_le (x := nuPtr + x) (v := degNu θ d) (by eval_expr) (by
        have : (1 - (if θ < d then 1 else 0)) * d = degNu θ d := by
          unfold degNu; split_ifs <;> simp
        rw [← this]
        have : (1 - (if θ < d then 1 else 0)) * d ≤ d := by split_ifs <;> simp
        eval_expr) ⟨⟨fun i hi => ?_, by simpa using h8, ?_, ?_, ?_⟩, by simpa using h8⟩ ?_
      · simp only [Function.update_of_ne (show i ≠ 8 by omega),
          Function.update_of_ne (show i ≠ 9 by omega)]
        exact hR i hi
      · intro a ha
        dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hfr a ha
      · intro y hy
        dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hD y hy
      · intro y hy
        dsimp only
        by_cases hyx : y = x
        · subst hyx; rw [Function.update_self]
        · rw [Function.update_of_ne (by omega)]; exact hN y (by omega)
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
  refine runs_start_le ?_
  unfold decompDegProc
  refine runs_seq_triple_le hloop1 rfl ?_
  intro st1 hI1
  refine runs_seq_triple_le hloop2 hI1 ?_
  rintro st ⟨-, -, hfr, hD, hN⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨m0, euPtr, evPtr, n, θ, degPtr, nuPtr, rfl, rfl,
    hfr, fun x hx => ⟨hD x hx, hN x hx⟩⟩ ?_
  simp only [decompDegContract, hargs, List.getD_cons_zero, List.getD_cons_succ, Expr.size_const,
    Expr.size_reg, Nat.sub_zero]
  omega

end

end MinCostFlow.LSF.Program
