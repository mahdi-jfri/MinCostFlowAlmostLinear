module

public import MinCostFlow.LSF.Program.Utils
public import MinCostFlow.LSF.Program.DecompClosureMath

/-!
# The marks for the closure pass

The boundary of the decomposition is the LCA closure of the boundary of the root pieces and the
heavy vertices (`b7Props_of_good`). `boundary_rootPieces` describes the first set by the batch
counts `nb` and batch numbers `bidx` of the greedy pass. `decompMarkProc` writes the mark
`S x ∈ {0, 1}` of every index `x`:
* for `x ≠ r`: `S x = 1` when `x` is heavy (`θ < deg x`) or `1 ≤ nb x`;
* for the root: `S r = 1` when `r` is heavy, or `2 ≤ nb r`, or `1 ≤ nb r` and some child `c` of
  `r` has `bidx c = nb r` (then the root bag is not `{r}`).

The pass is one loop over the indices with no branch, plus one step for the root. The flag of
the last case is kept in a register. The cost is `O(n)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow

@[expose] public section

/-- The mark of a non-root index. -/
def markVal (θ nbx degx : ℕ) : ℕ := if θ < degx ∨ 0 < nbx then 1 else 0

/-- `1` when some index `x < j` other than `r` is a child of `r` with batch number `nb r`. -/
def rootFlag (par bidx nb : ℕ → ℕ) (r j : ℕ) : ℕ :=
  open Classical in if ∃ x < j, x ≠ r ∧ par x = r ∧ bidx x = nb r then 1 else 0

/-- The mark of the root. -/
def rootMarkVal (θ nbr degr f : ℕ) : ℕ := if θ < degr ∨ 1 < nbr ∨ (0 < nbr ∧ 0 < f) then 1 else 0

lemma rootFlag_zero (par bidx nb : ℕ → ℕ) (r : ℕ) : rootFlag par bidx nb r 0 = 0 := by
  simp [rootFlag]

lemma rootFlag_le (par bidx nb : ℕ → ℕ) (r j : ℕ) : rootFlag par bidx nb r j ≤ 1 := by
  unfold rootFlag; split_ifs <;> omega

lemma rootFlag_succ (par bidx nb : ℕ → ℕ) (r j : ℕ) :
    rootFlag par bidx nb r (j + 1) =
      if 0 < rootFlag par bidx nb r j + (1 - (if j = r then 1 else 0)) *
        ((if par j = r then 1 else 0) * (if bidx j = nb r then 1 else 0)) then 1 else 0 := by
  classical
  unfold rootFlag
  have hiff : (∃ x < j + 1, x ≠ r ∧ par x = r ∧ bidx x = nb r) ↔
      (∃ x < j, x ≠ r ∧ par x = r ∧ bidx x = nb r) ∨ (j ≠ r ∧ par j = r ∧ bidx j = nb r) := by
    constructor
    · rintro ⟨x, hx, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
      · exact Or.inl ⟨x, hx, h⟩
      · exact Or.inr h
    · rintro (⟨x, hx, h⟩ | h)
      · exact ⟨x, by omega, h⟩
      · exact ⟨j, by omega, h⟩
  by_cases h1 : ∃ x < j, x ≠ r ∧ par x = r ∧ bidx x = nb r
  · rw [ite_eq_left (hiff.mpr (Or.inl h1)), ite_eq_left h1]
    simp
  · rw [ite_eq_right h1, zero_add]
    by_cases h2 : j ≠ r ∧ par j = r ∧ bidx j = nb r
    · rw [ite_eq_left (hiff.mpr (Or.inr h2))]
      obtain ⟨h2a, h2b, h2c⟩ := h2
      simp [h2a, h2b, h2c]
    · have h3 : ¬ ∃ x < j + 1, x ≠ r ∧ par x = r ∧ bidx x = nb r := fun h =>
        (hiff.mp h).elim h1 h2
      rw [ite_eq_right h3]
      by_cases hjr : j = r
      · simp [hjr]
      · by_cases hp : par j = r
        · have hb : bidx j ≠ nb r := fun hb => h2 ⟨hjr, hp, hb⟩
          simp [hjr, hp, hb]
        · simp [hjr, hp]

/-- Index `x` (register `8`). Registers: `9 = [x = r]`, `10 = ` the root flag. -/
def decompMarkBody : Stmt :=
  .assign 9 (.bin .eq (.reg 8) (.reg 2)) ;;
  .store (.bin .add (.reg 7) (.reg 8))
    (.bin .lt (.const 0) (.bin .add (.bin .lt (.reg 6) (.load (.bin .add (.reg 5) (.reg 8))))
      (.bin .mul (.bin .sub (.const 1) (.reg 9))
        (.bin .lt (.const 0) (.load (.bin .add (.reg 3) (.reg 8))))))) ;;
  .assign 10 (.bin .lt (.const 0) (.bin .add (.reg 10) (.bin .mul (.bin .sub (.const 1) (.reg 9))
    (.bin .mul (.bin .eq (.load (.bin .add (.reg 1) (.reg 8))) (.reg 2))
      (.bin .eq (.load (.bin .add (.reg 4) (.reg 8))) (.load (.bin .add (.reg 3) (.reg 2))))))))

/-- Args: `[n, parPtr, r, nbPtr, bidxPtr, degPtr, θ, sPtr]`. The store after the loop is the
root step. -/
def decompMarkProc : Stmt :=
  .assign 10 (.const 0) ;;
  forRange 8 (.const 0) (.reg 0) decompMarkBody ;;
  .store (.bin .add (.reg 7) (.reg 2))
    (.bin .lt (.const 0) (.bin .add (.bin .add (.bin .lt (.reg 6) (.load (.bin .add (.reg 5) (.reg 2))))
      (.bin .lt (.const 1) (.load (.bin .add (.reg 3) (.reg 2)))))
      (.bin .mul (.bin .lt (.const 0) (.load (.bin .add (.reg 3) (.reg 2)))) (.reg 10)))) ;;
  .ret (.const 0)

lemma decompMarkProc_noRand : decompMarkProc.NoRand := by
  simp [decompMarkProc, decompMarkBody, forRange, forUp, Stmt.NoRand]

/-- The contract of `decompMarkProc`. -/
def decompMarkContract (w : ℕ) : Contract where
  pre args mem := ∃ (n parPtr r nbPtr bidxPtr degPtr θ sPtr : ℕ),
    args = [n, parPtr, r, nbPtr, bidxPtr, degPtr, θ, sPtr] ∧ 16 ≤ 2 ^ w ∧ r < n ∧
    parPtr + n ≤ sPtr ∧ nbPtr + n ≤ sPtr ∧ bidxPtr + n ≤ sPtr ∧ degPtr + n ≤ sPtr ∧
    sPtr + n < 2 ^ w
  post args mem ret mem' := ∃ (n parPtr r nbPtr bidxPtr degPtr θ sPtr : ℕ),
    args = [n, parPtr, r, nbPtr, bidxPtr, degPtr, θ, sPtr] ∧ ret = 0 ∧
    (∀ a, a < sPtr ∨ sPtr + n ≤ a → mem' a = mem a) ∧
    (∀ x < n, x ≠ r → mem' (sPtr + x) = markVal θ (mem (nbPtr + x)) (mem (degPtr + x))) ∧
    mem' (sPtr + r) = rootMarkVal θ (mem (nbPtr + r)) (mem (degPtr + r))
      (rootFlag (fun x => mem (parPtr + x)) (fun x => mem (bidxPtr + x)) (fun x => mem (nbPtr + x))
        r n)
  cost args _ := 80 * args.getD 0 0 + 80

theorem decompMark_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some decompMarkProc) :
    MeetsContract w p b (decompMarkContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, parPtr, r, nbPtr, bidxPtr, degPtr, θ, sPtr, rfl, hw, hrn, h1, h2, h3, h4, hsl⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  set args := [n, parPtr, r, nbPtr, bidxPtr, degPtr, θ, sPtr] with hargs
  set par : ℕ → ℕ := fun x => mem (parPtr + x) with hpar
  set bidx : ℕ → ℕ := fun x => mem (bidxPtr + x) with hbidx
  set nb : ℕ → ℕ := fun x => mem (nbPtr + x) with hnb
  set deg : ℕ → ℕ := fun x => mem (degPtr + x) with hdeg
  have hnw : n < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun j st =>
    (∀ i < 8, st.regs i = args.getD i 0) ∧ st.regs 8 = j ∧ st.regs 10 = rootFlag par bidx nb r j ∧
    (∀ a, a < sPtr ∨ sPtr + n ≤ a → st.mem a = mem a) ∧
    ∀ x < j, x ≠ r → st.mem (sPtr + x) = markVal θ (nb x) (deg x)
  let P : State → Prop := fun st =>
    (∀ i < 8, st.regs i = args.getD i 0) ∧ st.regs 10 = 0 ∧ st.mem = mem
  have hloop : Triple w p P (forRange 8 (.const 0) (.reg 0) decompMarkBody) (normalPost (Inv n))
      (fun _ => (n - 0) * (60 + (Expr.reg 0).size + 8) +
        ((Expr.const 0).size + (Expr.reg 0).size + 5)) := by
    refine Triple.forRange_const 60 0 n (Nat.zero_le _) hw1 (fun _ => hnw) ?_ ?_ ?_ ?_
    · rintro st ⟨hR, h10, hm⟩
      refine ⟨by eval_expr, fun i hi => ?_, by simp, ?_, fun a _ => by rw [hm], fun x hx => ?_⟩
      · simp only [Function.update_of_ne (show i ≠ 8 by omega)]; exact hR i hi
      · simp only [Function.update_of_ne (show (10 : ℕ) ≠ 8 by omega), rootFlag_zero]; exact h10
      · omega
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = n := hI.1 0 (by omega)
      eval_expr
    · intro x _ hx st ω' hI
      obtain ⟨hR, h8, h10, hfr, hS⟩ := hI
      have r1 : st.regs 1 = parPtr := hR 1 (by omega)
      have r2 : st.regs 2 = r := hR 2 (by omega)
      have r3 : st.regs 3 = nbPtr := hR 3 (by omega)
      have r4 : st.regs 4 = bidxPtr := hR 4 (by omega)
      have r5 : st.regs 5 = degPtr := hR 5 (by omega)
      have r6 : st.regs 6 = θ := hR 6 (by omega)
      have r7 : st.regs 7 = sPtr := hR 7 (by omega)
      have hmdeg : st.mem (degPtr + x) = deg x := hfr _ (Or.inl (by omega))
      have hmnb : st.mem (nbPtr + x) = nb x := hfr _ (Or.inl (by omega))
      set isR := if x = r then 1 else 0 with hisR
      have hisR_le : isR ≤ 1 := by rw [hisR]; split_ifs <;> omega
      set v := if 0 < (if θ < deg x then 1 else 0) + (1 - isR) * (if 0 < nb x then 1 else 0)
        then 1 else 0 with hv
      have hv_le : v ≤ 1 := by rw [hv]; split_ifs <;> omega
      set F := rootFlag par bidx nb r x with hF
      have hF_le : F ≤ 1 := rootFlag_le _ _ _ _ _
      have hmpar : Function.update st.mem (sPtr + x) v (parPtr + x) = par x := by
        rw [Function.update_of_ne (by omega)]; exact hfr _ (Or.inl (by omega))
      have hmbidx : Function.update st.mem (sPtr + x) v (bidxPtr + x) = bidx x := by
        rw [Function.update_of_ne (by omega)]; exact hfr _ (Or.inl (by omega))
      have hmnbr : Function.update st.mem (sPtr + x) v (nbPtr + r) = nb r := by
        rw [Function.update_of_ne (by omega)]; exact hfr _ (Or.inl (by omega))
      refine runs_start_le ?_
      unfold decompMarkBody
      refine runs_seq_assign_le (v := isR) (by rw [hisR]; eval_expr) ?_
      refine runs_seq_store_le (x := sPtr + x) (v := v) (by eval_expr) (by
        rw [hv, ← hmdeg, ← hmnb]
        have : (1 - isR) * (if 0 < st.mem (nbPtr + x) then 1 else 0) ≤ 1 := by
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hisR_le with h | h <;> rw [h] <;>
            split_ifs <;> omega
        have : (if θ < st.mem (degPtr + x) then 1 else 0) +
            (1 - isR) * (if 0 < st.mem (nbPtr + x) then 1 else 0) < 2 ^ w := by
          split_ifs <;> omega
        eval_expr) ?_
      refine runs_assign_le (v := rootFlag par bidx nb r (x + 1)) (by
        rw [rootFlag_succ, ← hF]
        have hp1 : (if par x = r then 1 else 0) * (if bidx x = nb r then 1 else 0) ≤ 1 := by
          split_ifs <;> omega
        have hp2 : (1 - isR) * ((if par x = r then 1 else 0) * (if bidx x = nb r then 1 else 0))
            ≤ 1 := by
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hisR_le with h | h <;> rw [h] <;> omega
        have : F + (1 - isR) * ((if par x = r then 1 else 0) * (if bidx x = nb r then 1 else 0))
            < 2 ^ w := by omega
        rw [← hmpar, ← hmbidx, ← hmnbr] at *
        have : (1 - if x = r then 1 else 0) *
            ((if Function.update st.mem (sPtr + x) v (parPtr + x) = r then 1 else 0) *
            (if Function.update st.mem (sPtr + x) v (bidxPtr + x) =
              Function.update st.mem (sPtr + x) v (nbPtr + r) then 1 else 0)) < 2 ^ w := by
          split_ifs <;> omega
        eval_expr) ⟨⟨fun i hi => ?_, by simpa using h8, by simp, ?_, ?_⟩, by simp [h8]⟩ ?_
      · simp only [Function.update_of_ne (show i ≠ 8 by omega),
          Function.update_of_ne (show i ≠ 10 by omega), Function.update_of_ne (show i ≠ 9 by omega)]
        exact hR i hi
      · intro a ha
        dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hfr a ha
      · intro y hy hyr
        dsimp only
        by_cases hyx : y = x
        · subst hyx
          rw [Function.update_self, hv, hisR, ite_eq_right hyr, markVal]
          simp only [Nat.sub_zero, one_mul]
          split_ifs <;> omega
        · rw [Function.update_of_ne (by omega)]; exact hS y (by omega) hyr
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
  refine runs_start_le ?_
  unfold decompMarkProc
  have hR0 : ∀ i < 8, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_triple_le hloop ⟨fun i hi => ?_, by simp, rfl⟩ ?_
  · simp only [Function.update_of_ne (show i ≠ 10 by omega)]; exact hR0 i hi
  rintro st ⟨hR, -, h10, hfr, hS⟩
  have r2 : st.regs 2 = r := hR 2 (by omega)
  have r3 : st.regs 3 = nbPtr := hR 3 (by omega)
  have r5 : st.regs 5 = degPtr := hR 5 (by omega)
  have r6 : st.regs 6 = θ := hR 6 (by omega)
  have r7 : st.regs 7 = sPtr := hR 7 (by omega)
  have hmdeg : st.mem (degPtr + r) = deg r := hfr _ (Or.inl (by omega))
  have hmnb : st.mem (nbPtr + r) = nb r := hfr _ (Or.inl (by omega))
  set F := rootFlag par bidx nb r n with hF
  have hF_le : F ≤ 1 := rootFlag_le _ _ _ _ _
  set rv := rootMarkVal θ (nb r) (deg r) F with hrv
  have hrv_le : rv ≤ 1 := by rw [hrv]; unfold rootMarkVal; split_ifs <;> omega
  refine runs_seq_store_le (x := sPtr + r) (v := rv) (by eval_expr) (by
    have heq : rv = if 0 < (if θ < st.mem (degPtr + r) then 1 else 0) +
        (if 1 < st.mem (nbPtr + r) then 1 else 0) +
        (if 0 < st.mem (nbPtr + r) then 1 else 0) * F then 1 else 0 := by
      rw [hrv, hmdeg, hmnb, rootMarkVal]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hF_le with h | h <;> rw [h] <;>
        split_ifs <;> omega
    rw [heq]
    have : (if 0 < st.mem (nbPtr + r) then 1 else 0) * F ≤ 1 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hF_le with h | h <;> rw [h] <;> split_ifs <;> omega
    have : (if θ < st.mem (degPtr + r) then 1 else 0) +
        (if 1 < st.mem (nbPtr + r) then 1 else 0) +
        (if 0 < st.mem (nbPtr + r) then 1 else 0) * F < 2 ^ w := by split_ifs <;> omega
    eval_expr) ?_
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, parPtr, r, nbPtr, bidxPtr, degPtr, θ, sPtr, rfl,
    rfl, fun a ha => ?_, fun x hx hxr => ?_, ?_⟩ ?_
  · dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a ha
  · dsimp only; rw [Function.update_of_ne (by omega)]; exact hS x hx hxr
  · dsimp only; rw [Function.update_self]
  · simp only [decompMarkContract, hargs, List.getD_cons_zero, Expr.size_const, Expr.size_reg,
      Expr.size_bin, Expr.size_load, Nat.sub_zero]
    omega

end

end MinCostFlow.LSF.Program
