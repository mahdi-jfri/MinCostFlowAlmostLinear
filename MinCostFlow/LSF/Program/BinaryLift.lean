module

public import MinCostFlow.LSF.Program.Utils
public import WordRAM.Tactic
import Mathlib.Tactic.Linarith

/-!
# Binary lifting: the ancestor table

To find ancestors and lowest common ancestors fast, the LSF stores for each vertex index `i` and
each level `j < logCap` the ancestor `2^j` steps up (`upV` in `AuxAt`). Level `0` is the parent,
and level `j + 1` is level `j` applied twice. `liftF par i j` is this table as a function, and
`liftF_eq_iterate` shows that it is the `2^j`-th iterate of the parent map.

`upVProc` fills the table at `upPtr + (i * logCap + j)`, level by level, in time
`O(n · logCap)` (`upV_meetsContract`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM

@[expose] public section

/-! ## The table as a function -/

/-- The ancestor of `i` at distance `2^j` along `par`. -/
def liftF (par : ℕ → ℕ) (i : ℕ) : ℕ → ℕ
  | 0 => par i
  | j + 1 => liftF par (liftF par i j) j

lemma liftF_eq_iterate (par : ℕ → ℕ) (j : ℕ) : ∀ i, liftF par i j = par^[2 ^ j] i := by
  induction j with
  | zero => intro i; simp [liftF]
  | succ j ih =>
    intro i
    rw [liftF, ih, ih, ← Function.iterate_add_apply, pow_succ]
    congr 1
    ring

lemma liftF_lt {par : ℕ → ℕ} {n : ℕ} (hpar : ∀ x < n, par x < n) (j : ℕ) :
    ∀ i < n, liftF par i j < n := by
  induction j with
  | zero => intro i hi; exact hpar i hi
  | succ j ih => intro i hi; exact ih _ (ih i hi)

/-! ## The procedure -/

/-- Level `0`: `up[i * logCap] = par[i]`, for `i` in register `5`. -/
def upV0Body : Stmt :=
  .store (.bin .add (.reg 3) (.bin .mul (.reg 5) (.reg 1))) (.load (.bin .add (.reg 2) (.reg 5)))

/-- Level `j + 1` (register `4` is `j`) at `i` (register `5`). -/
def upVStepBody : Stmt :=
  .assign 6 (.load (.bin .add (.reg 3) (.bin .add (.bin .mul (.reg 5) (.reg 1)) (.reg 4)))) ;;
  .assign 7 (.load (.bin .add (.reg 3) (.bin .add (.bin .mul (.reg 6) (.reg 1)) (.reg 4)))) ;;
  .store (.bin .add (.reg 3) (.bin .add (.bin .add (.bin .mul (.reg 5) (.reg 1)) (.reg 4))
    (.const 1))) (.reg 7)

/-- Args: `[n, logCap, parPtr, upPtr]`. -/
def upVProc : Stmt :=
  forRange 5 (.const 0) (.reg 0) upV0Body ;;
  forRange 4 (.const 0) (.bin .sub (.reg 1) (.const 1)) (forRange 5 (.const 0) (.reg 0) upVStepBody) ;;
  .ret (.const 0)

lemma upVProc_noRand : upVProc.NoRand := by
  simp [upVProc, upV0Body, upVStepBody, forRange, forUp, Stmt.NoRand]

/-- The contract of `upVProc`. -/
def upVContract (w : ℕ) : Contract where
  pre args mem := ∃ (n logCap parPtr upPtr : ℕ),
    args = [n, logCap, parPtr, upPtr] ∧ 16 ≤ 2 ^ w ∧ 1 ≤ logCap ∧
    (∀ i < n, mem (parPtr + i) < n) ∧ parPtr + n ≤ upPtr ∧ upPtr + n * logCap < 2 ^ w
  post args mem ret mem' := ∃ (n logCap parPtr upPtr : ℕ),
    args = [n, logCap, parPtr, upPtr] ∧ ret = 0 ∧
    (∀ i < n, ∀ j < logCap,
      mem' (upPtr + (i * logCap + j)) = liftF (fun x => mem (parPtr + x)) i j) ∧
    ∀ a, a < upPtr ∨ upPtr + n * logCap ≤ a → mem' a = mem a
  cost args _ := 60 * args.getD 0 0 * args.getD 1 0 + 40 * args.getD 1 0 + 40

/-! ## Proof -/

private lemma idx_lt {i j n L : ℕ} (hi : i < n) (hj : j < L) : i * L + j < n * L := by
  have : (i + 1) * L ≤ n * L := Nat.mul_le_mul_right _ hi
  nlinarith

private lemma idx_inj {a b c d L : ℕ} (hb : b < L) (hd : d < L) (h : a * L + b = c * L + d) :
    a = c ∧ b = d := by
  have hL : 0 < L := by omega
  have h1 : (a * L + b) / L = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hb, Nat.zero_add]
  have h2 : (c * L + d) / L = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hd, Nat.zero_add]
  have hac : a = c := by rw [← h1, ← h2, h]
  subst hac
  omega

/-- The argument registers `0, …, 3`. -/
def UpRegs (st : State) (n logCap parPtr upPtr : ℕ) : Prop :=
  st.regs 0 = n ∧ st.regs 1 = logCap ∧ st.regs 2 = parPtr ∧ st.regs 3 = upPtr

lemma UpRegs.upd {st : State} {n logCap parPtr upPtr : ℕ}
    (h : UpRegs st n logCap parPtr upPtr) (q v : ℕ) (hq : 4 ≤ q) :
    UpRegs { st with regs := Function.update st.regs q v } n logCap parPtr upPtr := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [UpRegs, Function.update_of_ne (show (0 : ℕ) ≠ q by omega),
    Function.update_of_ne (show (1 : ℕ) ≠ q by omega),
    Function.update_of_ne (show (2 : ℕ) ≠ q by omega),
    Function.update_of_ne (show (3 : ℕ) ≠ q by omega)]
  exact ⟨h0, h1, h2, h3⟩

theorem upV_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some upVProc) :
    MeetsContract w p b (upVContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, L, parPtr, upPtr, rfl, hw, hL, hpar, hlay, hword⟩ := hpre
  have hnw : n < 2 ^ w := hwords n (by simp)
  have hLw : L < 2 ^ w := hwords L (by simp)
  have hw1 : 1 < 2 ^ w := by omega
  set P : ℕ → ℕ := fun x => mem (parPtr + x) with hP
  have hPlt : ∀ x < n, P x < n := hpar
  let Frame : (ℕ → ℕ) → Prop := fun m => ∀ a, a < upPtr ∨ upPtr + n * L ≤ a → m a = mem a
  -- level `0`
  let Inv0 : ℕ → State → Prop := fun i st =>
    UpRegs st n L parPtr upPtr ∧ st.regs 5 = i ∧ Frame st.mem ∧
    ∀ i' < i, st.mem (upPtr + (i' * L + 0)) = liftF P i' 0
  have hloop0 : Triple w p (fun st => st = startState [n, L, parPtr, upPtr] mem pos)
      (forRange 5 (.const 0) (.reg 0) upV0Body) (normalPost (Inv0 n))
      (fun _ => n * (20 + Expr.size (.reg 0) + 8) + (Expr.size (.const 0) +
        Expr.size (.reg 0) + 5)) := by
    refine Triple.forRange_const 20 0 n (Nat.zero_le _) hw1 (fun _ => hnw) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, ⟨by simp [startState], by simp [startState], by simp [startState],
        by simp [startState]⟩, by simp, fun _ _ => rfl,
        fun i hi => absurd hi (by omega)⟩
    · intro i st _ _ h; exact h.2.1
    · intro i st _ _ h; have := h.1.1; eval_expr
    · intro i _ hi st ω' ⟨hR, h5, hfr, hdone⟩
      obtain ⟨r0, r1, r2, r3⟩ := hR
      have hidx := idx_lt (j := 0) hi hL
      have hPi : st.mem (parPtr + i) = P i := hfr _ (Or.inl (by omega))
      refine runs_start_le ?_
      unfold upV0Body
      refine runs_store_le (x := upPtr + i * L) (v := P i) (by eval_expr) (by
        rw [← hPi]; eval_expr) ⟨⟨(UpRegs.upd ⟨r0, r1, r2, r3⟩ 5 (i + 1) (by omega)), by simp,
          ?_, ?_⟩, h5⟩ ?_
      · intro a ha
        simp only
        rw [Function.update_of_ne (by omega)]
        exact hfr a ha
      · intro i' hi'
        simp only [Nat.add_zero]
        by_cases hii : i' = i
        · subst hii; rw [Function.update_self]; rfl
        · rw [Function.update_of_ne (by
            intro h
            have := idx_inj (b := 0) (d := 0) (by omega) (by omega)
              (show i' * L + 0 = i * L + 0 by omega)
            omega)]
          simpa using hdone i' (by omega)
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
  -- levels `j + 1`, one pass over all `i` for each `j < L - 1`
  let InvJ : ℕ → State → Prop := fun j st =>
    UpRegs st n L parPtr upPtr ∧ st.regs 4 = j ∧ Frame st.mem ∧
    ∀ i' < n, ∀ j' ≤ j, st.mem (upPtr + (i' * L + j')) = liftF P i' j'
  let InvI : ℕ → ℕ → State → Prop := fun j i st =>
    UpRegs st n L parPtr upPtr ∧ st.regs 4 = j ∧ st.regs 5 = i ∧ Frame st.mem ∧
    (∀ i' < n, ∀ j' ≤ j, st.mem (upPtr + (i' * L + j')) = liftF P i' j') ∧
    ∀ i' < i, st.mem (upPtr + (i' * L + (j + 1))) = liftF P i' (j + 1)
  have hinner : ∀ j, j < L - 1 → Triple w p (InvJ j) (forRange 5 (.const 0) (.reg 0) upVStepBody)
      (normalPost fun st₁ =>
        InvJ (j + 1) { st₁ with regs := Function.update st₁.regs 4 (j + 1) } ∧ st₁.regs 4 = j)
      (fun _ => n * (40 + Expr.size (.reg 0) + 8) + (Expr.size (.const 0) +
        Expr.size (.reg 0) + 5)) := by
    intro j hj
    refine (Triple.forRange_const (Inv := InvI j) 40 0 n (Nat.zero_le _) hw1 (fun _ => hnw)
      ?_ ?_ ?_ ?_).conseq (fun _ h => h) ?_ (fun _ _ => le_rfl)
    · rintro st ⟨hR, h4, hfr, hdone⟩
      exact ⟨by eval_expr, hR.upd 5 0 (by omega), by simpa using h4, by simp, hfr, hdone,
        fun i hi => absurd hi (by omega)⟩
    · intro i st _ _ h; exact h.2.2.1
    · intro i st _ _ h; have := h.1.1; eval_expr
    · intro i _ hi st ω' ⟨hR, h4, h5, hfr, hlev, hdone⟩
      obtain ⟨r0, r1, r2, r3⟩ := hR
      have hj1 : j + 1 < L := by omega
      have hidx := idx_lt (j := j) hi (show j < L by omega)
      have hidx1 := idx_lt hi hj1
      have hu := liftF_lt hPlt j i hi
      have hidx2 := idx_lt (j := j) hu (show j < L by omega)
      have hv1 : st.mem (upPtr + (i * L + j)) = liftF P i j := hlev i hi j le_rfl
      have hv2 : st.mem (upPtr + (liftF P i j * L + j)) = liftF P (liftF P i j) j :=
        hlev _ hu j le_rfl
      refine runs_start_le ?_
      unfold upVStepBody
      refine runs_seq_assign_le (v := liftF P i j) (by rw [← hv1]; eval_expr) ?_
      refine runs_seq_assign_le (v := liftF P (liftF P i j) j) (by rw [← hv2]; eval_expr) ?_
      refine runs_store_le (x := upPtr + (i * L + j + 1)) (v := liftF P (liftF P i j) j)
        (by eval_expr) (by eval_expr) ⟨⟨((UpRegs.upd ⟨r0, r1, r2, r3⟩ 6 _ (by omega)).upd 7 _
          (by omega)).upd 5 (i + 1) (by omega), by simpa using h4, by simp, ?_, ?_, ?_⟩,
          by simpa using h5⟩ ?_
      · intro a ha
        simp only
        rw [Function.update_of_ne (by omega)]
        exact hfr a ha
      · intro i' hi' j' hj'
        simp only
        rw [Function.update_of_ne (by
          intro h
          have := idx_inj (show j' < L by omega) hj1 (show i' * L + j' = i * L + (j + 1) by omega)
          omega)]
        exact hlev i' hi' j' hj'
      · intro i' hi'
        simp only
        by_cases hii : i' = i
        · subst hii
          rw [show upPtr + (i' * L + (j + 1)) = upPtr + (i' * L + j + 1) by ring,
            Function.update_self]
          rfl
        · rw [Function.update_of_ne (by
            intro h
            have := idx_inj hj1 hj1 (show i' * L + (j + 1) = i * L + (j + 1) by omega)
            omega)]
          exact hdone i' (by omega)
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
    · intro o st h
      cases o with
      | returned v => exact h
      | normal =>
        obtain ⟨hR, h4, -, hfr, hlev, hdone⟩ := h
        refine ⟨⟨hR.upd 4 _ (by omega), by simp, hfr, fun i' hi' j' hj' => ?_⟩, h4⟩
        rcases Nat.lt_or_eq_of_le hj' with hlt | rfl
        · exact hlev i' hi' j' (by omega)
        · exact hdone i' hi'
  have hloop1 : Triple w p (fun st => UpRegs st n L parPtr upPtr ∧ Frame st.mem ∧
        ∀ i' < n, ∀ j' ≤ 0, st.mem (upPtr + (i' * L + j')) = liftF P i' j')
      (forRange 4 (.const 0) (.bin .sub (.reg 1) (.const 1))
        (forRange 5 (.const 0) (.reg 0) upVStepBody)) (normalPost (InvJ (L - 1)))
      (fun _ => (L - 1) * ((n * (40 + Expr.size (.reg 0) + 8) + (Expr.size (.const 0) +
        Expr.size (.reg 0) + 5)) + Expr.size (.bin .sub (.reg 1) (.const 1)) + 8) +
        (Expr.size (.const 0) + Expr.size (.bin .sub (.reg 1) (.const 1)) + 5)) := by
    refine Triple.forRange_const (Inv := InvJ) _ 0 (L - 1) (Nat.zero_le _) hw1
      (fun _ => by omega) ?_ ?_ ?_ (fun j _ hj => hinner j hj)
    · rintro st ⟨hR, hfr, hlev⟩
      exact ⟨by eval_expr, hR.upd 4 0 (by omega), by simp, hfr, hlev⟩
    · intro i st _ _ h; exact h.2.1
    · intro i st _ _ h
      have := h.1.2.1
      eval_expr
  -- the whole procedure
  refine runs_start_le ?_
  unfold upVProc
  refine runs_seq_triple_le hloop0 rfl ?_
  rintro st₁ ⟨hR, -, hfr, hdone⟩
  refine runs_seq_triple_le hloop1 ⟨hR, hfr, fun i' hi' j' hj' => by
    have : j' = 0 := by omega
    subst this
    exact hdone i' hi'⟩ ?_
  rintro st₂ ⟨-, -, hfr2, hlev2⟩
  refine runs_ret_le (by eval_expr) ⟨n, L, parPtr, upPtr, rfl, rfl,
    fun i hi j hj => hlev2 i hi j (by omega), hfr2⟩ ?_
  simp only [upVContract, Expr.size_const, Expr.size_reg, Expr.size_bin, List.getD_cons_zero,
    List.getD_cons_succ]
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  nlinarith

end

end MinCostFlow.LSF.Program
