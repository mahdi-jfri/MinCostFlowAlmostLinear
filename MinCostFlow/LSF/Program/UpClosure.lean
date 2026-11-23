module

public import MinCostFlow.LSF.Program.UpClosureMath
public import MinCostFlow.LSF.Program.FRLevel

/-!
# The upward closure program

`upClosureProc` computes the flags of the upward closure of a flagged set in `T_H`
(`UpClosureMath.lean`). It runs `upLevelProc` once for each depth `j = D, D - 1, …, 1`. The pass
at depth `j` sets the flag of the parent of each flagged index of depth `j`. The cost is
`O(D n)`, where `D` bounds the depths in `T_H`.

The result is `upClosure_meetsContract`. With `THIdx.upClosure_flag` its flags are the flags of
`upClosure (hldAuxTree T₀ r₀) r₀ R`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num

@[expose] public section

lemma ParDep.congr {n : ℕ} {d p d' p' : ℕ → ℕ} (h : ParDep n d p) (hd : ∀ x < n, d' x = d x)
    (hp : ∀ x < n, p' x = p x) : ParDep n d' p' := by
  intro x hx hpos
  rw [hd x hx] at hpos
  obtain ⟨h1, h2⟩ := h x hx hpos
  rw [hp x hx, hd x hx, hd _ h1]
  exact ⟨h1, h2⟩

/-! ## One pass -/

/-- Args: `[n, pPtr, dPtr, fPtr, j]`. Register `5` is the index `x`. -/
def upLevelProc : Stmt :=
  forRange 5 (.const 0) (.reg 0)
    (.cond (.bin .eq (.load (.bin .add (.reg 2) (.reg 5))) (.reg 4))
      (.store (.bin .add (.reg 3) (.load (.bin .add (.reg 1) (.reg 5))))
        (.bin .lt (.const 0)
          (.bin .add (.load (.bin .add (.reg 3) (.load (.bin .add (.reg 1) (.reg 5)))))
            (.load (.bin .add (.reg 3) (.reg 5))))))
      .nop) ;;
  .ret (.const 0)

lemma upLevelProc_noRand : upLevelProc.NoRand := by
  simp [upLevelProc, forRange, forUp, Stmt.NoRand]

open Classical in
/-- The flag of `y` after the pass at depth `j` has seen the indices below `X`. -/
noncomputable def upLevelVal (d p f : ℕ → ℕ) (j X y : ℕ) : ℕ :=
  if f y = 1 ∨ ∃ x < X, d x = j ∧ p x = y ∧ f x = 1 then 1 else 0

lemma upLevelVal_le (d p f : ℕ → ℕ) (j X y : ℕ) : upLevelVal d p f j X y ≤ 1 := by
  unfold upLevelVal; split_ifs <;> omega

lemma upLevelVal_succ (d p f : ℕ → ℕ) (j X y : ℕ) :
    upLevelVal d p f j (X + 1) y =
      if d X = j ∧ p X = y ∧ f X = 1 then 1 else upLevelVal d p f j X y := by
  have key : (∃ x < X + 1, d x = j ∧ p x = y ∧ f x = 1) ↔
      (∃ x < X, d x = j ∧ p x = y ∧ f x = 1) ∨ (d X = j ∧ p X = y ∧ f X = 1) := by
    constructor
    · rintro ⟨x, hx, hP⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
      · exact Or.inl ⟨x, hx, hP⟩
      · exact Or.inr hP
    · rintro (⟨x, hx, hP⟩ | hP)
      · exact ⟨x, by omega, hP⟩
      · exact ⟨X, by omega, hP⟩
  unfold upLevelVal
  simp only [key]
  by_cases h1 : d X = j ∧ p X = y ∧ f X = 1
  · rw [if_pos h1, if_pos (Or.inr (Or.inr h1))]
  · rw [if_neg h1]
    exact if_congr (or_congr_right (or_iff_left h1)) rfl rfl

/-- An index of depth `j` is not the parent of an index of depth `j`, so its flag is still the
input flag. -/
lemma upLevelVal_self {n : ℕ} {d p f : ℕ → ℕ} {j X : ℕ} (h : ParDep n d p) (hX : X ≤ n)
    (hj : 1 ≤ j) (hd : d X = j) : upLevelVal d p f j X X = if f X = 1 then 1 else 0 := by
  unfold upLevelVal
  congr 1
  apply propext
  constructor
  · rintro (h1 | ⟨x, hx, hdx, hpx, -⟩)
    · exact h1
    · have := (h x (by omega) (by omega)).2
      rw [hpx] at this
      omega
  · exact Or.inl

/-- The contract of `upLevelProc`. -/
def upLevelContract (w : ℕ) : Contract where
  pre args mem := ∃ n pPtr dPtr fPtr j, args = [n, pPtr, dPtr, fPtr, j] ∧ 16 ≤ 2 ^ w ∧
    1 ≤ j ∧ pPtr + n ≤ fPtr ∧ dPtr + n ≤ fPtr ∧ fPtr + n < 2 ^ w ∧
    ParDep n (fun x => mem (dPtr + x)) (fun x => mem (pPtr + x)) ∧ ∀ x < n, mem (fPtr + x) ≤ 1
  post args mem ret mem' := ∃ n pPtr dPtr fPtr j, args = [n, pPtr, dPtr, fPtr, j] ∧ ret = 0 ∧
    (∀ a, a < fPtr ∨ fPtr + n ≤ a → mem' a = mem a) ∧
    ∀ y < n, mem' (fPtr + y) = upLevelVal (fun x => mem (dPtr + x)) (fun x => mem (pPtr + x))
      (fun x => mem (fPtr + x)) j n y
  cost args _ := 70 * args.getD 0 0 + 20

theorem upLevel_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some upLevelProc) :
    MeetsContract w p b (upLevelContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, pPtr, dPtr, fPtr, j, rfl, h16, hj, hpf, hdf, hfw, hPD, hf1⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := by omega
  set args := [n, pPtr, dPtr, fPtr, j] with hargs
  set d : ℕ → ℕ := fun x => mem (dPtr + x) with hdd
  set pp : ℕ → ℕ := fun x => mem (pPtr + x) with hppd
  set f : ℕ → ℕ := fun x => mem (fPtr + x) with hfd
  let Inv : ℕ → State → Prop := fun X st =>
    st.regs 0 = n ∧ st.regs 1 = pPtr ∧ st.regs 2 = dPtr ∧ st.regs 3 = fPtr ∧ st.regs 4 = j ∧
    st.regs 5 = X ∧ (∀ a, a < fPtr ∨ fPtr + n ≤ a → st.mem a = mem a) ∧
    ∀ y < n, st.mem (fPtr + y) = upLevelVal d pp f j X y
  have hloop : Triple w p (fun st => st = startState args mem pos)
      (forRange 5 (.const 0) (.reg 0)
        (.cond (.bin .eq (.load (.bin .add (.reg 2) (.reg 5))) (.reg 4))
          (.store (.bin .add (.reg 3) (.load (.bin .add (.reg 1) (.reg 5))))
            (.bin .lt (.const 0)
              (.bin .add (.load (.bin .add (.reg 3) (.load (.bin .add (.reg 1) (.reg 5)))))
                (.load (.bin .add (.reg 3) (.reg 5))))))
          .nop))
      (normalPost (Inv n))
      (fun _ => (n - 0) * (60 + (Expr.reg 0).size + 8) +
        ((Expr.const 0).size + (Expr.reg 0).size + 5)) := by
    refine Triple.forRange_const 60 0 n (by omega) hw1 (fun _ => hnw) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, by simp [startState, hargs], by simp [startState, hargs],
        by simp [startState, hargs], by simp [startState, hargs], by simp [startState, hargs],
        by simp, fun a _ => rfl, fun y hy => ?_⟩
      have := hf1 y hy
      simp only [startState, upLevelVal, hfd]
      split_ifs with h1
      · rcases h1 with h1 | ⟨x, hx, -⟩
        · exact h1
        · exact absurd hx (by omega)
      · push Not at h1
        have := h1.1
        omega
    · intro X st _ _ hI; exact hI.2.2.2.2.2.1
    · intro X st _ _ hI
      have r0 : st.regs 0 = n := hI.1
      eval_expr
    · intro X _ hXn st ω' hI
      obtain ⟨r0, r1, r2, r3, r4, r5, hfr, hval⟩ := hI
      have hdX : st.mem (dPtr + X) = d X := hfr _ (Or.inl (by omega))
      have hpX : st.mem (pPtr + X) = pp X := hfr _ (Or.inl (by omega))
      refine runs_start_le ?_
      refine runs_cond_le (v := if d X = j then 1 else 0)
        (by rw [← hdX]; eval_expr) (fun hv => ?_) (fun hv => ?_)
      · have hdj : d X = j := by by_contra hne; exact hv (if_neg hne)
        obtain ⟨hpn, -⟩ := hPD X hXn (by omega)
        have hfX : st.mem (fPtr + X) = if f X = 1 then 1 else 0 := by
          rw [hval X hXn, upLevelVal_self hPD (by omega) hj hdj]
        have hfP := hval _ hpn
        have hcP := upLevelVal_le d pp f j X (pp X)
        have hfX1 : st.mem (fPtr + X) ≤ 1 := by rw [hfX]; split_ifs <;> omega
        have hfPw : fPtr + pp X < 2 ^ w := by omega
        have hsum : st.mem (fPtr + st.mem (pPtr + X)) + st.mem (fPtr + X) < 2 ^ w := by
          rw [hpX, hfP]; omega
        refine runs_store_le (x := fPtr + pp X)
          (v := if 0 < st.mem (fPtr + pp X) + st.mem (fPtr + X) then 1 else 0)
          (by rw [← hpX]; eval_expr) (by rw [← hpX]; eval_expr)
          ⟨⟨by simpa using r0, by simpa using r1, by simpa using r2, by simpa using r3,
            by simpa using r4, by simp, fun a ha => ?_, fun y hy => ?_⟩, by simpa using r5⟩
          (by simp [Expr.size])
        · dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a ha
        · dsimp only
          rw [upLevelVal_succ]
          by_cases hy' : y = pp X
          · subst hy'
            rw [Function.update_self, hfP, hfX]
            simp only [hdj, true_and]
            split_ifs <;> omega
          · rw [Function.update_of_ne (by omega), if_neg (fun h => hy' h.2.1.symm)]
            exact hval y hy
      · have hdj : d X ≠ j := by intro he; exact absurd hv (by simp [he])
        refine runs_nop_le ⟨⟨by simpa using r0, by simpa using r1, by simpa using r2,
          by simpa using r3, by simpa using r4, by simp, fun a ha => hfr a ha, fun y hy => ?_⟩,
          by simpa using r5⟩ (by simp [Expr.size])
        dsimp only
        rw [upLevelVal_succ, if_neg (fun h => hdj h.1)]
        exact hval y hy
  refine runs_start_le ?_
  unfold upLevelProc
  refine runs_seq_triple_le hloop rfl ?_
  rintro st ⟨-, -, -, -, -, -, hfr, hval⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, pPtr, dPtr, fPtr, j, rfl, rfl, hfr, hval⟩ ?_
  simp only [upLevelContract, hargs, List.getD_cons_zero, Expr.size_const, Expr.size_reg]
  omega

/-! ## All passes -/

/-- Args: `[n, pPtr, dPtr, fPtr, D]`. Register `5` is the pass number `k`; the pass is at depth
`D - k`. -/
def upClosureProc (bLev : ℕ) : Stmt :=
  forRange 5 (.const 0) (.reg 4)
    (.call 6 bLev [.reg 0, .reg 1, .reg 2, .reg 3, .bin .sub (.reg 4) (.reg 5)]) ;;
  .ret (.const 0)

lemma upClosureProc_noRand (bLev : ℕ) : (upClosureProc bLev).NoRand := by
  simp [upClosureProc, forRange, forUp, Stmt.NoRand]

open Classical in
/-- The contract of `upClosureProc`. The output flag of `y` is `1` exactly when `y` is an
ancestor of a flagged index. -/
def upClosureContract (w : ℕ) : Contract where
  pre args mem := ∃ n pPtr dPtr fPtr D, args = [n, pPtr, dPtr, fPtr, D] ∧ 16 ≤ 2 ^ w ∧
    pPtr + n ≤ fPtr ∧ dPtr + n ≤ fPtr ∧ fPtr + n < 2 ^ w ∧
    ParDep n (fun x => mem (dPtr + x)) (fun x => mem (pPtr + x)) ∧
    (∀ x < n, mem (dPtr + x) ≤ D) ∧ ∀ x < n, mem (fPtr + x) ≤ 1
  post args mem ret mem' := ∃ n pPtr dPtr fPtr D, args = [n, pPtr, dPtr, fPtr, D] ∧ ret = 0 ∧
    (∀ a, a < fPtr ∨ fPtr + n ≤ a → mem' a = mem a) ∧
    ∀ y < n, mem' (fPtr + y) =
      if ∃ u < n, mem (fPtr + u) = 1 ∧
        IdxAnc (fun x => mem (dPtr + x)) (fun x => mem (pPtr + x)) y u then 1 else 0
  cost args _ := args.getD 4 0 * (70 * args.getD 0 0 + 80) + 20

theorem upClosure_meetsContract {w : ℕ} {p : Program} {b bLev : ℕ}
    (hp : p.procs[b]? = some (upClosureProc bLev))
    (hLev : MeetsContract w p bLev (upLevelContract w)) :
    MeetsContract w p b (upClosureContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, pPtr, dPtr, fPtr, D, rfl, h16, hpf, hdf, hfw, hPD, hDle, hf1⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  have hDw : D < 2 ^ w := hwords _ (by simp)
  set args := [n, pPtr, dPtr, fPtr, D] with hargs
  set d : ℕ → ℕ := fun x => mem (dPtr + x) with hdd
  set pp : ℕ → ℕ := fun x => mem (pPtr + x) with hppd
  set f : ℕ → ℕ := fun x => mem (fPtr + x) with hfd
  let Inv : ℕ → State → Prop := fun k st =>
    st.regs 0 = n ∧ st.regs 1 = pPtr ∧ st.regs 2 = dPtr ∧ st.regs 3 = fPtr ∧ st.regs 4 = D ∧
    st.regs 5 = k ∧ (∀ a, a < fPtr ∨ fPtr + n ≤ a → st.mem a = mem a) ∧
    ∀ y < n, st.mem (fPtr + y) = if UpState n d pp f (D - k) y then 1 else 0
  have hloop : Triple w p (fun st => st = startState args mem pos)
      (forRange 5 (.const 0) (.reg 4)
        (.call 6 bLev [.reg 0, .reg 1, .reg 2, .reg 3, .bin .sub (.reg 4) (.reg 5)]))
      (normalPost (Inv D))
      (fun _ => (D - 0) * ((70 * n + 60) + (Expr.reg 4).size + 8) +
        ((Expr.const 0).size + (Expr.reg 4).size + 5)) := by
    refine Triple.forRange_const (70 * n + 60) 0 D (by omega) hw1 (fun _ => hDw) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, by simp [startState, hargs], by simp [startState, hargs],
        by simp [startState, hargs], by simp [startState, hargs], by simp [startState, hargs],
        by simp, fun a _ => rfl, fun y hy => ?_⟩
      have : f y ≤ 1 := hf1 y hy
      simp only [startState, Nat.sub_zero]
      rw [if_congr (upState_init hDle hy) rfl rfl]
      show f y = _
      split_ifs <;> omega
    · intro k st _ _ hI; exact hI.2.2.2.2.2.1
    · intro k st _ _ hI
      have r4 : st.regs 4 = D := hI.2.2.2.2.1
      eval_expr
    · intro k _ hkD st ω' hI
      obtain ⟨r0, r1, r2, r3, r4, r5, hfr, hval⟩ := hI
      have hd' : ∀ x < n, st.mem (dPtr + x) = d x := fun x hx => hfr _ (Or.inl (by omega))
      have hp' : ∀ x < n, st.mem (pPtr + x) = pp x := fun x hx => hfr _ (Or.inl (by omega))
      have hcur : ∀ x < n, st.mem (fPtr + x) = 1 ↔ UpState n d pp f (D - k) x := fun x hx => by
        rw [hval x hx]; split_ifs with h <;> simp [h]
      refine runs_start_le ?_
      refine runs_call_le (vs := [n, pPtr, dPtr, fPtr, D - k]) hLev
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))
        (by
          intro v hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl <;>
            first | omega | exact hwords _ (by simp [hargs]))
        ⟨n, pPtr, dPtr, fPtr, D - k, rfl, h16, by omega, hpf, hdf, hfw, hPD.congr hd' hp',
          fun x hx => by rw [hval x hx]; split_ifs <;> omega⟩ ?_
      rintro v mem' pos' ⟨n', pPtr', dPtr', fPtr', j', heq, -, hfr', hval'⟩
      simp only [List.cons.injEq, and_true] at heq
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
      refine ⟨⟨⟨by simpa using r0, by simpa using r1, by simpa using r2, by simpa using r3,
        by simpa using r4, by simp, fun a ha => ?_, fun y hy => ?_⟩, ?_⟩, ?_⟩
      · dsimp only; rw [hfr' a ha]; exact hfr a ha
      · dsimp only
        rw [hval' y hy]
        simp only [upLevelVal]
        refine if_congr ?_ rfl rfl
        rw [show D - (k + 1) = D - k - 1 by omega, ← hPD.upState_step (by omega : 1 ≤ D - k)]
        refine or_congr (hcur y hy) ⟨fun ⟨x, hx, h1, h2, h3⟩ => ⟨x, hx, ?_, ?_, (hcur x hx).mp h3⟩,
          fun ⟨x, hx, h1, h2, h3⟩ => ⟨x, hx, ?_, ?_, (hcur x hx).mpr h3⟩⟩
        · rw [← hd' x hx]; exact h1
        · rw [← hp' x hx]; exact h2
        · rw [hd' x hx]; exact h1
        · rw [hp' x hx]; exact h2
      · show Function.update st.regs 6 v 5 = k
        rw [Function.update_of_ne (by omega)]; exact r5
      · simp only [upLevelContract, List.getD_cons_zero, argsSize, Expr.size_reg, Expr.size_bin]
        omega
  refine runs_start_le ?_
  unfold upClosureProc
  refine runs_seq_triple_le hloop rfl ?_
  rintro st ⟨-, -, -, -, -, -, hfr, hval⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, pPtr, dPtr, fPtr, D, rfl, rfl, hfr,
    fun y hy => ?_⟩ ?_
  · rw [hval y hy, Nat.sub_self]
    exact if_congr upState_zero rfl rfl
  · simp only [upClosureContract, hargs, List.getD_cons_zero, List.getD_cons_succ,
      Expr.size_const, Expr.size_reg]
    have : D * (70 * n + 60 + 1 + 8) ≤ D * (70 * n + 80) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.sub_zero]
    omega

end

end MinCostFlow.LSF.Program
