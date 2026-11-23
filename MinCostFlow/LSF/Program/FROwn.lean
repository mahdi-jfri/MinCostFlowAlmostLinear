module

public import MinCostFlow.LSF.Program.FRIdx
public import MinCostFlow.LSF.Program.TopDownPass

/-!
# The second part of the roots pass: the owner array

`frOwnProc` sets the `tM` words of `own` to `0`. Then, for every index `y < n` of `R` other than
the root, it stores `own (mp y) = y + 1`. The result is `OwnState … n` (`FRIdx.lean`): each edge
index `i` with `own i ≠ 0` is the `mp` of the index `own i - 1` of `R`, and `own i = 0` means no
index of `R` other than the root has `mp` equal to `i`. The cost is `O(n + tM)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow

@[expose] public section

/-- The test for one index (register `9` is `y`): `y` is in `R` and is not the root. -/
def frOwnTest : Expr :=
  .bin .mul (.load (.bin .add (.reg 3) (.reg 9)))
    (.bin .sub (.const 1) (.bin .eq (.reg 9) (.reg 1)))

/-- Args: `[n, r, mpPtr, inRPtr, ownPtr, tM]`. -/
def frOwnProc : Stmt :=
  forRange 8 (.const 0) (.reg 5) (.store (.bin .add (.reg 4) (.reg 8)) (.const 0)) ;;
  forRange 9 (.const 0) (.reg 0)
    (.cond frOwnTest
      (.store (.bin .add (.reg 4) (.load (.bin .add (.reg 2) (.reg 9))))
        (.bin .add (.reg 9) (.const 1)))
      .nop) ;;
  .ret (.const 0)

lemma frOwnProc_noRand : frOwnProc.NoRand := by
  simp [frOwnProc, frOwnTest, forRange, forUp, Stmt.NoRand]

/-- The contract of `frOwnProc`. The owner array lies above the arrays it reads. -/
def frOwnContract (w : ℕ) : Contract where
  pre args mem := ∃ (n r mpPtr inRPtr ownPtr tM : ℕ),
    args = [n, r, mpPtr, inRPtr, ownPtr, tM] ∧ r < n ∧
    (∀ y < n, mem (inRPtr + y) ≤ 1) ∧
    (∀ y < n, y ≠ r → mem (inRPtr + y) = 1 → mem (mpPtr + y) < tM) ∧
    mpPtr + n ≤ ownPtr ∧ inRPtr + n ≤ ownPtr ∧ ownPtr + tM < 2 ^ w
  post args mem ret mem' := ∃ (n r mpPtr inRPtr ownPtr tM : ℕ),
    args = [n, r, mpPtr, inRPtr, ownPtr, tM] ∧ ret = 0 ∧
    (∀ a, a < ownPtr ∨ ownPtr + tM ≤ a → mem' a = mem a) ∧
    OwnState r tM (fun y => mem (inRPtr + y)) (fun y => mem (mpPtr + y))
      (fun i => mem' (ownPtr + i)) n
  cost args _ := 30 * args.getD 5 0 + 60 * args.getD 0 0 + 40

theorem frOwn_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some frOwnProc) :
    MeetsContract w p b (frOwnContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, r, mpPtr, inRPtr, ownPtr, tM, rfl, hrn, hinR1, hmpt, hma, hia, hoa⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  set args := [n, r, mpPtr, inRPtr, ownPtr, tM] with hargs
  set inR : ℕ → ℕ := fun x => mem (inRPtr + x) with hinR
  set mp : ℕ → ℕ := fun x => mem (mpPtr + x) with hmp
  have hnw : n < 2 ^ w := by omega
  have htw : tM < 2 ^ w := by omega
  have hR0 : ∀ i < 6, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  -- the zero loop
  let Inv1 : ℕ → State → Prop := fun k st =>
    (∀ i < 6, st.regs i = args.getD i 0) ∧ st.regs 8 = k ∧
    (∀ a, a < ownPtr ∨ ownPtr + tM ≤ a → st.mem a = mem a) ∧
    ∀ i < k, st.mem (ownPtr + i) = 0
  have hloop1 : Triple w p (fun st => st = startState args mem pos)
      (forRange 8 (.const 0) (.reg 5) (.store (.bin .add (.reg 4) (.reg 8)) (.const 0)))
      (normalPost (Inv1 tM))
      (fun _ => (tM - 0) * (10 + (Expr.reg 5).size + 8) +
        ((Expr.const 0).size + (Expr.reg 5).size + 5)) := by
    refine Triple.forRange_const 10 0 tM (by omega) hw1 (fun _ => htw) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, fun i hi => ?_, by simp, fun a _ => rfl, fun i hi => absurd hi (by omega)⟩
      simp only [Function.update_of_ne (show i ≠ 8 by omega)]
      exact hR0 i hi
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r5 : st.regs 5 = tM := hI.1 5 (by omega)
      eval_expr
    · intro k _ hk st ω' hI
      obtain ⟨hR, h8, hfr, hz⟩ := hI
      have r4 : st.regs 4 = ownPtr := hR 4 (by omega)
      refine runs_start_le ?_
      refine runs_store_le (x := ownPtr + k) (v := 0) (by eval_expr) (by eval_expr)
        ⟨⟨fun i hi => ?_, by simpa using h8, fun a ha => ?_, fun i hi => ?_⟩, by simpa using h8⟩
        (by simp [Expr.size])
      · simp only [Function.update_of_ne (show i ≠ 8 by omega)]; exact hR i hi
      · dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a ha
      · dsimp only
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · rw [Function.update_of_ne (by omega)]; exact hz i hi
        · rw [Function.update_self]
  -- the owner loop
  let Inv2 : ℕ → State → Prop := fun j st =>
    (∀ i < 6, st.regs i = args.getD i 0) ∧ st.regs 9 = j ∧
    (∀ a, a < ownPtr ∨ ownPtr + tM ≤ a → st.mem a = mem a) ∧
    OwnState r tM inR mp (fun i => st.mem (ownPtr + i)) j
  have hloop2 : ∀ st₀ : State, Inv1 tM st₀ → Triple w p (fun st => st = st₀)
      (forRange 9 (.const 0) (.reg 0)
        (.cond frOwnTest
          (.store (.bin .add (.reg 4) (.load (.bin .add (.reg 2) (.reg 9))))
            (.bin .add (.reg 9) (.const 1)))
          .nop))
      (normalPost (Inv2 n))
      (fun _ => (n - 0) * (40 + (Expr.reg 0).size + 8) +
        ((Expr.const 0).size + (Expr.reg 0).size + 5)) := by
    intro st₀ hI1
    refine Triple.forRange_const 40 0 n (by omega) hw1 (fun _ => hnw) ?_ ?_ ?_ ?_
    · rintro st rfl
      obtain ⟨hR, -, hfr, hz⟩ := hI1
      refine ⟨by eval_expr, fun i hi => ?_, by simp, hfr, ownState_zero hz⟩
      simp only [Function.update_of_ne (show i ≠ 9 by omega)]
      exact hR i hi
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = n := hI.1 0 (by omega)
      eval_expr
    · intro j _ hjn st ω' hI
      obtain ⟨hR, h9, hfr, hO⟩ := hI
      have r1 : st.regs 1 = r := hR 1 (by omega)
      have r2 : st.regs 2 = mpPtr := hR 2 (by omega)
      have r3 : st.regs 3 = inRPtr := hR 3 (by omega)
      have r4 : st.regs 4 = ownPtr := hR 4 (by omega)
      have hmi : st.mem (inRPtr + j) = inR j := hfr _ (Or.inl (by omega))
      have hmm : st.mem (mpPtr + j) = mp j := hfr _ (Or.inl (by omega))
      have hc1 : inR j ≤ 1 := hinR1 j hjn
      set c := inR j * (1 - if j = r then 1 else 0) with hc
      have hcle : c ≤ 1 := by
        rw [hc]; split_ifs <;> simp <;> omega
      refine runs_start_le ?_
      refine runs_cond_le (v := c) (by
        unfold frOwnTest
        rw [hc, ← hmi]
        have : st.mem (inRPtr + j) ≤ 1 := by rw [hmi]; exact hc1
        have : st.mem (inRPtr + j) * (1 - if j = r then 1 else 0) ≤ 1 := by
          split_ifs <;> simp <;> omega
        eval_expr) ?_ ?_
      · intro hne
        have hjr : j ≠ r := by
          intro h; rw [hc, if_pos h] at hne; simp at hne
        have hjR : inR j = 1 := by
          rw [hc, if_neg hjr] at hne
          simp at hne
          omega
        have hmt : mp j < tM := hmpt j hjn hjr hjR
        refine runs_store_le (x := ownPtr + mp j) (v := j + 1) (by rw [← hmm]; eval_expr)
          (by eval_expr) ⟨⟨fun i hi => ?_, by simpa using h9, fun a ha => ?_, ?_⟩,
            by simpa using h9⟩ (by simp [Expr.size, frOwnTest])
        · simp only [Function.update_of_ne (show i ≠ 9 by omega)]; exact hR i hi
        · dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a ha
        · dsimp only
          rw [update_shift]
          exact ownState_write hO hjr hjR (fun i => by rw [Function.update_apply])
      · intro hz
        have hskip : ¬ (j ≠ r ∧ inR j = 1) := by
          rintro ⟨hjr, hjR⟩
          rw [hc, if_neg hjr, hjR] at hz
          simp at hz
        refine runs_nop_le ⟨⟨fun i hi => ?_, by simpa using h9, fun a ha => hfr a ha,
          ownState_skip hO hskip⟩, by simpa using h9⟩ (by simp [Expr.size, frOwnTest])
        simp only [Function.update_of_ne (show i ≠ 9 by omega)]; exact hR i hi
  refine runs_start_le ?_
  unfold frOwnProc
  refine runs_seq_triple_le hloop1 rfl ?_
  rintro st₁ hI1
  refine runs_seq_triple_le (hloop2 st₁ hI1) rfl ?_
  rintro st ⟨-, -, hfr, hO⟩
  refine runs_ret_le (v := 0) (by eval_expr)
    ⟨n, r, mpPtr, inRPtr, ownPtr, tM, rfl, rfl, hfr, hO⟩ ?_
  simp only [frOwnContract, hargs, List.getD_cons_zero, List.getD_cons_succ, Expr.size_const,
    Expr.size_reg, Expr.size_bin, Expr.size_load]
  omega

end

end MinCostFlow.LSF.Program
