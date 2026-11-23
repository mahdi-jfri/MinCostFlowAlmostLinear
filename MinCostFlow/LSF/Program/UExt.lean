module

public import MinCostFlow.LSF.Program.UArithMul
public import MinCostFlow.Num.DivisionStepFacts

/-!
# Widening a limb block

`uExtProc` copies a block of `La` limbs into a wider block of `L` limbs and fills the rest with
zeros, or writes zero when the flag `keep` is `0`. The unsigned value is kept
(`unsignedVal_eq_prefix_of_zeros`). The cost is `O(L)`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num

/-- Args: `[d, a, La, L]`. Register `5` is the limb index `i`. A zero block is written when
`La = 0`. -/
def uExtProc : Stmt :=
  forRange 5 (.const 0) (.reg 3)
    (.store (.bin .add (.reg 0) (.reg 5))
      (.bin .mul (.bin .lt (.reg 5) (.reg 2)) (.load (.bin .add (.reg 1) (.reg 5))))) ;;
  .ret (.const 0)

lemma uExtProc_noRand : uExtProc.NoRand := by
  simp [uExtProc, forRange, forUp, Stmt.NoRand]

/-- The value the procedure writes at limb `i`. -/
def uExtLimb (mem : ℕ → ℕ) (a La i : ℕ) : ℕ :=
  (if i < La then 1 else 0) * mem (a + i)

/-- The contract of `uExtProc`. -/
def uExtContract (w h : ℕ) : Contract where
  pre args mem := ∃ d a La L, args = [d, a, La, L] ∧ La ≤ L ∧ Valid mem a h La ∧
    (a + L ≤ d ∨ d + L ≤ a) ∧ d + L < 2 ^ w ∧ a + L < 2 ^ w
  post args mem ret mem' := ∃ d a La L, args = [d, a, La, L] ∧ ret = 0 ∧
    (∀ x, x < d ∨ d + L ≤ x → mem' x = mem x) ∧ Valid mem' d h L ∧
    unsignedVal mem' d h L = unsignedVal mem a h La
  cost args _ := 30 * args.getD 3 0 + 20

lemma uExtLimb_lt {mem : ℕ → ℕ} {a La h i : ℕ} (hv : Valid mem a h La) :
    uExtLimb mem a La i < base h := by
  unfold uExtLimb
  have hB := base_pos h
  rcases Nat.lt_or_ge i La with hi | hi
  · simpa [hi] using hv i hi
  · simp [show ¬ i < La by omega, hB]

theorem uExt_meetsContract {w h : ℕ} {p : Program} {b : ℕ} (hw : 2 * h + 2 ≤ w)
    (hp : p.procs[b]? = some uExtProc) :
    MeetsContract w p b (uExtContract w h) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨d, a, La, L, rfl, hLa, hva, hdisj, hdw, haw⟩ := hpre
  have hBw : base h < 2 ^ w := base_lt_word hw
  have hB1 : 1 ≤ base h := base_pos h
  have hw1 : 1 < 2 ^ w := by
    have : 2 ≤ 2 ^ w := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hLw : L < 2 ^ w := by omega
  set args := [d, a, La, L] with hargs
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = d ∧ st.regs 1 = a ∧ st.regs 2 = La ∧ st.regs 3 = L ∧
    st.regs 5 = i ∧ (∀ y, y < d ∨ d + i ≤ y → st.mem y = mem y) ∧
    ∀ j < i, st.mem (d + j) = uExtLimb mem a La j
  have hloop : Triple w p (fun st => st = startState args mem pos)
      (forRange 5 (.const 0) (.reg 3)
        (.store (.bin .add (.reg 0) (.reg 5))
          (.bin .mul (.bin .lt (.reg 5) (.reg 2)) (.load (.bin .add (.reg 1) (.reg 5))))))
      (normalPost (Inv L))
      (fun _ => (L - 0) * (15 + (Expr.reg 3).size + 8) +
        ((Expr.const 0).size + (Expr.reg 3).size + 5)) := by
    refine Triple.forRange_const 15 0 L (by omega) hw1 (fun _ => hLw) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, by simp [startState, hargs], by simp [startState, hargs],
        by simp [startState, hargs], by simp [startState, hargs], by simp, fun y _ => rfl, fun j hj => absurd hj (by omega)⟩
    · intro i st _ _ hI; exact hI.2.2.2.2.1
    · intro i st _ _ hI
      have r3 : st.regs 3 = L := hI.2.2.2.1
      eval_expr
    · intro i _ hiL st ω' hI
      obtain ⟨r0, r1, r2, r3, r5, hfr, hdone⟩ := hI
      have hmi : st.mem (a + i) = mem (a + i) := hfr _ (by omega)
      have hlimb := uExtLimb_lt (mem := mem) (a := a) (i := i) hva
      refine runs_start_le ?_
      refine runs_store_le (x := d + i) (v := uExtLimb mem a La i) (by eval_expr) ?_
        ⟨⟨by simpa using r0, by simpa using r1, by simpa using r2, by simpa using r3,
          by simp, fun y hy => ?_, fun j hj => ?_⟩, by simpa using r5⟩
        (by simp [Expr.size])
      · rcases Nat.lt_or_ge i La with hiLa | hiLa
        · have hv := hva i hiLa
          have he : uExtLimb mem a La i = mem (a + i) := by simp [uExtLimb, hiLa]
          rw [he]
          have h1 : a + i < 2 ^ w := by omega
          have h2 : i < 2 ^ w := by omega
          have h3 : mem (a + i) < 2 ^ w := by omega
          simp [Expr.eval, BinOp.eval, r1, r2, r5, hiLa, hmi, h1, h2, h3, hw1]
        · have he : uExtLimb mem a La i = 0 := by simp [uExtLimb, show ¬ i < La by omega]
          rw [he]
          have h1 : a + i < 2 ^ w := by omega
          have h2 : i < 2 ^ w := by omega
          simp [Expr.eval, BinOp.eval, r1, r2, r5, show ¬ i < La by omega, h1, h2]
      · dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr y (by omega)
      · dsimp only
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [Function.update_of_ne (by omega)]; exact hdone j hj
        · rw [Function.update_self]
  refine runs_start_le ?_
  unfold uExtProc
  refine runs_seq_triple_le hloop rfl ?_
  rintro st ⟨-, -, -, -, -, hfr, hdone⟩
  have hval : Valid st.mem d h L := fun j hj => by
    rw [hdone j hj]; exact uExtLimb_lt hva
  refine runs_ret_le (v := 0) (by eval_expr) ⟨d, a, La, L, rfl, rfl,
    fun y hy => hfr y (by omega), hval, ?_⟩ ?_
  · rw [unsignedVal_eq_prefix_of_zeros hLa (fun i hi1 hi2 => by
      rw [hdone i hi2]; simp [uExtLimb, show ¬ i < La by omega])]
    exact unsignedVal_congr fun i hi => by rw [hdone i (by omega)]; simp [uExtLimb, hi]
  · simp only [uExtContract, hargs, List.getD_cons_zero, List.getD_cons_succ,
      Expr.size_const, Expr.size_reg, Expr.size_bin, Expr.size_load]
    omega

end MinCostFlow.LSF.Program
