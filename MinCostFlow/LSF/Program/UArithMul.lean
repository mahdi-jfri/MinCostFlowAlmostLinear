module

public import MinCostFlow.LSF.Program.UArith

/-!
# Loading a word and multiplying limb blocks

* `uLoadWordProc`: write the low `L` limbs of a word `x` into a block (cost `30 L + 20`).
* `uMulProc`: set a block `d` to `A · B` modulo its capacity, by schoolbook rows: for each limb
  `b_j` of `B`, add `b_j · A` to the block that starts `j` limbs into `d` (`uAccProc`). Adding at
  that offset adds `capacity_j · b_j · A` to `d`, modulo the capacity (`umul_step`). The cost is
  `O(L²)`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num

/-! ## Loading a word -/

/-- Args: `[d, L, x]`. Register `2` holds what is left of `x`, register `3` is `i`. -/
def uLoadWordProc (h : ℕ) : Stmt :=
  forRange 3 (.const 0) (.reg 1)
    (.store (.bin .add (.reg 0) (.reg 3)) (.bin .mod (.reg 2) (.const (base h))) ;;
     .assign 2 (.bin .div (.reg 2) (.const (base h)))) ;;
  .ret (.const 0)

lemma uLoadWordProc_noRand (h : ℕ) : (uLoadWordProc h).NoRand := by
  simp [uLoadWordProc, forRange, forUp, Stmt.NoRand]

/-- The contract of `uLoadWordProc`. -/
def uLoadWordContract (w h : ℕ) : Contract where
  pre args _ := ∃ d L x, args = [d, L, x] ∧ d + L < 2 ^ w
  post args mem ret mem' := ∃ d L x, args = [d, L, x] ∧ ret = 0 ∧
    (∀ y, y < d ∨ d + L ≤ y → mem' y = mem y) ∧ Valid mem' d h L ∧
    unsignedVal mem' d h L = x % capacity h L
  cost args _ := 30 * args.getD 1 0 + 20

theorem uLoadWord_meetsContract {w h : ℕ} {p : Program} {b : ℕ} (hw : 2 * h + 2 ≤ w)
    (hp : p.procs[b]? = some (uLoadWordProc h)) :
    MeetsContract w p b (uLoadWordContract w h) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨d, L, x, rfl, hdw⟩ := hpre
  set B := base h with hBdef
  have hB0 : 0 < B := base_pos h
  have hBw : B < 2 ^ w := base_lt_word hw
  have hw1 : 1 < 2 ^ w := by omega
  have hLw : L < 2 ^ w := by omega
  have hxw : x < 2 ^ w := hwords x (by simp)
  set args := [d, L, x] with hargs
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = d ∧ st.regs 1 = L ∧ st.regs 3 = i ∧ st.regs 2 ≤ x ∧
    (∀ y, y < d ∨ d + i ≤ y → st.mem y = mem y) ∧ (∀ j < i, st.mem (d + j) < B) ∧
    unsignedVal st.mem d h i + capacity h i * st.regs 2 = x
  have hloop : Triple w p (fun st => st = startState args mem pos)
      (forRange 3 (.const 0) (.reg 1)
        (.store (.bin .add (.reg 0) (.reg 3)) (.bin .mod (.reg 2) (.const (base h))) ;;
         .assign 2 (.bin .div (.reg 2) (.const (base h)))))
      (normalPost (Inv L))
      (fun _ => (L - 0) * (15 + (Expr.reg 1).size + 8) +
        ((Expr.const 0).size + (Expr.reg 1).size + 5)) := by
    refine Triple.forRange_const 15 0 L (by omega) hw1 (fun _ => hLw) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, by simp [startState, hargs], by simp [startState, hargs], by simp,
        by simp [startState, hargs], fun y _ => rfl, fun j hj => absurd hj (by omega), ?_⟩
      simp [startState, hargs, unsignedVal, capacity]
    · intro i st _ _ hI; exact hI.2.2.1
    · intro i st _ _ hI
      have r1 : st.regs 1 = L := hI.2.1
      eval_expr
    · intro i _ hiL st ω' hI
      obtain ⟨r0, r1, r3, hx, hfr, hlow, heq⟩ := hI
      set c := st.regs 2 with hc
      refine runs_start_le ?_
      refine runs_seq_store_le (x := d + i) (v := c % B) (by eval_expr) (by eval_expr) ?_
      refine runs_assign_le (v := c / B) (by eval_expr)
        ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ ?_
      · simp [r0]
      · simp [r1]
      · simp [r3]
      · simp only [Function.update_self, Function.update_of_ne (show (2 : ℕ) ≠ 3 by omega)]
        exact (Nat.div_le_self _ _).trans hx
      · intro y hy
        dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hfr y (by omega)
      · intro j hj
        dsimp only
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [Function.update_of_ne (by omega)]; exact hlow j hj
        · rw [Function.update_self]; exact Nat.mod_lt _ hB0
      · dsimp only
        simp only [Function.update_self, Function.update_of_ne (show (2 : ℕ) ≠ 3 by omega)]
        have hlowU : unsignedVal (Function.update st.mem (d + i) (c % B)) d h i =
            unsignedVal st.mem d h i :=
          unsignedVal_congr fun j hj => Function.update_of_ne (by omega) _ _
        rw [unsignedVal_snoc, hlowU, Function.update_self, capacity_succ, ← heq]
        have := Nat.mod_add_div c B
        rw [show capacity h i * c = capacity h i * (c % B + B * (c / B)) by rw [this]]
        ring
      · simp [r3]
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
  refine runs_start_le ?_
  unfold uLoadWordProc
  refine runs_seq_triple_le hloop rfl ?_
  rintro st ⟨-, -, -, -, hfr, hlow, heq⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨d, L, x, rfl, rfl,
    fun y hy => hfr y (by omega), fun j hj => hlow j hj, ?_⟩ ?_
  · have hlt : unsignedVal st.mem d h L < capacity h L := unsignedVal_lt fun j hj => hlow j hj
    rw [← heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · simp only [uLoadWordContract, hargs, List.getD_cons_zero, List.getD_cons_succ,
      Expr.size_const, Expr.size_reg, Expr.size_bin, Expr.size_load]
    omega

/-! ## Schoolbook multiplication -/

/-- Adding `b_j · A` to the block `j` limbs into `d` adds `capacity_j · b_j · A` to `d`, modulo
the capacity. -/
lemma umul_step {mem mem' : ℕ → ℕ} {d a h j M bj : ℕ}
    (hlow : ∀ i < j, mem' (d + i) = mem (d + i))
    (hhigh : unsignedVal mem' (d + j) h M =
      (unsignedVal mem (d + j) h M + bj * unsignedVal mem a h M) % capacity h M)
    (hva : Valid mem a h (j + M)) :
    unsignedVal mem' d h (j + M) % capacity h (j + M) =
      (unsignedVal mem d h (j + M) + capacity h j * bj * unsignedVal mem a h (j + M)) %
        capacity h (j + M) := by
  have hY : unsignedVal mem a h M = unsignedVal mem a h (j + M) % capacity h M := by
    rw [unsignedVal_mod_prefix hva (by omega)]
  rw [unsignedVal_split mem' d h j M, unsignedVal_split mem d h j M, hhigh,
    unsignedVal_congr (fun i hi => hlow i hi) (a' := d), capacity_add]
  set P := unsignedVal mem d h j
  set X := unsignedVal mem (d + j) h M
  set A := unsignedVal mem a h (j + M)
  set cj := capacity h j
  set cM := capacity h M
  change P + cj * ((X + bj * unsignedVal mem a h M) % cM) ≡ P + cj * X + cj * bj * A
    [MOD cj * cM]
  rw [hY]
  have h1 : cj * ((X + bj * (A % cM)) % cM) ≡ cj * (X + bj * (A % cM)) [MOD cj * cM] :=
    (Nat.mod_modEq _ _).mul_left' cj
  have h2 : cj * (A % cM) ≡ cj * A [MOD cj * cM] := (Nat.mod_modEq _ _).mul_left' cj
  have h3 : cj * (X + bj * (A % cM)) = cj * X + bj * (cj * (A % cM)) := by ring
  have h4 : cj * X + cj * bj * A = cj * X + bj * (cj * A) := by ring
  rw [add_assoc, h4]
  refine (h1.trans ?_).add_left P
  rw [h3]
  exact (h2.mul_left bj).add_left _

/-- Args: `[d, a, bb, L]`. Register `4` is the zero loop index, `5` is `j`. -/
def uMulProc (bAcc : ℕ) : Stmt :=
  forRange 4 (.const 0) (.reg 3) (.store (.bin .add (.reg 0) (.reg 4)) (.const 0)) ;;
  forRange 5 (.const 0) (.reg 3)
    (.call 6 bAcc [.bin .add (.reg 0) (.reg 5), .reg 1, .bin .sub (.reg 3) (.reg 5),
      .load (.bin .add (.reg 2) (.reg 5)), .const 0]) ;;
  .ret (.const 0)

lemma uMulProc_noRand (bAcc : ℕ) : (uMulProc bAcc).NoRand := by
  simp [uMulProc, forRange, forUp, Stmt.NoRand]

/-- The contract of `uMulProc`. The block `d` meets neither factor. -/
def uMulContract (w h : ℕ) : Contract where
  pre args mem := ∃ d a bb L, args = [d, a, bb, L] ∧ Valid mem a h L ∧ Valid mem bb h L ∧
    (a + L ≤ d ∨ d + L ≤ a) ∧ (bb + L ≤ d ∨ d + L ≤ bb) ∧ d + L < 2 ^ w ∧ a + L < 2 ^ w ∧
    bb + L < 2 ^ w
  post args mem ret mem' := ∃ d a bb L, args = [d, a, bb, L] ∧ ret = 0 ∧
    (∀ y, y < d ∨ d + L ≤ y → mem' y = mem y) ∧ Valid mem' d h L ∧
    unsignedVal mem' d h L = (unsignedVal mem a h L * unsignedVal mem bb h L) % capacity h L
  cost args _ := 80 * args.getD 3 0 * args.getD 3 0 + 100 * args.getD 3 0 + 50

theorem uMul_meetsContract {w h : ℕ} {p : Program} {b bAcc : ℕ}
    (hAcc : MeetsContract w p bAcc (uAccContract w h)) (hw : 2 * h + 2 ≤ w)
    (hp : p.procs[b]? = some (uMulProc bAcc)) :
    MeetsContract w p b (uMulContract w h) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨d, a, bb, L, rfl, hva, hvb, hda, hdb, hdw, haw, hbw⟩ := hpre
  set B := base h with hBdef
  have hB0 : 0 < B := base_pos h
  have hBw : B < 2 ^ w := base_lt_word hw
  have hw1 : 1 < 2 ^ w := by omega
  have hLw : L < 2 ^ w := by omega
  set args := [d, a, bb, L] with hargs
  have hR0 : ∀ j < 4, (startState args mem pos).regs j = args.getD j 0 := by
    intro j hj
    interval_cases j <;> simp [startState, hargs]
  -- the zero loop
  let Inv1 : ℕ → State → Prop := fun i st =>
    (∀ j < 4, st.regs j = args.getD j 0) ∧ st.regs 4 = i ∧
    (∀ y, y < d ∨ d + i ≤ y → st.mem y = mem y) ∧ ∀ j < i, st.mem (d + j) = 0
  have hloop1 : Triple w p (fun st => st = startState args mem pos)
      (forRange 4 (.const 0) (.reg 3) (.store (.bin .add (.reg 0) (.reg 4)) (.const 0)))
      (normalPost (Inv1 L))
      (fun _ => (L - 0) * (10 + (Expr.reg 3).size + 8) +
        ((Expr.const 0).size + (Expr.reg 3).size + 5)) := by
    refine Triple.forRange_const 10 0 L (by omega) hw1 (fun _ => hLw) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, fun j hj => ?_, by simp, fun y _ => rfl, fun j hj => absurd hj (by omega)⟩
      simp only [Function.update_of_ne (show j ≠ 4 by omega)]
      exact hR0 j hj
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r3 : st.regs 3 = L := hI.1 3 (by omega)
      eval_expr
    · intro i _ hi st ω' hI
      obtain ⟨hR, h4, hfr, hz⟩ := hI
      have r0 : st.regs 0 = d := hR 0 (by omega)
      refine runs_start_le ?_
      refine runs_store_le (x := d + i) (v := 0) (by eval_expr) (by eval_expr)
        ⟨⟨fun j hj => ?_, by simpa using h4, fun y hy => ?_, fun j hj => ?_⟩, by simpa using h4⟩
        (by simp [Expr.size])
      · simp only [Function.update_of_ne (show j ≠ 4 by omega)]; exact hR j hj
      · dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr y (by omega)
      · dsimp only
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [Function.update_of_ne (by omega)]; exact hz j hj
        · rw [Function.update_self]
  -- the row loop
  let Inv2 : ℕ → State → Prop := fun j st =>
    (∀ i < 4, st.regs i = args.getD i 0) ∧ st.regs 5 = j ∧
    (∀ y, y < d ∨ d + L ≤ y → st.mem y = mem y) ∧ Valid st.mem d h L ∧
    unsignedVal st.mem d h L =
      (unsignedVal mem a h L * unsignedVal mem bb h j) % capacity h L
  have hloop2 : ∀ st₀ : State, Inv1 L st₀ → Triple w p (fun st => st = st₀)
      (forRange 5 (.const 0) (.reg 3)
        (.call 6 bAcc [.bin .add (.reg 0) (.reg 5), .reg 1, .bin .sub (.reg 3) (.reg 5),
          .load (.bin .add (.reg 2) (.reg 5)), .const 0]))
      (normalPost (Inv2 L))
      (fun _ => (L - 0) * ((70 * L + 60) + (Expr.reg 3).size + 8) +
        ((Expr.const 0).size + (Expr.reg 3).size + 5)) := by
    intro st₀ hI1
    refine Triple.forRange_const (70 * L + 60) 0 L (by omega) hw1 (fun _ => hLw) ?_ ?_ ?_ ?_
    · rintro st rfl
      obtain ⟨hR, -, hfr, hz⟩ := hI1
      refine ⟨by eval_expr, fun i hi => ?_, by simp, fun y hy => hfr y (by omega),
        fun i hi => by simp only; rw [hz i hi]; exact hB0, ?_⟩
      · simp only [Function.update_of_ne (show i ≠ 5 by omega)]; exact hR i hi
      · simp only
        rw [unsignedVal_zero (fun i hi => hz i hi)]
        simp [unsignedVal]
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r3 : st.regs 3 = L := hI.1 3 (by omega)
      eval_expr
    · intro j _ hjL st ω' hI
      obtain ⟨hR, h5, hfr, hvd, heq⟩ := hI
      have r0 : st.regs 0 = d := hR 0 (by omega)
      have r1 : st.regs 1 = a := hR 1 (by omega)
      have r2 : st.regs 2 = bb := hR 2 (by omega)
      have r3 : st.regs 3 = L := hR 3 (by omega)
      have hma : ∀ i < L, st.mem (a + i) = mem (a + i) := fun i hi => hfr _ (by omega)
      have hmb : ∀ i < L, st.mem (bb + i) = mem (bb + i) := fun i hi => hfr _ (by omega)
      have hbj : st.mem (bb + j) < B := by rw [hmb j hjL]; exact hvb j hjL
      have hva' : Valid st.mem a h L := fun i hi => by rw [hma i hi]; exact hva i hi
      have hUa : unsignedVal st.mem a h L = unsignedVal mem a h L :=
        unsignedVal_congr fun i hi => hma i hi
      refine runs_start_le ?_
      refine runs_call_le (vs := [d + j, a, L - j, st.mem (bb + j), 0]) hAcc
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))
        (by
          intro v hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega)
        ⟨d + j, a, L - j, st.mem (bb + j), 0, rfl, by omega, hbj,
          fun i hi => by simpa [Nat.add_assoc] using hvd (j + i) (by omega),
          fun i hi => hva' i (by omega), by omega, by omega, by omega⟩ ?_
      rintro v mem' pos' ⟨d', a', L', k', neg', heq', hv0, hfr', hvd', hval'⟩
      simp only [List.cons.injEq, and_true] at heq'
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq'
      refine ⟨⟨⟨fun i hi => ?_, ?_, fun y hy => ?_, ?_, ?_⟩, ?_⟩, ?_⟩
      · dsimp only
        simp only [Function.update_of_ne (show i ≠ 5 by omega),
          Function.update_of_ne (show i ≠ 6 by omega)]
        exact hR i hi
      · simp
      · dsimp only; rw [hfr' y (by omega)]; exact hfr y hy
      · dsimp only
        intro i hi
        by_cases hij : i < j
        · rw [hfr' _ (by omega)]; exact hvd i hi
        · have := hvd' (i - j) (by omega)
          rwa [show d + j + (i - j) = d + i by omega] at this
      · dsimp only
        have hlow : ∀ i < j, mem' (d + i) = st.mem (d + i) := fun i hi => hfr' _ (by omega)
        have hvd'' : Valid mem' d h L := by
          intro i hi
          by_cases hij : i < j
          · rw [hfr' _ (by omega)]; exact hvd i hi
          · have := hvd' (i - j) (by omega)
            rwa [show d + j + (i - j) = d + i by omega] at this
        have hstep := umul_step (M := L - j) (bj := st.mem (bb + j)) hlow
          (by rw [hval']; rfl) (by rw [show j + (L - j) = L by omega]; exact hva')
        rw [show j + (L - j) = L by omega] at hstep
        have hlt : unsignedVal mem' d h L < capacity h L := unsignedVal_lt hvd''
        rw [← Nat.mod_eq_of_lt hlt, hstep, heq, hUa, unsignedVal_snoc mem bb, ← hmb j hjL]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        congr 1
        ring
      · dsimp only
        simp only [Function.update_of_ne (show (5 : ℕ) ≠ 6 by omega)]; exact h5
      · simp only [uAccContract, List.getD_cons_zero, List.getD_cons_succ, argsSize,
          Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]
        have : 70 * (L - j) ≤ 70 * L := Nat.mul_le_mul_left _ (by omega)
        omega
  refine runs_start_le ?_
  unfold uMulProc
  refine runs_seq_triple_le hloop1 rfl ?_
  rintro st₁ hI1
  refine runs_seq_triple_le (hloop2 st₁ hI1) rfl ?_
  rintro st ⟨-, -, hfr, hvd, heq⟩
  refine runs_ret_le (v := 0) (by eval_expr)
    ⟨d, a, bb, L, rfl, rfl, hfr, hvd, heq⟩ ?_
  simp only [uMulContract, hargs, List.getD_cons_zero, List.getD_cons_succ, Expr.size_const,
    Expr.size_reg, Expr.size_bin, Expr.size_load]
  have h1 : L * (70 * L + 60 + 1 + 8) = 70 * (L * L) + 69 * L := by ring
  have h2 : 80 * L * L = 80 * (L * L) := by ring
  simp only [Nat.sub_zero]
  omega

end MinCostFlow.LSF.Program
