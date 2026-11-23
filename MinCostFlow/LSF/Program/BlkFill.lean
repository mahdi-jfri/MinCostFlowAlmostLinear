module

public import MinCostFlow.LSF.Program.UExt
public import MinCostFlow.LSF.Program.TopDownPass

/-!
# Filling arrays of blocks

Two small loops that the stretch pass (`Wstr.lean`) runs before the levels.

* `idFillProc` writes `id[x] = x` for `x < n`. The pass of the distances to the roots uses this
  array as the second end of each pair.
* `blkExtLoopProc` writes `n` blocks of `LB` limbs. For `i < lim` block `i` is the `L_in`-limb
  block at `src + idx[i] · L_in`, widened to `LB` limbs. For `i ≥ lim` block `i` is zero. With
  `lim = n` it widens the lengths of a list of edges; with `lim = 0` it zeroes an array of blocks.
  The cost is `O(n LB)`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num

/-! ## The identity array -/

/-- Args: `[n, idPtr]`. Register `2` is the index `x`. -/
def idFillProc : Stmt :=
  forRange 2 (.const 0) (.reg 0) (.store (.bin .add (.reg 1) (.reg 2)) (.reg 2)) ;;
  .ret (.const 0)

lemma idFillProc_noRand : idFillProc.NoRand := by
  simp [idFillProc, forRange, forUp, Stmt.NoRand]

/-- The contract of `idFillProc`. -/
def idFillContract (w : ℕ) : Contract where
  pre args _ := ∃ n idPtr, args = [n, idPtr] ∧ 16 ≤ 2 ^ w ∧ idPtr + n < 2 ^ w
  post args mem ret mem' := ∃ n idPtr, args = [n, idPtr] ∧ ret = 0 ∧
    (∀ a, a < idPtr ∨ idPtr + n ≤ a → mem' a = mem a) ∧ ∀ x < n, mem' (idPtr + x) = x
  cost args _ := 20 * args.getD 0 0 + 20

theorem idFill_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some idFillProc) :
    MeetsContract w p b (idFillContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, idPtr, rfl, h16, hiw⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := by omega
  set args := [n, idPtr] with hargs
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs 0 = n ∧ st.regs 1 = idPtr ∧ st.regs 2 = j ∧
    (∀ a, a < idPtr ∨ idPtr + j ≤ a → st.mem a = mem a) ∧ ∀ x < j, st.mem (idPtr + x) = x
  have hloop : Triple w p (fun st => st = startState args mem pos)
      (forRange 2 (.const 0) (.reg 0) (.store (.bin .add (.reg 1) (.reg 2)) (.reg 2)))
      (normalPost (Inv n))
      (fun _ => (n - 0) * (5 + (Expr.reg 0).size + 8) +
        ((Expr.const 0).size + (Expr.reg 0).size + 5)) := by
    refine Triple.forRange_const 5 0 n (by omega) hw1 (fun _ => hnw) ?_ ?_ ?_ ?_
    · rintro st rfl
      exact ⟨by eval_expr, by simp [startState, hargs], by simp [startState, hargs], by simp,
        fun a _ => rfl, fun x hx => absurd hx (by omega)⟩
    · intro j st _ _ hI; exact hI.2.2.1
    · intro j st _ _ hI
      have r0 : st.regs 0 = n := hI.1
      eval_expr
    · intro j _ hjn st ω' hI
      obtain ⟨r0, r1, r2, hfr, hdone⟩ := hI
      refine runs_start_le ?_
      refine runs_store_le (x := idPtr + j) (v := j) (by eval_expr) (by eval_expr)
        ⟨⟨by simpa using r0, by simpa using r1, by simp, fun a ha => ?_, fun x hx => ?_⟩,
          by simpa using r2⟩ (by simp [Expr.size])
      · dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a (by omega)
      · dsimp only
        rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
        · rw [Function.update_of_ne (by omega)]; exact hdone x hx
        · rw [Function.update_self]
  refine runs_start_le ?_
  unfold idFillProc
  refine runs_seq_triple_le hloop rfl ?_
  rintro st ⟨-, -, -, hfr, hdone⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, idPtr, rfl, rfl, hfr, hdone⟩ ?_
  simp only [idFillContract, hargs, List.getD_cons_zero, Expr.size_const, Expr.size_reg]
  omega

/-! ## Widened or zero blocks -/

/-- One block (register `7` is `i`). Registers: `8 = [i < lim]`, `9 = idx[i] · [i < lim]`. -/
def blkExtBody (bExt : ℕ) : Stmt :=
  .assign 8 (.bin .lt (.reg 7) (.reg 6)) ;;
  .assign 9 (.bin .mul (.load (.bin .add (.reg 4) (.reg 7))) (.reg 8)) ;;
  .call 10 bExt [.bin .add (.reg 1) (.bin .mul (.reg 7) (.reg 2)),
    .bin .add (.reg 3) (.bin .mul (.reg 9) (.reg 5)), .bin .mul (.reg 8) (.reg 5), .reg 2]

/-- Args: `[n, dst, LB, src, idx, Lin, lim]`. -/
def blkExtLoopProc (bExt : ℕ) : Stmt :=
  forRange 7 (.const 0) (.reg 0) (blkExtBody bExt) ;;
  .ret (.const 0)

lemma blkExtLoopProc_noRand (bExt : ℕ) : (blkExtLoopProc bExt).NoRand := by
  simp [blkExtLoopProc, blkExtBody, forRange, forUp, Stmt.NoRand]

/-- The value of block `i`. -/
def blkExtVal (h : ℕ) (mem : ℕ → ℕ) (src idx Lin lim i : ℕ) : ℕ :=
  if i < lim then unsignedVal mem (src + mem (idx + i) * Lin) h Lin else 0

/-- The contract of `blkExtLoopProc`. The sources lie below the blocks. -/
def blkExtLoopContract (w h : ℕ) : Contract where
  pre args mem := ∃ (n dst LB src idx Lin lim : ℕ),
    args = [n, dst, LB, src, idx, Lin, lim] ∧ 16 ≤ 2 ^ w ∧ 1 ≤ Lin ∧ Lin ≤ LB ∧
    (∀ i < n, i < lim → Valid mem (src + mem (idx + i) * Lin) h Lin ∧
      src + mem (idx + i) * Lin + LB ≤ dst) ∧
    src + LB ≤ dst ∧ idx + n ≤ dst ∧ dst + n * LB < 2 ^ w
  post args mem ret mem' := ∃ (n dst LB src idx Lin lim : ℕ),
    args = [n, dst, LB, src, idx, Lin, lim] ∧ ret = 0 ∧
    (∀ a, a < dst ∨ dst + n * LB ≤ a → mem' a = mem a) ∧
    ∀ i < n, Valid mem' (dst + i * LB) h LB ∧
      unsignedVal mem' (dst + i * LB) h LB = blkExtVal h mem src idx Lin lim i
  cost args _ := args.getD 0 0 * (30 * args.getD 2 0 + 80) + 20

theorem blkExtLoop_meetsContract {w h : ℕ} {p : Program} {b bExt : ℕ}
    (hExt : MeetsContract w p bExt (uExtContract w h))
    (hp : p.procs[b]? = some (blkExtLoopProc bExt)) :
    MeetsContract w p b (blkExtLoopContract w h) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, dst, LB, src, idx, Lin, lim, rfl, h16, hLin1, hLin, hsrc, hsrc0, hidx, hdw⟩ := hpre
  set args := [n, dst, LB, src, idx, Lin, lim] with hargs
  have hnw : n < 2 ^ w := hwords n (by simp [hargs])
  have hLBw : LB < 2 ^ w := hwords LB (by simp [hargs])
  have hLinw : Lin < 2 ^ w := hwords Lin (by simp [hargs])
  have hlimw : lim < 2 ^ w := hwords lim (by simp [hargs])
  have hw1 : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun j st =>
    (∀ i < 7, st.regs i = args.getD i 0) ∧ st.regs 7 = j ∧
    (∀ a, a < dst ∨ dst + j * LB ≤ a → st.mem a = mem a) ∧
    ∀ i < j, Valid st.mem (dst + i * LB) h LB ∧
      unsignedVal st.mem (dst + i * LB) h LB = blkExtVal h mem src idx Lin lim i
  have hloop : Triple w p (fun st => st = startState args mem pos)
      (forRange 7 (.const 0) (.reg 0) (blkExtBody bExt)) (normalPost (Inv n))
      (fun _ => (n - 0) * ((30 * LB + 70) + (Expr.reg 0).size + 8) +
        ((Expr.const 0).size + (Expr.reg 0).size + 5)) := by
    refine Triple.forRange_const (30 * LB + 70) 0 n (by omega) hw1 (fun _ => hnw) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, fun i hi => ?_, by simp, fun a _ => rfl,
        fun t ht => absurd ht (by omega)⟩
      simp only [Function.update_of_ne (show i ≠ 7 by omega)]
      interval_cases i <;> simp [startState, hargs]
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = n := hI.1 0 (by omega)
      eval_expr
    · intro t _ htn st ω' hI
      obtain ⟨hR, h7, hfr, hdone⟩ := hI
      have r1 : st.regs 1 = dst := hR 1 (by omega)
      have r2 : st.regs 2 = LB := hR 2 (by omega)
      have r3 : st.regs 3 = src := hR 3 (by omega)
      have r4 : st.regs 4 = idx := hR 4 (by omega)
      have r5 : st.regs 5 = Lin := hR 5 (by omega)
      have r6 : st.regs 6 = lim := hR 6 (by omega)
      have hbt := blk_end LB htn
      have hlow : ∀ a, a < dst → st.mem a = mem a := fun a ha => hfr a (Or.inl ha)
      set fl := if t < lim then 1 else 0 with hfl
      set q := mem (idx + t) with hq
      have hmq : st.mem (idx + t) = q := hlow _ (by omega)
      -- the source block and its address
      have hsrcT : Valid mem (src + q * fl * Lin) h (fl * Lin) ∧
          src + q * fl * Lin + LB ≤ dst := by
        by_cases hl : t < lim
        · have := hsrc t htn hl
          simp only [hfl, if_pos hl, mul_one, one_mul]
          exact this
        · simp only [hfl, if_neg hl, mul_zero, zero_mul, add_zero]
          exact ⟨fun i hi => absurd hi (by omega), hsrc0⟩
      have hqfl : q * fl * Lin < 2 ^ w := by omega
      have hqf : q * fl < 2 ^ w :=
        lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega)) hqfl
      have hflLin : fl * Lin ≤ LB := by
        by_cases hl : t < lim
        · simp only [hfl, if_pos hl, one_mul]; exact hLin
        · simp only [hfl, if_neg hl, zero_mul]; omega
      refine runs_start_le ?_
      unfold blkExtBody
      refine runs_seq_assign_le (v := fl) (by
        simp only [hfl]
        eval_expr) ?_
      refine runs_seq_assign_le (v := q * fl) (by
        have hqf' : st.mem (idx + t) * fl < 2 ^ w := by rw [hmq]; exact hqf
        rw [← hmq]; eval_expr) ?_
      refine runs_call_le (vs := [dst + t * LB, src + q * fl * Lin, fl * Lin, LB]) hExt
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
        (by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl <;> omega)
        ⟨_, _, _, _, rfl, hflLin, fun i hi => by rw [hlow _ (by omega)]; exact hsrcT.1 i hi,
          Or.inl (by omega), by omega, by omega⟩ ?_
      rintro v₁ mem₁ pos₁ ⟨d₁, a₁, La₁, L₁, heq₁, -, hfr₁, hv₁, hu₁⟩
      simp only [List.cons.injEq, and_true] at heq₁
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq₁
      have hUs : unsignedVal st.mem (src + q * fl * Lin) h (fl * Lin) =
          blkExtVal h mem src idx Lin lim t := by
        rw [unsignedVal_congr (fun i hi => hlow _ (by omega))]
        unfold blkExtVal
        by_cases hl : t < lim
        · simp only [hfl, if_pos hl, mul_one, one_mul, hq]
        · simp only [hfl, if_neg hl, mul_zero, zero_mul]
          rfl
      refine ⟨⟨⟨fun i hi => ?_, ?_, fun a ha => ?_, fun t' ht' => ?_⟩, ?_⟩, ?_⟩
      · dsimp only
        simp only [Function.update_of_ne (show i ≠ 7 by omega),
          Function.update_of_ne (show i ≠ 10 by omega), Function.update_of_ne (show i ≠ 9 by omega),
          Function.update_of_ne (show i ≠ 8 by omega)]
        exact hR i hi
      · simp
      · dsimp only
        have hs : (t + 1) * LB = t * LB + LB := Nat.succ_mul t LB
        rw [hfr₁ a (by omega)]
        exact hfr a (by omega)
      · dsimp only
        rcases Nat.lt_succ_iff_lt_or_eq.mp ht' with ht' | rfl
        · have hb' := blk_end LB ht'
          have hd' := blk_disj LB (show t' ≠ t by omega)
          have hag : ∀ i < LB, mem₁ (dst + t' * LB + i) = st.mem (dst + t' * LB + i) :=
            fun i hi => hfr₁ _ (by omega)
          obtain ⟨hv', hu'⟩ := hdone t' ht'
          exact ⟨fun i hi => by rw [hag i hi]; exact hv' i hi, by rw [unsignedVal_congr hag, hu']⟩
        · exact ⟨hv₁, by rw [hu₁, hUs]⟩
      · simp only [Function.update_of_ne (show (7 : ℕ) ≠ 10 by omega),
          Function.update_of_ne (show (7 : ℕ) ≠ 9 by omega),
          Function.update_of_ne (show (7 : ℕ) ≠ 8 by omega)]
        exact h7
      · simp only [uExtContract, List.getD_cons_zero, List.getD_cons_succ, argsSize,
          Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]
        omega
  refine runs_start_le ?_
  unfold blkExtLoopProc
  refine runs_seq_triple_le hloop rfl ?_
  rintro st ⟨-, -, hfr, hdone⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, dst, LB, src, idx, Lin, lim, rfl, rfl, hfr,
    hdone⟩ ?_
  simp only [blkExtLoopContract, hargs, List.getD_cons_zero, List.getD_cons_succ, Expr.size_const,
    Expr.size_reg]
  have h1 : (n - 0) * (30 * LB + 70 + 1 + 8) ≤ n * (30 * LB + 80) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

end MinCostFlow.LSF.Program
