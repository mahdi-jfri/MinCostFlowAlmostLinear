module

public import MinCostFlow.LSF.Program.Lemma55StepBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Single-Edge Fixed-Point Weight Update and `ρ` Builder for Lemma 5.5 (`Lemma55Step`)

Defines and verifies the two deterministic Word-RAM subroutines used by the Lemma 5.5
multiplicative-weights driver (`arXiv:2309.16629v1`, page 17 and Appendix A.2, pages 48–49):
`buildRhoFpProc` / `buildRhoFp_runs` and `mwuEdgeStepProc` / `mwuEdgeStep_runs`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.Num

@[expose] public section

/-! ## WordRAM Procedure 1: `buildRhoFpProc` -/

/-- Compute `ρ_fp = lemma55RhoNat K_AN n0 k_nat · 2^P_fp` into `L_w` limbs at `dst`, using
`4 * L_w` scratch words at `scratch` (cleared back to `0` on exit).
Args: `[dst, n0, k_nat, L_w, pLimb, scratch]`. Returns `0`. -/
def buildRhoFpProc (bLog bEmit bLoad bMul bFill : ℕ) : Stmt :=
  .call 6 bFill [.reg 0, .reg 3, .const 0] ;;
  .assign 6 (.bin .sub (.reg 3) (.reg 4)) ;;
  .assign 7 (.bin .add (.reg 0) (.reg 4)) ;;
  .assign 8 (.reg 5) ;;
  .assign 9 (.bin .add (.reg 8) (.reg 6)) ;;
  .assign 10 (.bin .add (.reg 9) (.reg 6)) ;;
  .assign 11 (.bin .add (.reg 10) (.reg 6)) ;;
  .call 12 bLog [.bin .add (.reg 1) (.const 2)] ;;
  .assign 12 (.bin .add (.reg 12) (.const 1)) ;;
  .call 13 bEmit [.reg 8, .reg 6] ;;
  .call 13 bLoad [.reg 9, .reg 6, .reg 2] ;;
  .call 13 bMul [.reg 10, .reg 8, .reg 9, .reg 6] ;;
  .call 13 bLoad [.reg 8, .reg 6, .reg 12] ;;
  .call 13 bMul [.reg 9, .reg 8, .reg 8, .reg 6] ;;
  .call 13 bMul [.reg 11, .reg 9, .reg 9, .reg 6] ;;
  .call 13 bMul [.reg 8, .reg 11, .reg 9, .reg 6] ;;
  .call 13 bMul [.reg 7, .reg 10, .reg 8, .reg 6] ;;
  .call 13 bFill [.reg 5, .bin .mul (.const 4) (.reg 3), .const 0] ;;
  .ret (.const 0)

lemma buildRhoFpProc_noRand (bLog bEmit bLoad bMul bFill : ℕ) :
    (buildRhoFpProc bLog bEmit bLoad bMul bFill).NoRand := by
  simp [buildRhoFpProc, Stmt.NoRand]

/-- Execution theorem for `buildRhoFpProc`. -/
theorem buildRhoFp_runs {w h bLog bEmit bLoad bMul bFill dst n0 k_nat L_w P_fp scratch : ℕ}
    {K_AN : ℝ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ}
    (hh : 1 ≤ h) (hw : 3 * h + 2 ≤ w) (hk : 1 ≤ k_nat)
    (hdiv : h ∣ P_fp) (hP_le : P_fp / h ≤ L_w)
    (hrho_fit : 2 * (lemma55RhoNat K_AN n0 k_nat * 2 ^ P_fp) < capacity h L_w)
    (hn0_ltw : n0 + 2 < 2 ^ w) (hk_ltw : k_nat < 2 ^ w)
    (hdst_ltw : dst + L_w < 2 ^ w) (hscr_ltw : scratch + 4 * L_w < 2 ^ w)
    (hdisj : dst + L_w ≤ scratch ∨ scratch + 4 * L_w ≤ dst)
    (hLog : MeetsContract w p bLog log2Contract)
    (hEmit : MeetsContract w p bEmit (emitNatContract w (lemma55RhoConst K_AN) h))
    (hLoad : MeetsContract w p bLoad (uLoadWordContract w h))
    (hMul : MeetsContract w p bMul (uMulContract w h))
    (hFill : MeetsContract w p bFill (memFillContract w)) :
    ∃ st' c,
      Runs w p ω (buildRhoFpProc bLog bEmit bLoad bMul bFill)
        (startState [dst, n0, k_nat, L_w, P_fp / h, scratch] mem pos) (.returned 0) st' c ∧
      Valid st'.mem dst h L_w ∧
      intVal st'.mem dst h L_w = (lemma55RhoNat K_AN n0 k_nat : ℤ) * (2 : ℤ) ^ P_fp ∧
      (∀ i < 4 * L_w, st'.mem (scratch + i) = 0) ∧
      (∀ z, (z < dst ∨ dst + L_w ≤ z) → (z < scratch ∨ scratch + 4 * L_w ≤ z) →
        st'.mem z = mem z) ∧
      c ≤ 500 * L_w * L_w + 800 * L_w + 20 * Nat.log 2 (n0 + 2) + 800 := by
  set pL := P_fp / h
  set rem := L_w - pL
  set d := Nat.log 2 (n0 + 2) + 1
  set C0 := lemma55RhoConst K_AN
  have h2w_16 : 16 ≤ 2 ^ w := by
    have : 2 ^ 5 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hbw : base h < 2 ^ w := base_lt_word (by omega)
  have hrem_cap : lemma55RhoNat K_AN n0 k_nat < capacity h rem := by
    have hmul : h * pL = P_fp := Nat.mul_div_cancel' hdiv
    have hcap_split : capacity h L_w = capacity h rem * 2 ^ P_fp := by
      rw [capacity_eq_two_pow, capacity_eq_two_pow, ← pow_add, ← hmul, ← Nat.mul_add,
        Nat.sub_add_cancel hP_le]
    rw [hcap_split] at hrho_fit
    have h2P_pos : 0 < 2 ^ P_fp := by positivity
    nlinarith
  have hd_pos : 1 ≤ d := by omega
  have hC0_pos : 1 ≤ C0 := by
    have := (defaultC_ceil_ge K_AN).2
    dsimp [C0, lemma55RhoConst, defaultK_sigma]; omega
  have hrho_eq : lemma55RhoNat K_AN n0 k_nat = C0 * k_nat * d ^ 6 := rfl
  have hC0_lt : C0 < capacity h rem := by
    have : C0 ≤ C0 * k_nat * d ^ 6 := by
      have h1 : 1 ≤ k_nat * d ^ 6 := Nat.mul_pos hk (Nat.one_le_pow _ _ hd_pos)
      calc C0 = C0 * 1 := (Nat.mul_one _).symm
        _ ≤ C0 * (k_nat * d ^ 6) := Nat.mul_le_mul_left _ h1
        _ = C0 * k_nat * d ^ 6 := by ring
    omega
  have hk_lt_cap : k_nat < capacity h rem := by
    have : k_nat ≤ C0 * k_nat * d ^ 6 := by
      have h1 : 1 ≤ C0 * d ^ 6 := Nat.mul_pos hC0_pos (Nat.one_le_pow _ _ hd_pos)
      calc k_nat = k_nat * 1 := (Nat.mul_one _).symm
        _ ≤ k_nat * (C0 * d ^ 6) := Nat.mul_le_mul_left _ h1
        _ = C0 * k_nat * d ^ 6 := by ring
    omega
  have hCk_lt : C0 * k_nat < capacity h rem := by
    have : C0 * k_nat ≤ C0 * k_nat * d ^ 6 := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hd_pos)
    omega
  have hd_lt_cap : d < capacity h rem := by
    have h1 : d ≤ d ^ 6 := le_self_pow₀ hd_pos (by decide)
    have h2 : d ^ 6 ≤ C0 * k_nat * d ^ 6 := Nat.le_mul_of_pos_left _ (Nat.mul_pos hC0_pos hk)
    omega
  have hd2_lt : d * d < capacity h rem := by
    have h1 : d * d = d ^ 2 := by ring
    have h2 : d ^ 2 ≤ d ^ 6 := Nat.pow_le_pow_right hd_pos (by decide)
    have h3 : d ^ 6 ≤ C0 * k_nat * d ^ 6 := Nat.le_mul_of_pos_left _ (Nat.mul_pos hC0_pos hk)
    omega
  have hd4_lt : (d * d) * (d * d) < capacity h rem := by
    have h1 : (d * d) * (d * d) = d ^ 4 := by ring
    have h2 : d ^ 4 ≤ d ^ 6 := Nat.pow_le_pow_right hd_pos (by decide)
    have h3 : d ^ 6 ≤ C0 * k_nat * d ^ 6 := Nat.le_mul_of_pos_left _ (Nat.mul_pos hC0_pos hk)
    omega
  have hd6_lt : ((d * d) * (d * d)) * (d * d) < capacity h rem := by
    have h1 : ((d * d) * (d * d)) * (d * d) = d ^ 6 := by ring
    have h2 : d ^ 6 ≤ C0 * k_nat * d ^ 6 := Nat.le_mul_of_pos_left _ (Nat.mul_pos hC0_pos hk)
    omega
  have hnat_len : (natLimbs h C0).length ≤ rem :=
    (natLimbs_length_le_iff (by omega)).mpr hC0_lt
  have hd_ltw : d < 2 ^ w := by
    have hlog_lt : Nat.log 2 (n0 + 2) < w := Nat.log_lt_of_lt_pow (by omega) hn0_ltw
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    omega
  set t0 := scratch
  set t1 := scratch + rem
  set t2 := scratch + rem + rem
  set t3 := scratch + rem + rem + rem
  set dstHi := dst + pL
  have hpL_le : pL ≤ L_w := hP_le
  have hrem_le : rem ≤ L_w := Nat.sub_le _ _
  have hbuf_bds :
      dstHi + rem = dst + L_w ∧
      t0 + rem = t1 ∧ t1 + rem = t2 ∧ t2 + rem = t3 ∧ t3 + rem ≤ scratch + 4 * L_w := by
    refine ⟨by change dst + pL + (L_w - pL) = dst + L_w; omega, rfl, rfl, rfl,
      by change scratch + rem + rem + rem + rem ≤ scratch + 4 * L_w; omega⟩
  suffices hmain : ∃ o st' c,
      Runs w p ω (buildRhoFpProc bLog bEmit bLoad bMul bFill)
        (startState [dst, n0, k_nat, L_w, pL, scratch] mem pos) o st' c ∧
      (o = .returned 0 ∧
        Valid st'.mem dst h L_w ∧
        intVal st'.mem dst h L_w = (lemma55RhoNat K_AN n0 k_nat : ℤ) * (2 : ℤ) ^ P_fp ∧
        (∀ i < 4 * L_w, st'.mem (scratch + i) = 0) ∧
        ∀ z, (z < dst ∨ dst + L_w ≤ z) → (z < scratch ∨ scratch + 4 * L_w ≤ z) →
          st'.mem z = mem z) ∧
      0 + c ≤ 500 * L_w * L_w + 800 * L_w + 20 * Nat.log 2 (n0 + 2) + 800 by
    rcases hmain with ⟨_, st', c, hrun, ⟨rfl, h1, h2, h3, h4⟩, hc⟩
    exact ⟨st', c, hrun, h1, h2, h3, h4, by omega⟩
  have hr0 : (startState [dst, n0, k_nat, L_w, pL, scratch] mem pos).regs 0 = dst := by simp [startState]
  have hr1 : (startState [dst, n0, k_nat, L_w, pL, scratch] mem pos).regs 1 = n0 := by simp [startState]
  have hr2 : (startState [dst, n0, k_nat, L_w, pL, scratch] mem pos).regs 2 = k_nat := by simp [startState]
  have hr3 : (startState [dst, n0, k_nat, L_w, pL, scratch] mem pos).regs 3 = L_w := by simp [startState]
  have hr4 : (startState [dst, n0, k_nat, L_w, pL, scratch] mem pos).regs 4 = pL := by simp [startState]
  have hr5 : (startState [dst, n0, k_nat, L_w, pL, scratch] mem pos).regs 5 = scratch := by simp [startState]
  dsimp only [buildRhoFpProc]
  -- 1. Fill [dst, dst + L_w) with 0
  refine runs_seq_call_le hFill (vs := [dst, L_w, 0])
    (by simp [evalArgs, Expr.eval, hr0, hr3, show 0 < 2 ^ w by omega])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> omega)
    ⟨dst, L_w, 0, rfl, hdst_ltw⟩ ?_
  intro ret0 mem1 pos1 hpost0
  rcases hpost0 with ⟨_, _, _, hEq0, _, hfill0, hfr0⟩
  simp only [List.cons.injEq, and_true] at hEq0
  rcases hEq0 with ⟨rfl, rfl, rfl⟩
  -- 2. Assign rem, dstHi, t0, t1, t2, t3
  refine runs_seq_assign_le (v := rem)
    (by simp [Expr.eval, BinOp.eval, hr3, hr4, rem, show L_w - pL < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := dstHi)
    (by simp [Expr.eval, BinOp.eval, hr0, hr4, dstHi, show dst + pL < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := t0) (by simp [Expr.eval, hr5, t0]) ?_
  refine runs_seq_assign_le (v := t1)
    (by simp [Expr.eval, BinOp.eval, t0, t1, show scratch + rem < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := t2)
    (by simp [Expr.eval, BinOp.eval, t1, t2, show scratch + rem + rem < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := t3)
    (by simp [Expr.eval, BinOp.eval, t2, t3, show scratch + rem + rem + rem < 2 ^ w by omega]) ?_
  -- 3. Call log2(n0 + 2), add 1 -> d
  refine runs_seq_call_le hLog (vs := [n0 + 2])
    (by simp [evalArgs, Expr.eval, BinOp.eval, hr1, show 2 < 2 ^ w by omega, hn0_ltw])
    (by intro z hz; simp only [List.mem_singleton] at hz; subst z; exact hn0_ltw)
    ⟨n0 + 2, rfl, by omega⟩ ?_
  intro ret1 mem2 pos2 hpost1
  rcases hpost1 with ⟨_, hEq1, rfl, hret1⟩
  simp only [List.cons.injEq, and_true] at hEq1; subst hEq1
  refine runs_seq_assign_le (v := d)
    (by simp [Expr.eval, BinOp.eval, hret1, d, show 1 < 2 ^ w by omega,
        show Nat.log 2 (n0 + 2) + 1 < 2 ^ w from hd_ltw]) ?_
  -- 4. Call emitNat(t0, rem) -> C0
  refine runs_seq_call_le hEmit (vs := [t0, rem])
    (by simp [evalArgs, Expr.eval])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl <;> omega)
    ⟨t0, rem, rfl, hh, hbw, hnat_len, by omega⟩ ?_
  intro _ mem3 _ hpost2
  rcases hpost2 with ⟨_, _, hEq2, _, hv_t0_3, hu_t0_3, hfr3⟩
  simp only [List.cons.injEq, and_true] at hEq2; rcases hEq2 with ⟨rfl, rfl⟩
  -- 5. Call uLoadWord(t1, rem, k_nat) -> k_nat
  refine runs_seq_call_le hLoad (vs := [t1, rem, k_nat])
    (by simp [evalArgs, Expr.eval, hr2])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> omega)
    ⟨t1, rem, k_nat, rfl, by omega⟩ ?_
  intro _ mem4 _ hpost3
  rcases hpost3 with ⟨_, _, _, hEq3, _, hfr4, hv_t1_4, hu_t1_4⟩
  simp only [List.cons.injEq, and_true] at hEq3; rcases hEq3 with ⟨rfl, rfl, rfl⟩
  have hmem4_t0 : ∀ i < rem, mem4 (t0 + i) = mem3 (t0 + i) := fun i hi => hfr4 _ (Or.inl (by omega))
  have hv_t0_4 : Valid mem4 t0 h rem := fun i hi => by rw [hmem4_t0 i hi]; exact hv_t0_3 i hi
  have hu_t0_4 : unsignedVal mem4 t0 h rem = C0 :=
    (unsignedVal_congr hmem4_t0).trans hu_t0_3
  -- 6. Call uMul(t2, t0, t1, rem) -> C0 * k_nat
  refine runs_seq_call_le hMul (vs := [t2, t0, t1, rem])
    (by simp [evalArgs, Expr.eval])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl <;> omega)
    ⟨t2, t0, t1, rem, rfl, hv_t0_4, hv_t1_4, Or.inl (by omega), Or.inl (by omega),
      by omega, by omega, by omega⟩ ?_
  intro _ mem5 _ hpost4
  rcases hpost4 with ⟨_, _, _, _, hEq4, _, hfr5, hv_t2_5, hu_t2_5⟩
  simp only [List.cons.injEq, and_true] at hEq4; rcases hEq4 with ⟨rfl, rfl, rfl, rfl⟩
  rw [hu_t0_4, hu_t1_4, Nat.mod_eq_of_lt hk_lt_cap, Nat.mod_eq_of_lt hCk_lt] at hu_t2_5
  -- 7. Call uLoadWord(t0, rem, d) -> d
  refine runs_seq_call_le hLoad (vs := [t0, rem, d])
    (by simp [evalArgs, Expr.eval])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> omega)
    ⟨t0, rem, d, rfl, by omega⟩ ?_
  intro _ mem6 _ hpost5
  rcases hpost5 with ⟨_, _, _, hEq5, _, hfr6, hv_t0_6, hu_t0_6⟩
  simp only [List.cons.injEq, and_true] at hEq5; rcases hEq5 with ⟨rfl, rfl, rfl⟩
  rw [Nat.mod_eq_of_lt hd_lt_cap] at hu_t0_6
  -- 8. Call uMul(t1, t0, t0, rem) -> d^2
  refine runs_seq_call_le hMul (vs := [t1, t0, t0, rem])
    (by simp [evalArgs, Expr.eval])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl <;> omega)
    ⟨t1, t0, t0, rem, rfl, hv_t0_6, hv_t0_6, Or.inl (by omega), Or.inl (by omega),
      by omega, by omega, by omega⟩ ?_
  intro _ mem7 _ hpost6
  rcases hpost6 with ⟨_, _, _, _, hEq6, _, hfr7, hv_t1_7, hu_t1_7⟩
  simp only [List.cons.injEq, and_true] at hEq6; rcases hEq6 with ⟨rfl, rfl, rfl, rfl⟩
  rw [hu_t0_6, Nat.mod_eq_of_lt hd2_lt] at hu_t1_7
  -- 9. Call uMul(t3, t1, t1, rem) -> d^4
  refine runs_seq_call_le hMul (vs := [t3, t1, t1, rem])
    (by simp [evalArgs, Expr.eval])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl <;> omega)
    ⟨t3, t1, t1, rem, rfl, hv_t1_7, hv_t1_7, Or.inl (by omega), Or.inl (by omega),
      by omega, by omega, by omega⟩ ?_
  intro _ mem8 _ hpost7
  rcases hpost7 with ⟨_, _, _, _, hEq7, _, hfr8, hv_t3_8, hu_t3_8⟩
  simp only [List.cons.injEq, and_true] at hEq7; rcases hEq7 with ⟨rfl, rfl, rfl, rfl⟩
  rw [hu_t1_7, Nat.mod_eq_of_lt hd4_lt] at hu_t3_8
  have hmem8_t1 : ∀ i < rem, mem8 (t1 + i) = mem7 (t1 + i) := fun i hi => hfr8 _ (Or.inl (by omega))
  have hv_t1_8 : Valid mem8 t1 h rem := fun i hi => by rw [hmem8_t1 i hi]; exact hv_t1_7 i hi
  have hu_t1_8 : unsignedVal mem8 t1 h rem = d * d :=
    (unsignedVal_congr hmem8_t1).trans hu_t1_7
  -- 10. Call uMul(t0, t3, t1, rem) -> d^6
  refine runs_seq_call_le hMul (vs := [t0, t3, t1, rem])
    (by simp [evalArgs, Expr.eval])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl <;> omega)
    ⟨t0, t3, t1, rem, rfl, hv_t3_8, hv_t1_8, Or.inr (by omega), Or.inr (by omega),
      by omega, by omega, by omega⟩ ?_
  intro _ mem9 _ hpost8
  rcases hpost8 with ⟨_, _, _, _, hEq8, _, hfr9, hv_t0_9, hu_t0_9⟩
  simp only [List.cons.injEq, and_true] at hEq8; rcases hEq8 with ⟨rfl, rfl, rfl, rfl⟩
  rw [hu_t3_8, hu_t1_8, Nat.mod_eq_of_lt hd6_lt] at hu_t0_9
  have hmem9_t2 : ∀ i < rem, mem9 (t2 + i) = mem5 (t2 + i) := fun i hi =>
    (hfr9 _ (Or.inr (by omega))).trans ((hfr8 _ (Or.inl (by omega))).trans
      ((hfr7 _ (Or.inr (by omega))).trans (hfr6 _ (Or.inr (by omega)))))
  have hv_t2_9 : Valid mem9 t2 h rem := fun i hi => by rw [hmem9_t2 i hi]; exact hv_t2_5 i hi
  have hu_t2_9 : unsignedVal mem9 t2 h rem = C0 * k_nat :=
    (unsignedVal_congr hmem9_t2).trans hu_t2_5
  -- 11. Call uMul(dstHi, t2, t0, rem) -> C0 * k_nat * d^6 = lemma55RhoNat
  refine runs_seq_call_le hMul (vs := [dstHi, t2, t0, rem])
    (by simp [evalArgs, Expr.eval])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl <;> omega)
    ⟨dstHi, t2, t0, rem, rfl, hv_t2_9, hv_t0_9,
      by rcases hdisj with h | h <;> [right; left] <;> omega,
      by rcases hdisj with h | h <;> [right; left] <;> omega,
      by omega, by omega, by omega⟩ ?_
  intro _ mem10 _ hpost9
  rcases hpost9 with ⟨_, _, _, _, hEq9, _, hfr10, hv_dh_10, hu_dh_10⟩
  simp only [List.cons.injEq, and_true] at hEq9; rcases hEq9 with ⟨rfl, rfl, rfl, rfl⟩
  have hprod_eq : C0 * k_nat * (((d * d) * (d * d)) * (d * d)) = lemma55RhoNat K_AN n0 k_nat := by
    rw [hrho_eq]; ring
  rw [hu_t2_9, hu_t0_9, hprod_eq, Nat.mod_eq_of_lt hrem_cap] at hu_dh_10
  -- 12. Clear scratch [scratch, scratch + 4 * L_w) back to 0
  refine runs_seq_call_le hFill (vs := [scratch, 4 * L_w, 0])
    (by simp [evalArgs, Expr.eval, BinOp.eval, hr3, hr5, show 4 < 2 ^ w by omega,
        show 0 < 2 ^ w by omega, show 4 * L_w < 2 ^ w by omega])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> omega)
    ⟨scratch, 4 * L_w, 0, rfl, hscr_ltw⟩ ?_
  intro _ mem11 _ hpost10
  rcases hpost10 with ⟨_, _, _, hEq10, _, hfill10, hfr11⟩
  simp only [List.cons.injEq, and_true] at hEq10; rcases hEq10 with ⟨rfl, rfl, rfl⟩
  dsimp only [startState] at hfr0 hfr3 hfr4 hfr5 hfr6 hfr7 hfr8 hfr9 hfr10 hfr11
  have hmem11_dst : ∀ z, dst ≤ z → z < dst + L_w → mem11 z = mem10 z := fun z hz1 hz2 =>
    hfr11 z (by rcases hdisj with h | h <;> [left; right] <;> omega)
  have hlow_zero : ∀ i < pL, mem11 (dst + i) = 0 := fun i hi => by
    rw [hmem11_dst _ (by omega) (by omega), hfr10 _ (Or.inl (by omega)),
      hfr9 _ (by rcases hdisj with h | h <;> [left; right] <;> omega),
      hfr8 _ (by rcases hdisj with h | h <;> [left; right] <;> omega),
      hfr7 _ (by rcases hdisj with h | h <;> [left; right] <;> omega),
      hfr6 _ (by rcases hdisj with h | h <;> [left; right] <;> omega),
      hfr5 _ (by rcases hdisj with h | h <;> [left; right] <;> omega),
      hfr4 _ (by rcases hdisj with h | h <;> [left; right] <;> omega),
      hfr3 _ (by rcases hdisj with h | h <;> [left; right] <;> omega)]
    exact hfill0 i (by omega)
  have hhi_val : Valid mem11 (dst + pL) h rem := fun i hi => by
    rw [hmem11_dst _ (by omega) (by omega)]; exact hv_dh_10 i hi
  have hhi_u : unsignedVal mem11 (dst + pL) h rem = lemma55RhoNat K_AN n0 k_nat :=
    (unsignedVal_congr fun i hi => hmem11_dst _ (by omega) (by omega)).trans hu_dh_10
  obtain ⟨hv_dst, hint_dst⟩ := lemma55_shift_limbs hdiv hP_le hlow_zero hhi_val hhi_u hrho_fit
  have hfr_all : ∀ z, (z < dst ∨ dst + L_w ≤ z) → (z < scratch ∨ scratch + 4 * L_w ≤ z) →
      mem11 z = mem z := fun z hzd hzs => by
    rw [hfr11 z hzs, hfr10 z (by rcases hzd with h | h <;> [left; right] <;> omega),
      hfr9 z (by rcases hzs with h | h <;> [left; right] <;> omega),
      hfr8 z (by rcases hzs with h | h <;> [left; right] <;> omega),
      hfr7 z (by rcases hzs with h | h <;> [left; right] <;> omega),
      hfr6 z (by rcases hzs with h | h <;> [left; right] <;> omega),
      hfr5 z (by rcases hzs with h | h <;> [left; right] <;> omega),
      hfr4 z (by rcases hzs with h | h <;> [left; right] <;> omega),
      hfr3 z (by rcases hzs with h | h <;> [left; right] <;> omega),
      hfr0 z hzd]
  refine runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega])
    ⟨rfl, hv_dst, hint_dst, hfill10, hfr_all⟩ ?_
  dsimp only [memFillContract, log2Contract, emitNatContract, uLoadWordContract, uMulContract,
    argsSize, Expr.size]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  have hrem_le : rem ≤ L_w := Nat.sub_le _ _
  have h80_sq : 80 * rem * rem ≤ 80 * L_w * L_w := by
    rw [Nat.mul_assoc, Nat.mul_assoc]
    exact Nat.mul_le_mul_left 80 (Nat.mul_le_mul hrem_le hrem_le)
  have h500 : 500 * L_w * L_w = 500 * (L_w * L_w) := Nat.mul_assoc _ _ _
  have h80L : 80 * L_w * L_w = 80 * (L_w * L_w) := Nat.mul_assoc _ _ _
  have hnat_le : (natLimbs h C0).length ≤ L_w := le_trans hnat_len hrem_le
  clear * - hrem_le h80_sq h500 h80L hnat_le
  omega

/-! ## WordRAM Procedure 2: `mwuEdgeStepProc` -/

/-- Scratch heap space above `tmpHeap` used (and cleared back to `0`) by `mwuEdgeStepProc`. -/
def mwuEdgeStepSpace (L_in L_w P_fp : ℕ) : ℕ :=
  2 * fixedDivideSpace L_w + positiveExponentialSpace L_w P_fp 1 + (11 * L_in + 1)

/-- Time bound for one call to `mwuEdgeStepProc`. -/
def mwuEdgeStepCost (L_in L_w P_fp : ℕ) : ℕ :=
  2 * ((3 * L_w) * (900 * L_w + 644) + 900 * L_w + 700) +
    positiveExponentialCost L_w P_fp 1 +
    ((2 * L_in) * (38 * (2 * L_in) + 35) + 269 * L_in + 248) +
    20 * L_in + 16 * mwuEdgeStepSpace L_in L_w P_fp + 200

/-- Single-edge MWU fixed-point update: computes `v' ≈ v · exp(wstr / ρ)` in `L_in` limbs at `wtPtr`
and clears temporary scratch `[tmpHeap, tmpHeap + mwuEdgeStepSpace)`.
Args: `[numPtr, denPtr, wtPtr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap]`. Returns `0`. -/
def mwuEdgeStepProc (bDiv bExp bMul bCopy bFill : ℕ) : Stmt :=
  .call 9 bDiv [.reg 0, .reg 1, .reg 6, .reg 7, .reg 8] ;;
  .call 10 bDiv [.bin .sub (.reg 9) (.reg 6), .reg 4, .reg 6, .reg 7, .reg 9] ;;
  .call 11 bExp [.bin .sub (.reg 10) (.reg 6), .reg 3, .reg 6, .reg 7, .const 1, .reg 10] ;;
  .call 12 bMul [.reg 2, .bin .sub (.reg 11) (.reg 6), .reg 5, .reg 7, .reg 11] ;;
  .call 13 bCopy [.reg 2, .bin .sub (.reg 12) (.reg 5), .reg 5] ;;
  .call 13 bFill [.reg 8, .bin .sub (.reg 12) (.reg 8), .const 0] ;;
  .ret (.const 0)

lemma mwuEdgeStepProc_noRand (bDiv bExp bMul bCopy bFill : ℕ) :
    (mwuEdgeStepProc bDiv bExp bMul bCopy bFill).NoRand := by
  simp [mwuEdgeStepProc, Stmt.NoRand]

/-- Execution theorem for `mwuEdgeStepProc`. -/
theorem mwuEdgeStep_runs {w h q bDiv bExp bMul bCopy bFill
    numPtr denPtr wtPtr onePtr rhoPtr L_in L_w P_fp tmpHeap k_nat m0 rho_nat : ℕ}
    {wstr v : ℝ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ}
    (hh : 1 ≤ h) (hw : 3 * h + 2 ≤ w) (hLin_le : L_in ≤ L_w) (hk : 1 ≤ k_nat)
    (hdiv : h ∣ P_fp) (hq_P : q + 11 ≤ P_fp) (hk_q : 8 * k_nat ≤ 2 ^ q)
    (hP_Lin : P_fp + 6 ≤ h * L_in)
    (hm_Lin : 32 * (m0 + 1) * 2 ^ P_fp < 2 ^ (h * L_in - 1))
    (h2P_ltw : 2 * P_fp + 9 < 2 ^ w)
    (hrho_pos : 1 ≤ rho_nat) (hrho_cap : rho_nat < 2 ^ (h * (L_w - L_in)))
    (hnum_le : numPtr + L_w ≤ tmpHeap) (hden_le : denPtr + L_w ≤ tmpHeap)
    (hwt_le : wtPtr + L_in ≤ tmpHeap) (hone_le : onePtr + L_w ≤ tmpHeap)
    (hrho_le : rhoPtr + L_w ≤ tmpHeap)
    (hsp : tmpHeap + mwuEdgeStepSpace L_in L_w P_fp < 2 ^ w)
    (hz : ZeroFrom mem tmpHeap)
    (hv_num : Valid mem numPtr h L_w) (hv_den : Valid mem denPtr h L_w)
    (hv_wt : Valid mem wtPtr h L_in) (hv_one : Valid mem onePtr h L_w)
    (hv_rho : Valid mem rhoPtr h L_w)
    (hnum_pos : 0 < intVal mem numPtr h L_w) (hden_pos : 0 < intVal mem denPtr h L_w)
    (hwstr_eq : (intVal mem numPtr h L_w : ℝ) / (intVal mem denPtr h L_w : ℝ) = wstr)
    (hwstr_lo : 1 ≤ wstr) (hwstr_hi : wstr ≤ (rho_nat : ℝ) / 10)
    (hv_eq : fixVal mem wtPtr h L_in P_fp = v)
    (hv_lo : (1 / 2 : ℝ) ≤ v) (hv_hi : v ≤ 8 * (m0 : ℝ))
    (hone_eq : intVal mem onePtr h L_w = (2 : ℤ) ^ P_fp)
    (hrho_eq : intVal mem rhoPtr h L_w = (rho_nat : ℤ) * (2 : ℤ) ^ P_fp)
    (hDiv : MeetsContract w p bDiv (fixedDivideContract w h))
    (hExp : MeetsContract w p bExp (positiveExponentialContract w h q))
    (hMul : MeetsContract w p bMul (fixedMultiplyContract w h))
    (hCopy : MeetsContract w p bCopy (memCopyContract w))
    (hFill : MeetsContract w p bFill (memFillContract w)) :
    ∃ st' c,
      Runs w p ω (mwuEdgeStepProc bDiv bExp bMul bCopy bFill)
        (startState [numPtr, denPtr, wtPtr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos)
        (.returned 0) st' c ∧
      Valid st'.mem wtPtr h L_in ∧
      0 < fixVal st'.mem wtPtr h L_in P_fp ∧
      (1 - 1 / (4 * (k_nat : ℝ))) * v * Real.exp (wstr / (rho_nat : ℝ)) ≤
        fixVal st'.mem wtPtr h L_in P_fp ∧
      fixVal st'.mem wtPtr h L_in P_fp ≤
        (1 + 1 / (4 * (k_nat : ℝ))) * v * Real.exp (wstr / (rho_nat : ℝ)) ∧
      (∀ z < tmpHeap, z < wtPtr ∨ wtPtr + L_in ≤ z → st'.mem z = mem z) ∧
      ZeroFrom st'.mem tmpHeap ∧
      c ≤ mwuEdgeStepCost L_in L_w P_fp := by
  obtain ⟨hfit_Q, hfit_X, hX_nn, hX_le1, hE_step⟩ :=
    lemma55_step_error hh hLin_le hk hq_P hk_q hP_Lin hm_Lin hrho_pos hrho_cap
      hnum_pos hden_pos hwstr_eq hwstr_lo hwstr_hi hv_eq hv_lo hv_hi
  have h2w_16 : 16 ≤ 2 ^ w := by
    have : 2 ^ 5 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hLw_div : L_w ≤ fixedDivideSpace L_w := by
    dsimp [fixedDivideSpace]; omega
  have hLw_exp : L_w ≤ positiveExponentialSpace L_w P_fp 1 := by
    dsimp [positiveExponentialSpace]; omega
  have hLin_mul : L_in ≤ 11 * L_in + 1 := by omega
  have hsp_exp : mwuEdgeStepSpace L_in L_w P_fp =
      fixedDivideSpace L_w + fixedDivideSpace L_w +
        positiveExponentialSpace L_w P_fp 1 + (11 * L_in + 1) := by
    dsimp [mwuEdgeStepSpace]; omega
  suffices hmain : ∃ o st' c,
      Runs w p ω (mwuEdgeStepProc bDiv bExp bMul bCopy bFill)
        (startState [numPtr, denPtr, wtPtr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos)
        o st' c ∧
      (o = .returned 0 ∧
        Valid st'.mem wtPtr h L_in ∧
        0 < fixVal st'.mem wtPtr h L_in P_fp ∧
        (1 - 1 / (4 * (k_nat : ℝ))) * v * Real.exp (wstr / (rho_nat : ℝ)) ≤
          fixVal st'.mem wtPtr h L_in P_fp ∧
        fixVal st'.mem wtPtr h L_in P_fp ≤
          (1 + 1 / (4 * (k_nat : ℝ))) * v * Real.exp (wstr / (rho_nat : ℝ)) ∧
        (∀ z < tmpHeap, z < wtPtr ∨ wtPtr + L_in ≤ z → st'.mem z = mem z) ∧
        ZeroFrom st'.mem tmpHeap) ∧
      0 + c ≤ mwuEdgeStepCost L_in L_w P_fp by
    rcases hmain with ⟨_, st', c, hrun, ⟨rfl, h1, h2, h3, h4, h5, h6⟩, hc⟩
    exact ⟨st', c, hrun, h1, h2, h3, h4, h5, h6, by omega⟩
  have hr0 : (startState [numPtr, denPtr, wtPtr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos).regs 0 = numPtr := by simp [startState]
  have hr1 : (startState [numPtr, denPtr, wtPtr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos).regs 1 = denPtr := by simp [startState]
  have hr2 : (startState [numPtr, denPtr, wtPtr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos).regs 2 = wtPtr := by simp [startState]
  have hr3 : (startState [numPtr, denPtr, wtPtr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos).regs 3 = onePtr := by simp [startState]
  have hr4 : (startState [numPtr, denPtr, wtPtr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos).regs 4 = rhoPtr := by simp [startState]
  have hr5 : (startState [numPtr, denPtr, wtPtr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos).regs 5 = L_in := by simp [startState]
  have hr6 : (startState [numPtr, denPtr, wtPtr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos).regs 6 = L_w := by simp [startState]
  have hr7 : (startState [numPtr, denPtr, wtPtr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos).regs 7 = P_fp := by simp [startState]
  have hr8 : (startState [numPtr, denPtr, wtPtr, onePtr, rhoPtr, L_in, L_w, P_fp, tmpHeap] mem pos).regs 8 = tmpHeap := by simp [startState]
  dsimp only [mwuEdgeStepProc]
  -- 1. q_e := fixedDivide(numPtr, denPtr, L_w, P_fp, tmpHeap)
  refine runs_seq_call_le hDiv (vs := [numPtr, denPtr, L_w, P_fp, tmpHeap])
    (by simp [evalArgs, Expr.eval, hr0, hr1, hr6, hr7, hr8])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨⟨numPtr, denPtr, L_w, P_fp, tmpHeap, rfl, hdiv, hnum_le, hden_le, hv_num, hv_den,
      ne_of_gt hden_pos, hfit_Q⟩, hz, by change tmpHeap + fixedDivideSpace L_w < 2 ^ w; omega⟩ ?_
  intro hp1 mem1 _ hpost1
  rcases hpost1 with ⟨hhp1, _, _, hfr1, hz1, hv_q, hint_q⟩
  change hp1 = tmpHeap + fixedDivideSpace L_w at hhp1
  change ∀ z < tmpHeap, mem1 z = mem z at hfr1
  change ZeroFrom mem1 hp1 at hz1
  have hq_ptr : tmpHeap + 9 * L_w + integerDivideSpace (3 * L_w) = hp1 - L_w := by
    rw [hhp1]; dsimp [fixedDivideSpace]; omega
  change Valid mem1 (tmpHeap + 9 * L_w + integerDivideSpace (3 * L_w)) h L_w at hv_q
  change intVal mem1 (tmpHeap + 9 * L_w + integerDivideSpace (3 * L_w)) h L_w =
      floorDiv (intVal mem numPtr h L_w * (2 : ℤ) ^ P_fp) (intVal mem denPtr h L_w) at hint_q
  rw [hq_ptr] at hv_q hint_q
  have hv_rho1 : Valid mem1 rhoPtr h L_w := fun i hi => by rw [hfr1 _ (by omega)]; exact hv_rho i hi
  have hrho_eq1 : intVal mem1 rhoPtr h L_w = (rho_nat : ℤ) * (2 : ℤ) ^ P_fp :=
    (intVal_congr fun i hi => hfr1 _ (by omega)).trans hrho_eq
  have hrho_ne1 : intVal mem1 rhoPtr h L_w ≠ 0 := by rw [hrho_eq1]; positivity
  -- 2. x_e := fixedDivide(hp1 - L_w, rhoPtr, L_w, P_fp, hp1)
  refine runs_seq_call_le hDiv (vs := [hp1 - L_w, rhoPtr, L_w, P_fp, hp1])
    (by simp [evalArgs, Expr.eval, BinOp.eval, hr4, hr6, hr7, show hp1 - L_w < 2 ^ w by omega])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨⟨hp1 - L_w, rhoPtr, L_w, P_fp, hp1, rfl, hdiv, by omega, by omega, hv_q, hv_rho1, hrho_ne1,
      by rw [hint_q, hrho_eq1]; exact hfit_X⟩, hz1,
      by change hp1 + fixedDivideSpace L_w < 2 ^ w; omega⟩ ?_
  intro hp2 mem2 _ hpost2
  rcases hpost2 with ⟨hhp2, _, _, hfr2, hz2, hv_x, hint_x⟩
  change hp2 = hp1 + fixedDivideSpace L_w at hhp2
  change ∀ z < hp1, mem2 z = mem1 z at hfr2
  change ZeroFrom mem2 hp2 at hz2
  have hx_ptr : hp1 + 9 * L_w + integerDivideSpace (3 * L_w) = hp2 - L_w := by
    rw [hhp2]; dsimp [fixedDivideSpace]; omega
  change Valid mem2 (hp1 + 9 * L_w + integerDivideSpace (3 * L_w)) h L_w at hv_x
  change intVal mem2 (hp1 + 9 * L_w + integerDivideSpace (3 * L_w)) h L_w =
      floorDiv (intVal mem1 (hp1 - L_w) h L_w * (2 : ℤ) ^ P_fp) (intVal mem1 rhoPtr h L_w) at hint_x
  rw [hx_ptr] at hv_x hint_x
  rw [hint_q, hrho_eq1] at hint_x
  have hfr2_0 : ∀ z < tmpHeap, mem2 z = mem z := fun z hz' => (hfr2 z (by omega)).trans (hfr1 z hz')
  have hv_one2 : Valid mem2 onePtr h L_w := fun i hi => by rw [hfr2_0 _ (by omega)]; exact hv_one i hi
  have hone_eq2 : intVal mem2 onePtr h L_w = (2 : ℤ) ^ P_fp :=
    (intVal_congr fun i hi => hfr2_0 _ (by omega)).trans hone_eq
  -- 3. e_e := positiveExponential(hp2 - L_w, onePtr, L_w, P_fp, 1, hp2)
  refine runs_seq_call_le hExp (vs := [hp2 - L_w, onePtr, L_w, P_fp, 1, hp2])
    (by simp [evalArgs, Expr.eval, BinOp.eval, hr3, hr6, hr7, show 1 < 2 ^ w by omega,
        show hp2 - L_w < 2 ^ w by omega])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨⟨hp2 - L_w, onePtr, L_w, P_fp, 1, hp2, rfl, hdiv, by omega,
      by have : h * L_in ≤ h * L_w := Nat.mul_le_mul_left h hLin_le; omega,
      h2P_ltw, by omega, by omega, hv_x, hv_one2, hone_eq2,
      by rw [hint_x]; exact hX_nn,
      by unfold fixVal; rw [hint_x]; simpa using hX_le1⟩, hz2,
      by change hp2 + positiveExponentialSpace L_w P_fp 1 < 2 ^ w; omega⟩ ?_
  intro hp3 mem3 _ hpost3
  rcases hpost3 with ⟨hhp3, _, _, hfr3, hz3, hv_e_w, hE1, hE_le, hE_err⟩
  change hp3 = hp2 + positiveExponentialSpace L_w P_fp 1 at hhp3
  change ∀ z < hp2, mem3 z = mem2 z at hfr3
  change ZeroFrom mem3 hp3 at hz3
  have he_ptr : hp2 + positiveExponentialSpace L_w P_fp 1 - L_w = hp3 - L_w := by rw [hhp3]
  change Valid mem3 (hp2 + positiveExponentialSpace L_w P_fp 1 - L_w) h L_w at hv_e_w
  change 1 ≤ fixVal mem3 (hp2 + positiveExponentialSpace L_w P_fp 1 - L_w) h L_w P_fp at hE1
  change fixVal mem3 (hp2 + positiveExponentialSpace L_w P_fp 1 - L_w) h L_w P_fp ≤
      Real.exp (fixVal mem2 (hp2 - L_w) h L_w P_fp) at hE_le
  change |fixVal mem3 (hp2 + positiveExponentialSpace L_w P_fp 1 - L_w) h L_w P_fp -
      Real.exp (fixVal mem2 (hp2 - L_w) h L_w P_fp)| ≤
      (1 / (2 : ℝ) ^ q) * Real.exp (fixVal mem2 (hp2 - L_w) h L_w P_fp) at hE_err
  rw [he_ptr] at hv_e_w hE1 hE_le hE_err
  have hx_eq_real : fixVal mem2 (hp2 - L_w) h L_w P_fp =
      ((floorDiv (floorDiv (intVal mem numPtr h L_w * (2 : ℤ) ^ P_fp) (intVal mem denPtr h L_w) *
        (2 : ℤ) ^ P_fp) ((rho_nat : ℤ) * (2 : ℤ) ^ P_fp) : ℤ) : ℝ) / (2 : ℝ) ^ P_fp := by
    unfold fixVal; rw [hint_x]
  rw [hx_eq_real] at hE_le hE_err
  obtain ⟨hE_nn, hE_fit_in, hwrap, hv'_pos, hv'_lb, hv'_ub⟩ :=
    hE_step (intVal mem3 (hp3 - L_w) h L_w) hE1 hE_le hE_err
  obtain ⟨hv_e_in, hint_e_in⟩ := lemma55_trunc_pos hv_e_w hLin_le hE_nn hE_fit_in
  have hfr3_0 : ∀ z < tmpHeap, mem3 z = mem z := fun z hz' => (hfr3 z (by omega)).trans (hfr2_0 z hz')
  have hv_wt3 : Valid mem3 wtPtr h L_in := fun i hi => by rw [hfr3_0 _ (by omega)]; exact hv_wt i hi
  have hwt_eq3 : intVal mem3 wtPtr h L_in = intVal mem wtPtr h L_in :=
    intVal_congr fun i hi => hfr3_0 _ (by omega)
  -- 4. prod := fixedMultiply(wtPtr, hp3 - L_w, L_in, P_fp, hp3)
  refine runs_seq_call_le hMul (vs := [wtPtr, hp3 - L_w, L_in, P_fp, hp3])
    (by simp [evalArgs, Expr.eval, BinOp.eval, hr2, hr5, hr6, hr7, show hp3 - L_w < 2 ^ w by omega])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨⟨wtPtr, hp3 - L_w, L_in, P_fp, hp3, rfl, hdiv, by omega, by omega, hv_wt3, hv_e_in⟩, hz3,
      by change hp3 + (11 * L_in + 1) < 2 ^ w; omega⟩ ?_
  intro hp4 mem4 _ hpost4
  rcases hpost4 with ⟨hhp4, _, _, hfr4, hz4, hv_prod, hint_prod⟩
  change hp4 = hp3 + (11 * L_in + 1) at hhp4
  change ∀ z < hp3, mem4 z = mem3 z at hfr4
  change ZeroFrom mem4 hp4 at hz4
  have hprod_ptr : hp3 + 10 * L_in + 1 = hp4 - L_in := by omega
  change Valid mem4 (hp3 + 10 * L_in + 1) h L_in at hv_prod
  change intVal mem4 (hp3 + 10 * L_in + 1) h L_in =
      wrap h L_in ((intVal mem3 wtPtr h L_in * intVal mem3 (hp3 - L_w) h L_in) / (2 : ℤ) ^ P_fp) at hint_prod
  rw [hprod_ptr] at hv_prod hint_prod
  rw [hwt_eq3, hint_e_in] at hint_prod
  -- 5. Copy prod (L_in limbs) into wtPtr
  refine runs_seq_call_le hCopy (vs := [wtPtr, hp4 - L_in, L_in])
    (by simp [evalArgs, Expr.eval, BinOp.eval, hr2, hr5, show hp4 - L_in < 2 ^ w by omega])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> omega)
    ⟨wtPtr, hp4 - L_in, L_in, rfl, by omega, by omega, Or.inl (by omega)⟩ ?_
  intro _ mem5 _ hpost5
  rcases hpost5 with ⟨_, _, _, hEq5, _, hcp5, hfr5⟩
  simp only [List.cons.injEq, and_true] at hEq5; rcases hEq5 with ⟨rfl, rfl, rfl⟩
  -- 6. Zero [tmpHeap, hp4) back to 0
  refine runs_seq_call_le hFill (vs := [tmpHeap, hp4 - tmpHeap, 0])
    (by simp [evalArgs, Expr.eval, BinOp.eval, hr8, show 0 < 2 ^ w by omega,
        show hp4 - tmpHeap < 2 ^ w by omega])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> omega)
    ⟨tmpHeap, hp4 - tmpHeap, 0, rfl, by omega⟩ ?_
  intro _ mem6 _ hpost6
  rcases hpost6 with ⟨_, _, _, hEq6, _, hfill6, hfr6⟩
  simp only [List.cons.injEq, and_true] at hEq6; rcases hEq6 with ⟨rfl, rfl, rfl⟩
  have hwt_mem6 : ∀ i < L_in, mem6 (wtPtr + i) = mem4 (hp4 - L_in + i) := fun i hi =>
    (hfr6 _ (Or.inl (by omega))).trans (hcp5 i hi)
  have hv_wt6 : Valid mem6 wtPtr h L_in := fun i hi => by rw [hwt_mem6 i hi]; exact hv_prod i hi
  have hfix_wt6 : fixVal mem6 wtPtr h L_in P_fp =
      (wrap h L_in ((intVal mem wtPtr h L_in * intVal mem3 (hp3 - L_w) h L_w) / (2 : ℤ) ^ P_fp) : ℝ) /
        (2 : ℝ) ^ P_fp := by
    unfold fixVal
    rw [intVal_congr hwt_mem6, hint_prod]
  have hfr_out : ∀ z < tmpHeap, z < wtPtr ∨ wtPtr + L_in ≤ z → mem6 z = mem z := fun z hzt hzw =>
    (hfr6 z (Or.inl hzt)).trans ((hfr5 z hzw).trans ((hfr4 z (by omega)).trans (hfr3_0 z hzt)))
  dsimp only at hfr5 hfr6
  have hz_out : ZeroFrom mem6 tmpHeap := by
    intro z hz'
    by_cases hlt : z < hp4
    · have := hfill6 (z - tmpHeap) (by omega)
      rwa [show tmpHeap + (z - tmpHeap) = z by omega] at this
    · rw [hfr6 z (Or.inr (by omega)), hfr5 z (Or.inr (by omega))]
      exact hz4 z (by omega)
  refine runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega])
    ⟨rfl, hv_wt6, hfix_wt6 ▸ hv'_pos, hfix_wt6 ▸ hv'_lb, hfix_wt6 ▸ hv'_ub, hfr_out, hz_out⟩ ?_
  dsimp only [fixedDivideContract, positiveExponentialContract, fixedMultiplyContract,
    memCopyContract, memFillContract, heapContract, mwuEdgeStepCost, argsSize, Expr.size]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  have hdiff : hp4 - tmpHeap = mwuEdgeStepSpace L_in L_w P_fp := by omega
  rw [hdiff]
  clear * -
  omega

end

end MinCostFlow.LSF.Program
