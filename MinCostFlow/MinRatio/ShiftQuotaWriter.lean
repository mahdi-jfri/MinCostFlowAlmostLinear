module

public import MinCostFlow.MinRatio.OrdChainRefreshWiredBase
import WordRAM.Tactic

/-!
# Shift quota writer procedure (`ShiftQuotaWriterSpec`)

Implements the deterministic Word-RAM procedure `shiftQuotaWriterBody threshold` that computes
the integer shift quotas `shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i`
for every level `i ≤ cfg.P.d` and the pass limit `⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊`, and proves
`shiftQuotaWriterSpec_proved` discharging `ShiftQuotaWriterSpec`.

Since `alg2PsiGame Ψ M₀ = 2 * ⌈Ψ⌉₊ + Nat.clog 2 (M₀ + 1) + 1` is an exact natural number, the
base `B = 10 * alg2PsiGameNat ⌈Ψ⌉₊ M₀ * k` is an exact natural number and `gameShiftBound` is the
integer polynomial

  `B^(i+1) + ∑_{j ≤ i} rebuildCount j * B^(i + 1 - j)`.

Evaluating it via Horner's recurrence `acc₀ = 1`, `acc_{i+1} = (acc_i + rebuildCount i) * B`
computes all `d + 1` quotas in a single loop of length `d + 1` with zero heap allocation and no
external procedure calls (computing `Nat.clog 2 (M₀ + 1)` with an inline halving loop). Every
intermediate value is bounded by the final quota at level `d`, so the word-fit hypothesis of
`ShiftQuotaWriterSpec` covers all arithmetic.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain SparseCore.Program

/-! ## Exact natural-number arithmetic for `alg2PsiGame` and `gameShiftBound` -/

/-- Exact natural-number value of `alg2PsiGame Ψ M₀` when `psi = ⌈Ψ⌉₊`. -/
@[expose] def alg2PsiGameNat (psi M₀ : ℕ) : ℕ :=
  2 * psi + Nat.clog 2 (M₀ + 1) + 1

/-- Exact natural-number base `10 * Ψ_game * k` of Lemma 7.3's powers. -/
@[expose] def shiftQuotaBase (psi M₀ k : ℕ) : ℕ :=
  10 * alg2PsiGameNat psi M₀ * k

/-- Exact natural-number value of `gameShiftBound` for an integral base `B`. -/
@[expose] def gameShiftBoundNat (B : ℕ) (reb : ℕ → ℕ) (i : ℕ) : ℕ :=
  B ^ (i + 1) + ∑ j ∈ Finset.range (i + 1), reb j * B ^ (i + 1 - j)

/-- Horner accumulator for `gameShiftBoundNat`: `hornerQuota B reb (i + 1) = gameShiftBoundNat B reb i`. -/
@[expose] def hornerQuota (B : ℕ) (reb : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => (hornerQuota B reb j + reb j) * B

theorem alg2PsiGame_eq_natCast (Ψ : ℝ) (M₀ : ℕ) :
    alg2PsiGame Ψ M₀ = (alg2PsiGameNat ⌈Ψ⌉₊ M₀ : ℝ) := rfl

theorem ceil_two_mul_alg2PsiGame (Ψ : ℝ) (M₀ : ℕ) :
    ⌈2 * alg2PsiGame Ψ M₀⌉₊ = 2 * alg2PsiGameNat ⌈Ψ⌉₊ M₀ := by
  rw [alg2PsiGame_eq_natCast, show (2 : ℝ) * (alg2PsiGameNat ⌈Ψ⌉₊ M₀ : ℝ) =
    ((2 * alg2PsiGameNat ⌈Ψ⌉₊ M₀ : ℕ) : ℝ) by push_cast; ring, Nat.ceil_natCast]

theorem gameShiftBound_eq_natCast (P : ChainParams) (Ψ : ℝ) (reb : ℕ → ℕ) (i : ℕ) :
    gameShiftBound P (alg2PsiGame Ψ P.M₀) reb i =
      (gameShiftBoundNat (shiftQuotaBase ⌈Ψ⌉₊ P.M₀ P.k) reb i : ℝ) := by
  unfold gameShiftBound gameShiftBoundNat shiftQuotaBase
  rw [alg2PsiGame_eq_natCast]
  push_cast
  rfl

theorem shiftQuotaWord_eq_gameShiftBoundNat (P : ChainParams) (Ψ : ℝ) (reb : ℕ → ℕ) (i : ℕ) :
    shiftQuotaWord P (alg2PsiGame Ψ P.M₀) reb i =
      gameShiftBoundNat (shiftQuotaBase ⌈Ψ⌉₊ P.M₀ P.k) reb i := by
  have hpsi : 0 ≤ alg2PsiGame Ψ P.M₀ :=
    le_trans zero_le_one (alg2PsiGame_ge_one Ψ P.M₀)
  have hiff : ∀ c, c < shiftQuotaWord P (alg2PsiGame Ψ P.M₀) reb i ↔
      c < gameShiftBoundNat (shiftQuotaBase ⌈Ψ⌉₊ P.M₀ P.k) reb i := by
    intro c
    rw [shiftQuotaWord_lt_iff P (alg2PsiGame Ψ P.M₀) reb i c hpsi, gameShiftBound_eq_natCast]
    have hcast : ((c : ℝ) + 1 ≤ (gameShiftBoundNat (shiftQuotaBase ⌈Ψ⌉₊ P.M₀ P.k) reb i : ℝ)) ↔
        c + 1 ≤ gameShiftBoundNat (shiftQuotaBase ⌈Ψ⌉₊ P.M₀ P.k) reb i := by
      exact_mod_cast Iff.rfl
    rw [hcast]
    omega
  apply le_antisymm
  · by_contra hgt
    have hlt : gameShiftBoundNat (shiftQuotaBase ⌈Ψ⌉₊ P.M₀ P.k) reb i <
        shiftQuotaWord P (alg2PsiGame Ψ P.M₀) reb i := Nat.lt_of_not_ge hgt
    exact Nat.lt_irrefl _ ((hiff _).mp hlt)
  · by_contra hgt
    have hlt : shiftQuotaWord P (alg2PsiGame Ψ P.M₀) reb i <
        gameShiftBoundNat (shiftQuotaBase ⌈Ψ⌉₊ P.M₀ P.k) reb i := Nat.lt_of_not_ge hgt
    exact Nat.lt_irrefl _ ((hiff _).mpr hlt)

theorem hornerQuota_succ_eq (B : ℕ) (reb : ℕ → ℕ) (i : ℕ) :
    hornerQuota B reb (i + 1) = gameShiftBoundNat B reb i := by
  induction i with
  | zero =>
    simp [hornerQuota, gameShiftBoundNat, Nat.add_mul]
  | succ i ih =>
    rw [hornerQuota, ih]
    dsimp only [gameShiftBoundNat]
    rw [Nat.add_mul, Nat.add_mul, ← pow_succ, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_range_succ, show i + 1 + 1 - (i + 1) = 1 by omega, pow_one]
    have hsum : ∑ x ∈ Finset.range (i + 1), reb x * B ^ (i + 1 - x) * B =
        ∑ x ∈ Finset.range (i + 1), reb x * B ^ (i + 1 + 1 - x) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' : x < i + 1 := Finset.mem_range.mp hx
      rw [mul_assoc, ← pow_succ, show i + 1 - x + 1 = i + 1 + 1 - x by omega]
    rw [hsum, Nat.add_assoc]

theorem shiftQuotaBase_ge_ten (psi M₀ : ℕ) {k : ℕ} (hk : 0 < k) :
    10 ≤ shiftQuotaBase psi M₀ k := by
  unfold shiftQuotaBase alg2PsiGameNat
  have h1 : 1 ≤ 2 * psi + Nat.clog 2 (M₀ + 1) + 1 := by omega
  have h2 : 10 * 1 * 1 ≤ 10 * (2 * psi + Nat.clog 2 (M₀ + 1) + 1) * k :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 10 h1) hk
  omega

theorem hornerQuota_mono {B : ℕ} (hB : 1 ≤ B) (reb : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j) :
    hornerQuota B reb i ≤ hornerQuota B reb j := by
  induction hij with
  | refl => exact le_rfl
  | @step m _ ih =>
    refine ih.trans ?_
    simp only [hornerQuota]
    calc hornerQuota B reb m
        ≤ hornerQuota B reb m + reb m := Nat.le_add_right _ _
      _ ≤ (hornerQuota B reb m + reb m) * B := Nat.le_mul_of_pos_right _ hB

theorem hornerQuota_add_reb_le {B : ℕ} (hB : 1 ≤ B) (reb : ℕ → ℕ) {i d : ℕ} (hid : i ≤ d) :
    hornerQuota B reb i + reb i ≤ gameShiftBoundNat B reb d := by
  rw [← hornerQuota_succ_eq]
  calc hornerQuota B reb i + reb i
      ≤ (hornerQuota B reb i + reb i) * B := Nat.le_mul_of_pos_right _ hB
    _ = hornerQuota B reb (i + 1) := rfl
    _ ≤ hornerQuota B reb (d + 1) := hornerQuota_mono hB reb (Nat.succ_le_succ hid)

theorem gameShiftBoundNat_ge_basePow (B : ℕ) (reb : ℕ → ℕ) (i : ℕ) :
    B ^ (i + 1) ≤ gameShiftBoundNat B reb i :=
  Nat.le_add_right _ _

theorem two_mul_succ_le_ten_pow_succ (d : ℕ) : 2 * (d + 1) ≤ 10 ^ (d + 1) := by
  induction d with
  | zero => decide
  | succ d ih =>
    rw [pow_succ]
    omega

theorem hundred_mul_M0_le_basePow (P : ChainParams) (psi : ℕ) :
    100 * P.M₀ ≤ shiftQuotaBase psi P.M₀ P.k ^ (P.d + 1) := by
  have h10k : 10 * P.k ≤ shiftQuotaBase psi P.M₀ P.k := by
    unfold shiftQuotaBase alg2PsiGameNat
    have h1 : 1 ≤ 2 * psi + Nat.clog 2 (P.M₀ + 1) + 1 := by omega
    calc 10 * P.k = 10 * 1 * P.k := by ring
      _ ≤ 10 * (2 * psi + Nat.clog 2 (P.M₀ + 1) + 1) * P.k :=
          Nat.mul_le_mul_right P.k (Nat.mul_le_mul_left 10 h1)
  have h100 : 100 ≤ 10 ^ (P.d + 1) :=
    calc 100 = 10 ^ 2 := by decide
      _ ≤ 10 ^ (P.d + 1) := Nat.pow_le_pow_right (by decide) (by have := P.hd; omega)
  have hkPow : P.M₀ ≤ P.k ^ (P.d + 1) :=
    P.hk_pow.trans (Nat.pow_le_pow_right P.hk (Nat.le_succ _))
  calc 100 * P.M₀ ≤ 10 ^ (P.d + 1) * P.k ^ (P.d + 1) := Nat.mul_le_mul h100 hkPow
    _ = (10 * P.k) ^ (P.d + 1) := (Nat.mul_pow 10 P.k (P.d + 1)).symm
    _ ≤ shiftQuotaBase psi P.M₀ P.k ^ (P.d + 1) := Nat.pow_le_pow_left h10k _

/-! ## Word-RAM procedure `shiftQuotaWriterBody` -/

/-- Inline halving loop computing `Nat.clog 2 x`: given `reg 8 = x ≥ 1` and `reg 9 = 0`, ends with
`reg 9 = Nat.clog 2 x` without touching memory or any other register. -/
@[expose] def clog2Loop : Stmt :=
  .loop (.bin .lt (.const 1) (.reg 8))
    (.assign 8 (.bin .div (.bin .add (.reg 8) (.const 1)) (.const 2)) ;;
     .assign 9 (.bin .add (.reg 9) (.const 1)))

theorem clog2Loop_noRand : clog2Loop.NoRand := by
  simp [clog2Loop, Stmt.NoRand]

/-- Inline Horner loop writing `gameShiftBoundNat B reb i` to `quotaBase + i` for `i = 0..d`.
Reads `quotaBase` (`reg 1`), `B` (`reg 11`), `d + 1` (`reg 13`), `rebBase` (`reg 14`), and
accumulator `acc` (`reg 15`, initially `1`), using `reg 12` as loop counter. -/
@[expose] def hornerQuotaLoop : Stmt :=
  forRange 12 (.const 0) (.reg 13)
    (.assign 15 (.bin .mul (.bin .add (.reg 15) (.load (.bin .add (.reg 14) (.reg 12)))) (.reg 11)) ;;
     .store (.bin .add (.reg 1) (.reg 12)) (.reg 15))

theorem hornerQuotaLoop_noRand : hornerQuotaLoop.NoRand := by
  simp [hornerQuotaLoop, forRange, forUp, Stmt.NoRand]

/-- Deterministic Word-RAM shift-quota writer taking `[root, quotaBase]` (`reg 0`, `reg 1`) and
fixed witness threshold `threshold`. Reads `(m, d, k, psi)` from `ChainInitParametersAt` and
`rebuildCount[0..d]` from `SolverScheduleAt`, computes `M₀ = max m threshold`,
`ψ_g = 2 * psi + Nat.clog 2 (M₀ + 1) + 1`, `B = 10 * ψ_g * k`, writes `2 * ψ_g` at
`quotaBase + (d + 1)` and `shiftQuotaWord ... i` at `quotaBase + i` for `i ≤ d`, and returns `0`. -/
@[expose] def shiftQuotaWriterBody (threshold : ℕ) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 2))) ;;
  .assign 4 (.load (.bin .add (.reg 2) (.const 11))) ;;
  .assign 5 (.load (.bin .add (.reg 2) (.const 12))) ;;
  .assign 6 (.load (.bin .add (.reg 2) (.const 13))) ;;
  .assign 7 (.load (.bin .add (.reg 2) (.const 9))) ;;
  .cond (.bin .lt (.reg 7) (.const threshold)) (.assign 7 (.const threshold)) .nop ;;
  .assign 8 (.bin .add (.reg 7) (.const 1)) ;;
  .assign 9 (.const 0) ;;
  clog2Loop ;;
  .assign 10 (.bin .add (.bin .add (.bin .mul (.const 2) (.reg 6)) (.reg 9)) (.const 1)) ;;
  .assign 11 (.bin .mul (.bin .mul (.const 10) (.reg 10)) (.reg 5)) ;;
  .assign 13 (.bin .add (.reg 4) (.const 1)) ;;
  .store (.bin .add (.reg 1) (.reg 13)) (.bin .mul (.const 2) (.reg 10)) ;;
  .assign 14 (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 13))) ;;
  .assign 15 (.const 1) ;;
  hornerQuotaLoop ;;
  .ret (.const 0)

theorem shiftQuotaWriterBody_noRand (threshold : ℕ) :
    (shiftQuotaWriterBody threshold).NoRand := by
  simp [shiftQuotaWriterBody, clog2Loop_noRand, hornerQuotaLoop_noRand, Stmt.NoRand]

/-- Step budget of `shiftQuotaWriterBody` in terms of `d` and `M₀`: `O(d + log M₀)`. -/
@[expose] def shiftQuotaWriterBudget (d M₀ : ℕ) : ℕ :=
  30 * (d + 1) + 25 * Nat.clog 2 (M₀ + 1) + 140

/-! ## Verification of the two loops and the full procedure -/

private theorem clog2_step_eq {x : ℕ} (hx : 1 < x) :
    Nat.clog 2 x = Nat.clog 2 ((x + 1) / 2) + 1 := by
  have h := Nat.clog_of_one_lt (by decide : 1 < 2) hx
  have heq : x + 2 - 1 = x + 1 := by omega
  simpa only [heq] using h

theorem clog2Loop_runs {w x₀ : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hx0 : 1 ≤ x₀) (hr8 : st.regs 8 = x₀) (hr9 : st.regs 9 = 0)
    (hxW : x₀ + 1 < 2 ^ w) (hw2 : 2 < 2 ^ w) :
    ∃ out cost,
      Runs w p ω clog2Loop st .normal out cost ∧
      cost ≤ 15 * Nat.clog 2 x₀ + 4 ∧
      out.regs 9 = Nat.clog 2 x₀ ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 8 → r ≠ 9 → out.regs r = st.regs r) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hclogLe : Nat.clog 2 x₀ ≤ x₀ := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  let Inv (s : State) : Prop :=
    1 ≤ s.regs 8 ∧ s.regs 8 ≤ x₀ ∧ s.regs 9 + Nat.clog 2 (s.regs 8) = Nat.clog 2 x₀ ∧
    s.mem = st.mem ∧ ∀ r, r ≠ 8 → r ≠ 9 → s.regs r = st.regs r
  let Q (s : State) : Prop :=
    s.regs 9 = Nat.clog 2 x₀ ∧ s.mem = st.mem ∧ ∀ r, r ≠ 8 → r ≠ 9 → s.regs r = st.regs r
  have hloop := Triple.loop_const_normal (w := w) (p := p)
    (e := .bin .lt (.const 1) (.reg 8))
    (body := .assign 8 (.bin .div (.bin .add (.reg 8) (.const 1)) (.const 2)) ;;
             .assign 9 (.bin .add (.reg 9) (.const 1)))
    (Inv := Inv) (Q := Q) (m := fun s => Nat.clog 2 (s.regs 8))
    (condVal := fun s => if 1 < s.regs 8 then 1 else 0) 11
    (fun s _ => by
      by_cases hlt : 1 < s.regs 8
      · simp [Expr.eval, BinOp.eval, hw1, hlt]
      · simp [Expr.eval, BinOp.eval, hw1, hlt, show 0 < 2 ^ w by omega])
    (fun s hI hv => by
      have hle : s.regs 8 ≤ 1 := by
        by_contra hgt
        have : 1 < s.regs 8 := by omega
        simp [this] at hv
      have hcz : Nat.clog 2 (s.regs 8) = 0 := Nat.clog_of_right_le_one hle 2
      have h9 : s.regs 9 = Nat.clog 2 x₀ := by have := hI.2.2.1; omega
      exact ⟨h9, hI.2.2.2.1, hI.2.2.2.2⟩)
    (fun s hI hv => by
      intro s0 bits hs0
      subst s0
      have hlt : 1 < s.regs 8 := by
        by_contra hng; simp [hng] at hv
      have hx1W : s.regs 8 + 1 < 2 ^ w := by have := hI.2.1; omega
      have hhalfW : (s.regs 8 + 1) / 2 < 2 ^ w := by omega
      have hcStep := clog2_step_eq hlt
      have hr9NextW : s.regs 9 + 1 < 2 ^ w := by have := hI.2.2.1; omega
      let s1 : State := { s with regs := Function.update s.regs 8 ((s.regs 8 + 1) / 2) }
      let s2 : State := { s1 with regs := Function.update s1.regs 9 (s.regs 9 + 1) }
      have r1 : Runs w p bits
          (.assign 8 (.bin .div (.bin .add (.reg 8) (.const 1)) (.const 2))) s .normal s1 6 :=
        runs_assign_iff.mpr ⟨(s.regs 8 + 1) / 2, by
          simp [Expr.eval, BinOp.eval, hw1, hw2, hx1W, hhalfW], rfl, rfl, rfl⟩
      have r2 : Runs w p bits (.assign 9 (.bin .add (.reg 9) (.const 1))) s1 .normal s2 4 :=
        runs_assign_iff.mpr ⟨s.regs 9 + 1, by
          simp [Expr.eval, BinOp.eval, s1, hw1, hr9NextW], rfl, rfl, rfl⟩
      refine ⟨.normal, s2, 11, runs_seq_iff.mpr (Or.inr ⟨s1, 6, 4, r1, r2, rfl⟩), ?_, le_rfl⟩
      refine ⟨⟨by simp [s2, s1]; omega, by simp [s2, s1]; have := hI.2.1; omega,
        by simp only [s2, s1, Function.update_self, Function.update_of_ne (by decide : (8 : ℕ) ≠ 9)];
           have := hI.2.2.1; omega,
        hI.2.2.2.1,
        fun r h8 h9 => by
          simpa [s2, s1, Function.update_of_ne h8, Function.update_of_ne h9] using hI.2.2.2.2 r h8 h9⟩,
        by simp only [s2, s1, Function.update_of_ne (by decide : (8 : ℕ) ≠ 9), Function.update_self]; omega⟩)
  obtain ⟨o, out, cost, hr, hQ, hc⟩ := hloop.runs ω
    ⟨by omega, by omega, by simp [hr8, hr9], rfl, fun _ _ _ => rfl⟩
  cases o with
  | returned _ => exact False.elim hQ
  | normal =>
    refine ⟨out, cost, hr, ?_, hQ.1, hQ.2.1, hQ.2.2⟩
    simp only [Expr.size, hr8] at hc
    omega

theorem hornerQuotaLoop_runs {w quotaBase rebBase d B : ℕ} {reb : ℕ → ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hB : 1 ≤ B) (hr1 : st.regs 1 = quotaBase) (hr11 : st.regs 11 = B)
    (hr13 : st.regs 13 = d + 1) (hr14 : st.regs 14 = rebBase) (hr15 : st.regs 15 = 1)
    (hreb : ∀ i ≤ d, st.mem (rebBase + i) = reb i)
    (hdisj : ∀ i ≤ d, ∀ j ≤ d, rebBase + i ≠ quotaBase + j)
    (hrebW : ∀ i ≤ d, rebBase + i < 2 ^ w)
    (hqW : quotaBase + d + 1 < 2 ^ w)
    (hdW : d + 1 < 2 ^ w)
    (hvalW : gameShiftBoundNat B reb d < 2 ^ w)
    (hw1 : 1 < 2 ^ w) :
    ∃ out cost,
      Runs w p ω hornerQuotaLoop st .normal out cost ∧
      cost ≤ 27 * (d + 1) + 10 ∧
      (∀ i ≤ d, out.mem (quotaBase + i) = gameShiftBoundNat B reb i) ∧
      (∀ a, a < quotaBase ∨ quotaBase + d < a → out.mem a = st.mem a) := by
  let Inv (j : ℕ) (s : State) : Prop :=
    j ≤ d + 1 ∧ s.regs 12 = j ∧ s.regs 15 = hornerQuota B reb j ∧
    (∀ r, r ≠ 12 → r ≠ 15 → s.regs r = st.regs r) ∧
    (∀ k < j, s.mem (quotaBase + k) = gameShiftBoundNat B reb k) ∧
    (∀ a, a < quotaBase ∨ quotaBase + j ≤ a → s.mem a = st.mem a)
  let body : Stmt :=
    .assign 15 (.bin .mul (.bin .add (.reg 15) (.load (.bin .add (.reg 14) (.reg 12)))) (.reg 11)) ;;
    .store (.bin .add (.reg 1) (.reg 12)) (.reg 15)
  have hstep : ∀ j, 0 ≤ j → j < d + 1 →
      Triple w p (Inv j) body
        (normalPost fun s' => Inv (j + 1) { s' with regs := Function.update s'.regs 12 (j + 1) } ∧
          s'.regs 12 = j) (fun _ => 17) := by
    intro j _ hj s bits ⟨_, h12, h15, hregs, hprev, hfr⟩
    have hjLe : j ≤ d := by omega
    have h1 : s.regs 1 = quotaBase := (hregs 1 (by decide) (by decide)).trans hr1
    have h11 : s.regs 11 = B := (hregs 11 (by decide) (by decide)).trans hr11
    have h14 : s.regs 14 = rebBase := (hregs 14 (by decide) (by decide)).trans hr14
    have hrebEq : s.mem (rebBase + j) = reb j := by
      have hnotIn : rebBase + j < quotaBase ∨ quotaBase + j ≤ rebBase + j := by
        by_contra hIn; push Not at hIn
        have hlt : rebBase + j - quotaBase < j := by omega
        exact hdisj j hjLe (rebBase + j - quotaBase) (by omega) (by omega)
      exact (hfr (rebBase + j) hnotIn).trans (hreb j hjLe)
    have haddW : hornerQuota B reb j + reb j < 2 ^ w :=
      lt_of_le_of_lt (hornerQuota_add_reb_le hB reb hjLe) hvalW
    have hmulW : (hornerQuota B reb j + reb j) * B < 2 ^ w := by
      have hle : (hornerQuota B reb j + reb j) * B ≤ gameShiftBoundNat B reb d := by
        rw [← hornerQuota_succ_eq]
        exact hornerQuota_mono hB reb (Nat.succ_le_succ hjLe)
      exact lt_of_le_of_lt hle hvalW
    let nextVal := (hornerQuota B reb j + reb j) * B
    let s1 : State := { s with regs := Function.update s.regs 15 nextVal }
    let s2 : State := { s1 with mem := Function.update s1.mem (quotaBase + j) nextVal }
    have r1 : Runs w p bits
        (.assign 15 (.bin .mul (.bin .add (.reg 15) (.load (.bin .add (.reg 14) (.reg 12)))) (.reg 11)))
        s .normal s1 9 :=
      runs_assign_iff.mpr ⟨nextVal, by
        simp [Expr.eval, BinOp.eval, h15, h14, h12, h11, hrebW j hjLe, hrebEq, haddW, hmulW, nextVal],
        rfl, rfl, rfl⟩
    have r2 : Runs w p bits (.store (.bin .add (.reg 1) (.reg 12)) (.reg 15)) s1 .normal s2 5 :=
      runs_store_iff.mpr ⟨quotaBase + j, nextVal,
        by simp [Expr.eval, BinOp.eval, s1, h1, h12, show quotaBase + j < 2 ^ w by omega],
        by simp [Expr.eval, s1], rfl, rfl, rfl⟩
    refine ⟨.normal, s2, 15, runs_seq_iff.mpr (Or.inr ⟨s1, 9, 5, r1, r2, rfl⟩), ⟨⟨by omega,
      by simp, by simp [s2, s1, nextVal, hornerQuota],
      fun r h12' h15' => by
        simpa [s2, s1, Function.update_of_ne h12', Function.update_of_ne h15'] using hregs r h12' h15',
      fun k hk => by
        by_cases hkj : k = j
        · subst hkj; simp only [s2, Function.update_self]; exact hornerQuota_succ_eq B reb k
        · simp only [s2, s1, Function.update_of_ne (show quotaBase + k ≠ quotaBase + j by omega)]
          exact hprev k (by omega),
      fun a ha => by
        simp only [s2, s1, Function.update_of_ne (show a ≠ quotaBase + j by omega)]
        exact hfr a (by omega)⟩, by simp [s2, s1, h12]⟩, by dsimp; omega⟩
  have hloop := Triple.forRange_const (p := p) (P := fun s => s = st) (Inv := Inv)
    (r := 12) (lo := .const 0) (hi := .reg 13) 17 0 (d + 1) (Nat.zero_le _) hw1 (fun _ => hdW)
    (by
      intro s hs; subst hs
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], Nat.zero_le _, by simp,
        by simp [hr15, hornerQuota], fun r h12 _ => by simp [Function.update_of_ne h12],
        fun k hk => by omega, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.1)
    (fun _ s _ _ h => by simp [Expr.eval, (h.2.2.2.1 13 (by decide) (by decide)).trans hr13])
    hstep
  obtain ⟨o, out, cost, hr, hInv, hc⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hInv
  | normal =>
    refine ⟨out, cost, hr, by simp [Expr.size] at hc; omega,
      fun i hi => hInv.2.2.2.2.1 i (by omega),
      fun a ha => hInv.2.2.2.2.2 a (by omega)⟩

/-- Full execution of `shiftQuotaWriterBody threshold`: computes `shiftQuotaWord` for all
`i ≤ cfg.P.d` and `⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊` at `quotaBase + (cfg.P.d + 1)`, framing
all other memory cells, in at most `shiftQuotaWriterBudget cfg.P.d cfg.P.M₀` steps. -/
theorem shiftQuotaWriterBody_runs {w L P m V psi k epsExp drainUnit threshold : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    {root quotaBase pos : ℕ} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    (hM0 : cfg.P.M₀ = max m threshold)
    (hpsi : psi = ⌈cfg.Ψ⌉₊)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hfootW : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < 2 ^ w)
    (hQuotasW : ∀ i ≤ cfg.P.d,
      shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i < 2 ^ w)
    (hqOut : ∀ i ≤ cfg.P.d + 1,
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok (quotaBase + i))
    (hqEnd : quotaBase + cfg.P.d + 1 < 2 ^ w) :
    ∃ cost out,
      Runs w p ω (shiftQuotaWriterBody threshold) (startState [root, quotaBase] mem pos)
        (.returned 0) out cost ∧
      cost ≤ shiftQuotaWriterBudget cfg.P.d cfg.P.M₀ ∧
      (∀ i ≤ cfg.P.d, out.mem (quotaBase + i) =
        shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i) ∧
      out.mem (quotaBase + (cfg.P.d + 1)) = ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ ∧
      (∀ a, a < quotaBase ∨ quotaBase + cfg.P.d + 1 < a → out.mem a = mem a) := by
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  let d := cfg.P.d
  let kB := cfg.P.k
  let M₀ := cfg.P.M₀
  let ψg := alg2PsiGameNat psi M₀
  let B := shiftQuotaBase psi M₀ kB
  have hQD : gameShiftBoundNat B model.chain.rebuildCount d < 2 ^ w := by
    have h := hQuotasW d le_rfl
    rw [shiftQuotaWord_eq_gameShiftBoundNat, ← hpsi] at h
    exact h
  have hB10 : 10 ≤ B := shiftQuotaBase_ge_ten psi M₀ cfg.P.hk
  have hB1 : 1 ≤ B := by omega
  have hM0_100 : 100 * M₀ ≤ gameShiftBoundNat B model.chain.rebuildCount d :=
    (hundred_mul_M0_le_basePow cfg.P psi).trans (gameShiftBoundNat_ge_basePow B _ d)
  have hM0_pos : 1 ≤ M₀ := cfg.P.hM₀
  have hw100 : 100 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw10 : 10 < 2 ^ w := by omega
  have hw13 : 13 < 2 ^ w := by omega
  have hM02W : M₀ + 2 < 2 ^ w := by omega
  have hthW : threshold < 2 ^ w := by
    have : threshold ≤ M₀ := by change threshold ≤ cfg.P.M₀; rw [hM0]; exact le_max_right m threshold
    omega
  have h2d1W : 2 * (d + 1) < 2 ^ w := by
    have h1 := two_mul_succ_le_ten_pow_succ d
    have h2 : 10 ^ (d + 1) ≤ B ^ (d + 1) := Nat.pow_le_pow_left hB10 _
    have h3 := gameShiftBoundNat_ge_basePow B model.chain.rebuildCount d
    omega
  have hd1W : d + 1 < 2 ^ w := by omega
  have hB_le_QD : B ≤ gameShiftBoundNat B model.chain.rebuildCount d :=
    calc B = B ^ 1 := (pow_one B).symm
      _ ≤ B ^ (d + 1) := Nat.pow_le_pow_right hB1 (by omega)
      _ ≤ gameShiftBoundNat B model.chain.rebuildCount d := gameShiftBoundNat_ge_basePow B _ d
  have hBW : B < 2 ^ w := lt_of_le_of_lt hB_le_QD hQD
  have h10ψW : 10 * ψg < 2 ^ w := by
    have : 10 * ψg ≤ B := Nat.le_mul_of_pos_right _ cfg.P.hk
    omega
  have h2ψW : 2 * ψg < 2 ^ w := by omega
  have hψW : ψg < 2 ^ w := by omega
  -- Extract layout facts from `hrep`
  obtain ⟨hrootDir, _, _, hchP, _, _, _, _, hsched, _, _, _, _, _, _, _, _, _, _, htags⟩ := hrep
  obtain ⟨hOwn, t1, t2, _, _, t5, _⟩ := htags
  have hTagLt {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : a < 2 ^ w :=
    hfootW a (Or.inl (hOwn a (ht ▸ hv)))
  have hroot0W : root < 2 ^ w := by simpa using hTagLt (t1 0 (by decide)) (by decide)
  have hroot2W : root + 2 < 2 ^ w := hTagLt (t1 2 (by decide)) (by decide)
  have hh9W : tok.handle + 9 < 2 ^ w := hTagLt (t2 9 (by decide)) (by decide)
  have hh11W : tok.handle + 11 < 2 ^ w := hTagLt (t2 11 (by decide)) (by decide)
  have hh12W : tok.handle + 12 < 2 ^ w := hTagLt (t2 12 (by decide)) (by decide)
  have hh13W : tok.handle + 13 < 2 ^ w := hTagLt (t2 13 (by decide)) (by decide)
  have hrebBaseW : tok.levelsEnd + 2 * (d + 1) < 2 ^ w :=
    hTagLt (t5 (2 * (d + 1)) (by omega)) (by decide)
  have hrebAddrW : ∀ i ≤ d, tok.levelsEnd + 2 * (d + 1) + i < 2 ^ w := fun i hi => by
    have heq : tok.levelsEnd + 2 * (d + 1) + i = tok.levelsEnd + (2 * (d + 1) + i) := by omega
    rw [heq]; exact hTagLt (t5 (2 * (d + 1) + i) (by omega)) (by decide)
  have hrebDisj : ∀ i ≤ d, ∀ j ≤ d + 1, tok.levelsEnd + 2 * (d + 1) + i ≠ quotaBase + j := by
    intro i hi j hj heq
    have hfoot : Rrep.foot root tok (tok.levelsEnd + 2 * (d + 1) + i) := by
      have h1 : tok.levelsEnd + 2 * (d + 1) + i = tok.levelsEnd + (2 * (d + 1) + i) := by omega
      rw [h1]; exact Or.inl (hOwn _ (by rw [t5 (2 * (d + 1) + i) (by omega)]; decide))
    rw [heq] at hfoot
    exact hqOut j hj hfoot
  have hroot0M : mem root = tok.handle := by simpa using hrootDir 0 (by simp)
  have hroot2M : mem (root + 2) = tok.levelsEnd := by simpa using hrootDir 2 (by simp)
  have hmM : mem (tok.handle + 9) = m := by simpa [Nat.add_assoc] using hchP 0 (by simp)
  have hdM : mem (tok.handle + 11) = d := by simpa [Nat.add_assoc] using hchP 2 (by simp)
  have hkM : mem (tok.handle + 12) = kB := by simpa [Nat.add_assoc] using hchP 3 (by simp)
  have hpsiM : mem (tok.handle + 13) = psi := by simpa [Nat.add_assoc] using hchP 4 (by simp)
  -- Step 1: initial loads into `regs 2..7`
  let s0 := startState [root, quotaBase] mem pos
  let s1 : State := { s0 with regs := Function.update s0.regs 2 tok.handle }
  let s2 : State := { s1 with regs := Function.update s1.regs 3 tok.levelsEnd }
  let s3 : State := { s2 with regs := Function.update s2.regs 4 d }
  let s4 : State := { s3 with regs := Function.update s3.regs 5 kB }
  let s5 : State := { s4 with regs := Function.update s4.regs 6 psi }
  let s6 : State := { s5 with regs := Function.update s5.regs 7 m }
  have r1 : Runs w p ω (.assign 2 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨tok.handle, by simp [Expr.eval, s0, startState, hroot0M], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 0) (.const 2)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨tok.levelsEnd, by
      simp [Expr.eval, BinOp.eval, s1, s0, startState, hw2, hroot2W, hroot2M], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 2) (.const 11)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨d, by
      simp [Expr.eval, BinOp.eval, s2, s1, s0, startState, show 11 < 2 ^ w by omega, hh11W, hdM], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 2) (.const 12)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨kB, by
      simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState, show 12 < 2 ^ w by omega, hh12W, hkM], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 2) (.const 13)))) s4 .normal s5 5 :=
    runs_assign_iff.mpr ⟨psi, by
      simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, s0, startState, hw13, hh13W, hpsiM], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 2) (.const 9)))) s5 .normal s6 5 :=
    runs_assign_iff.mpr ⟨m, by
      simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, s0, startState, show 9 < 2 ^ w by omega, hh9W, hmM],
      rfl, rfl, rfl⟩
  -- Step 2: `reg 7 := max m threshold = M₀`
  let s7 : State := { s6 with regs := Function.update s6.regs 7 M₀ }
  have hCondMax : ∃ cMax,
      Runs w p ω (.cond (.bin .lt (.reg 7) (.const threshold)) (.assign 7 (.const threshold)) .nop)
        s6 .normal s7 cMax ∧ cMax ≤ 6 := by
    by_cases hlt : m < threshold
    · have hM0eq : M₀ = threshold := by rw [show M₀ = max m threshold from hM0, max_eq_right (by omega)]
      have hrA : Runs w p ω (.assign 7 (.const threshold)) s6 .normal s7 2 :=
        runs_assign_iff.mpr ⟨threshold, by simp [Expr.eval, hthW], rfl,
          by simp [s7, hM0eq], rfl⟩
      exact ⟨6, runs_cond_iff.mpr ⟨1, 2, by simp [Expr.eval, BinOp.eval, s6, hthW, hlt, hw1],
        by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]; exact hrA, by simp [Expr.size]⟩, le_rfl⟩
    · have hM0eq : M₀ = m := by rw [show M₀ = max m threshold from hM0, max_eq_left (by omega)]
      have hs7eq : s7 = s6 := by
        dsimp only [s7]
        have hregs : Function.update s6.regs 7 M₀ = s6.regs := by
          funext r
          by_cases hr : r = 7
          · subst hr; simp [s6, hM0eq]
          · simp [Function.update_of_ne hr]
        rw [hregs]
      refine ⟨5, runs_cond_iff.mpr ⟨0, 1,
        by simp [Expr.eval, BinOp.eval, s6, hthW, hlt, show 0 < 2 ^ w by omega],
        by simp only [↓reduceIte]; rw [hs7eq]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩,
        by simp [Expr.size]⟩, by decide⟩
  obtain ⟨cMax, r7, hcMax⟩ := hCondMax
  -- Step 3: initialize `reg 8 := M₀ + 1`, `reg 9 := 0`, run `clog2Loop`
  let s8 : State := { s7 with regs := Function.update s7.regs 8 (M₀ + 1) }
  let s9 : State := { s8 with regs := Function.update s8.regs 9 0 }
  have r8 : Runs w p ω (.assign 8 (.bin .add (.reg 7) (.const 1))) s7 .normal s8 4 :=
    runs_assign_iff.mpr ⟨M₀ + 1, by
      simp [Expr.eval, BinOp.eval, s7, hw1, show M₀ + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 9 (.const 0)) s8 .normal s9 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  obtain ⟨s10, cLog, r10, hcLog, h9_10, hmem10, hregs10⟩ :=
    clog2Loop_runs (w := w) (x₀ := M₀ + 1) (p := p) (ω := ω) (st := s9)
      (by omega) (by simp [s9, s8]) (by simp [s9]) hM02W hw2
  have h1_10 : s10.regs 1 = quotaBase :=
    (hregs10 1 (by decide) (by decide)).trans (by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState])
  have h3_10 : s10.regs 3 = tok.levelsEnd :=
    (hregs10 3 (by decide) (by decide)).trans (by simp [s9, s8, s7, s6, s5, s4, s3, s2])
  have h4_10 : s10.regs 4 = d :=
    (hregs10 4 (by decide) (by decide)).trans (by simp [s9, s8, s7, s6, s5, s4, s3])
  have h5_10 : s10.regs 5 = kB :=
    (hregs10 5 (by decide) (by decide)).trans (by simp [s9, s8, s7, s6, s5, s4])
  have h6_10 : s10.regs 6 = psi :=
    (hregs10 6 (by decide) (by decide)).trans (by simp [s9, s8, s7, s6, s5])
  -- Step 4: compute `ψg`, `B`, `d + 1`, store `2 * ψg`, set up `rebBase` and `acc = 1`
  let s11 : State := { s10 with regs := Function.update s10.regs 10 ψg }
  let s12 : State := { s11 with regs := Function.update s11.regs 11 B }
  let s13 : State := { s12 with regs := Function.update s12.regs 13 (d + 1) }
  let s14 : State := { s13 with mem := Function.update s13.mem (quotaBase + (d + 1)) (2 * ψg) }
  let s15 : State := { s14 with regs := Function.update s14.regs 14 (tok.levelsEnd + 2 * (d + 1)) }
  let s16 : State := { s15 with regs := Function.update s15.regs 15 1 }
  have r11 : Runs w p ω
      (.assign 10 (.bin .add (.bin .add (.bin .mul (.const 2) (.reg 6)) (.reg 9)) (.const 1)))
      s10 .normal s11 8 :=
    runs_assign_iff.mpr ⟨ψg, by
      simp [Expr.eval, BinOp.eval, h6_10, h9_10, hw2, hw1,
        show 2 * psi < 2 ^ w by dsimp only [ψg, alg2PsiGameNat] at hψW; omega,
        show 2 * psi + Nat.clog 2 (M₀ + 1) < 2 ^ w by dsimp only [ψg, alg2PsiGameNat] at hψW; omega,
        show 2 * psi + Nat.clog 2 (M₀ + 1) + 1 < 2 ^ w from hψW, ψg, alg2PsiGameNat],
      rfl, rfl, rfl⟩
  have r12 : Runs w p ω (.assign 11 (.bin .mul (.bin .mul (.const 10) (.reg 10)) (.reg 5)))
      s11 .normal s12 6 :=
    runs_assign_iff.mpr ⟨B, by
      have hBdef : 10 * ψg * kB = B := rfl
      simp [Expr.eval, BinOp.eval, s11, h5_10, hw10, h10ψW, hBdef, hBW],
      rfl, rfl, rfl⟩
  have r13 : Runs w p ω (.assign 13 (.bin .add (.reg 4) (.const 1))) s12 .normal s13 4 :=
    runs_assign_iff.mpr ⟨d + 1, by
      simp [Expr.eval, BinOp.eval, s12, s11, h4_10, hw1, hd1W], rfl, rfl, rfl⟩
  have r14 : Runs w p ω (.store (.bin .add (.reg 1) (.reg 13)) (.bin .mul (.const 2) (.reg 10)))
      s13 .normal s14 7 :=
    runs_store_iff.mpr ⟨quotaBase + (d + 1), 2 * ψg,
      by simp [Expr.eval, BinOp.eval, s13, s12, s11, h1_10, show quotaBase + (d + 1) < 2 ^ w by omega],
      by simp [Expr.eval, BinOp.eval, s13, s12, s11, hw2, h2ψW], rfl, rfl, rfl⟩
  have r15 : Runs w p ω (.assign 14 (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 13))))
      s14 .normal s15 6 :=
    runs_assign_iff.mpr ⟨tok.levelsEnd + 2 * (d + 1), by
      simp [Expr.eval, BinOp.eval, s14, s13, s12, s11, h3_10, hw2, h2d1W, hrebBaseW],
      rfl, rfl, rfl⟩
  have r16 : Runs w p ω (.assign 15 (.const 1)) s15 .normal s16 2 :=
    runs_assign_iff.mpr ⟨1, by simp [Expr.eval, hw1], rfl, rfl, rfl⟩
  -- Step 5: run `hornerQuotaLoop`
  have hreb16 : ∀ i ≤ d, s16.mem (tok.levelsEnd + 2 * (d + 1) + i) = model.chain.rebuildCount i := by
    intro i hi
    have hne : tok.levelsEnd + 2 * (d + 1) + i ≠ quotaBase + (d + 1) := hrebDisj i hi (d + 1) le_rfl
    change Function.update s13.mem _ _ _ = _
    rw [Function.update_of_ne hne]
    exact (congrFun hmem10 _).trans (hsched.2.2.1 i hi)
  obtain ⟨s17, cHorner, r17, hcHorner, hquotas17, hfr17⟩ :=
    hornerQuotaLoop_runs (w := w) (quotaBase := quotaBase)
      (rebBase := tok.levelsEnd + 2 * (d + 1)) (d := d) (B := B)
      (reb := model.chain.rebuildCount) (p := p) (ω := ω) (st := s16)
      hB1 (by simp [s16, s15, s14, s13, s12, s11, h1_10]) (by simp [s16, s15, s14, s13, s12])
      (by simp [s16, s15, s14, s13]) (by simp [s16, s15]) (by simp [s16])
      hreb16 (fun i hi j hj => hrebDisj i hi j (by omega)) hrebAddrW hqEnd hd1W hQD hw1
  have r18 : Runs w p ω (.ret (.const 0)) s17 (.returned 0) s17 2 :=
    runs_ret_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have rFull : Runs w p ω (shiftQuotaWriterBody threshold) s0 (.returned 0) s17 _ :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 5, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, 5, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, cMax, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 4, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, 2, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨s10, cLog, _, r10,
    runs_seq_iff.mpr (Or.inr ⟨s11, 8, _, r11,
    runs_seq_iff.mpr (Or.inr ⟨s12, 6, _, r12,
    runs_seq_iff.mpr (Or.inr ⟨s13, 4, _, r13,
    runs_seq_iff.mpr (Or.inr ⟨s14, 7, _, r14,
    runs_seq_iff.mpr (Or.inr ⟨s15, 6, _, r15,
    runs_seq_iff.mpr (Or.inr ⟨s16, 2, _, r16,
    runs_seq_iff.mpr (Or.inr ⟨s17, cHorner, 2, r17, r18, rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  refine ⟨_, s17, rFull, ?_, ?_, ?_, ?_⟩
  · unfold shiftQuotaWriterBudget
    dsimp only [d, M₀] at hcLog hcHorner
    omega
  · intro i hi
    rw [hquotas17 i hi, shiftQuotaWord_eq_gameShiftBoundNat, ← hpsi]
  · rw [hfr17 (quotaBase + (d + 1)) (Or.inr (by omega)), ceil_two_mul_alg2PsiGame, ← hpsi]
    simp [s16, s15, s14, ψg, d, M₀]
  · intro a ha
    rw [hfr17 a (by omega)]
    change Function.update s13.mem _ _ a = mem a
    rw [Function.update_of_ne (by omega)]
    exact congrFun hmem10 a

/-- Discharges `ShiftQuotaWriterSpec` using the deterministic self-contained procedure
`shiftQuotaWriterBody threshold`, with polylogarithmic budget `shiftQuotaWriterBudget cfg.P.d cfg.P.M₀`. -/
theorem shiftQuotaWriterSpec_proved
    {w L P m V psi k epsExp drainUnit shiftQuotaWriterProc threshold : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    (hAt : p.procs[shiftQuotaWriterProc]? = some (shiftQuotaWriterBody threshold))
    (hM0 : cfg.P.M₀ = max m threshold)
    (hpsi : psi = ⌈cfg.Ψ⌉₊) :
    ShiftQuotaWriterSpec w L P m V psi k epsExp drainUnit cfg Rcore p
      shiftQuotaWriterProc (shiftQuotaWriterBudget cfg.P.d cfg.P.M₀) := by
  refine ⟨shiftQuotaWriterBody threshold, hAt, ?_⟩
  intro root quotaBase pos ω mem model tok hrep hfootW hQuotasW hqOut hqEnd
  exact shiftQuotaWriterBody_runs hM0 hpsi hrep hfootW hQuotasW hqOut hqEnd

end MinCostFlow.MinRatio
