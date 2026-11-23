module

public import MinCostFlow.MinRatio.RebuildGuard
import MinCostFlow.MinRatio.ShiftForestScan
import Mathlib.Tactic

/-!
# Certifying the level size at initialization

Bound the expression before taking its ceiling, and test the resulting
integer cross-products on the machine.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain

/-- A certified enclosure of Algorithm 1's stretch parameter gives
an enclosure of its level size before taking the ceiling (page 20). -/
theorem initLevelSize_bounds (TP : SparseCoreParams) (P : ChainParams) (i : ℕ)
    {lower upper : ℝ} (hzero : 0 ≤ lower)
    (hlo : lower ≤ TP.γ_ℓ (P.M₀ ^ 2)) (hhi : TP.γ_ℓ (P.M₀ ^ 2) ≤ upper) :
    (P.M₀ : ℝ) * lower * (lower / P.k) ^ i ≤
      (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i ∧
    (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i ≤
      (P.M₀ : ℝ) * upper * (upper / P.k) ^ i := by
  have hmono (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      (P.M₀ : ℝ) * a * (a / P.k) ^ i ≤ (P.M₀ : ℝ) * b * (b / P.k) ^ i := by
    have hk : (0 : ℝ) ≤ P.k := by positivity
    have hm : (0 : ℝ) ≤ P.M₀ := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left hab hm)
      (pow_le_pow_left₀ (div_nonneg ha hk) (div_le_div_of_nonneg_right hab hk) i)
      (by positivity) (mul_nonneg hm (ha.trans hab))
  exact ⟨hmono _ _ hzero hlo, hmono _ _ (hzero.trans hlo) hhi⟩

/-- Endpoints contained between the same consecutive integers certify
the exact ceiling used as the level size in Algorithm 1 (page 20). -/
theorem initLevelSize_eq_of_bounds (TP : SparseCoreParams) (P : ChainParams) (i q : ℕ)
    {lower upper : ℝ} (hzero : 0 ≤ lower)
    (hlo : lower ≤ TP.γ_ℓ (P.M₀ ^ 2)) (hhi : TP.γ_ℓ (P.M₀ ^ 2) ≤ upper)
    (hleft : (q : ℝ) < (P.M₀ : ℝ) * lower * (lower / P.k) ^ i)
    (hright : (P.M₀ : ℝ) * upper * (upper / P.k) ^ i ≤ (q + 1 : ℕ)) :
    levelM TP P i = q + 1 := by
  obtain ⟨hl, hu⟩ := initLevelSize_bounds TP P i hzero hlo hhi
  unfold levelM
  exact (Nat.ceil_eq_iff (Nat.succ_ne_zero q)).mpr
    ⟨by simpa using hleft.trans_le hl, hu.trans hright⟩

/-- Use integer cross-products to certify the ceiling of a level size
when the stretch endpoints share a positive denominator. -/
theorem initLevelSize_eq_of_scaledBounds (TP : SparseCoreParams) (P : ChainParams)
    (i q lower upper scale : ℕ) (hs : 0 < scale)
    (hlo : (lower : ℝ) / scale ≤ TP.γ_ℓ (P.M₀ ^ 2))
    (hhi : TP.γ_ℓ (P.M₀ ^ 2) ≤ (upper : ℝ) / scale)
    (hleft : q * (scale * (scale * P.k) ^ i) < P.M₀ * lower ^ (i + 1))
    (hright : P.M₀ * upper ^ (i + 1) ≤ (q + 1) * (scale * (scale * P.k) ^ i)) :
    levelM TP P i = q + 1 := by
  have hscale : (0 : ℝ) < scale := by exact_mod_cast hs
  have hk : (0 : ℝ) < P.k := by exact_mod_cast P.hk
  have hd : 0 < (scale : ℝ) * ((scale : ℝ) * P.k) ^ i := by positivity
  have he (x : ℕ) :
      (P.M₀ : ℝ) * ((x : ℝ) / scale) * (((x : ℝ) / scale) / P.k) ^ i =
        (P.M₀ : ℝ) * (x : ℝ) ^ (i + 1) / ((scale : ℝ) * ((scale : ℝ) * P.k) ^ i) := by
    rw [div_div, div_pow, pow_succ']
    field_simp
  apply initLevelSize_eq_of_bounds TP P i q (by positivity) hlo hhi
  · rw [he]
    apply (lt_div_iff₀ hd).mpr
    exact_mod_cast hleft
  · rw [he]
    apply (div_le_iff₀ hd).mpr
    exact_mod_cast hright

/-- Take the ceiling of the upper endpoint and test the lower endpoint
against the preceding integer to certify the exact Algorithm 1 level size. -/
theorem initLevelSize_eq_of_upperCandidate (TP : SparseCoreParams) (P : ChainParams)
    (i lower upper scale : ℕ) (hs : 0 < scale) (hu : 0 < P.M₀ * upper ^ (i + 1))
    (hlo : (lower : ℝ) / scale ≤ TP.γ_ℓ (P.M₀ ^ 2))
    (hhi : TP.γ_ℓ (P.M₀ ^ 2) ≤ (upper : ℝ) / scale) :
    let den := scale * (scale * P.k) ^ i
    let q := (P.M₀ * upper ^ (i + 1) - 1) / den
    q * den < P.M₀ * lower ^ (i + 1) →
      levelM TP P i = q + 1 := by
  dsimp only
  intro hloTest
  have hk := P.hk
  have hd : 0 < scale * (scale * P.k) ^ i := by positivity
  apply initLevelSize_eq_of_scaledBounds TP P i _ lower upper scale hs hlo hhi hloTest
  have hq : (P.M₀ * upper ^ (i + 1) - 1) / (scale * (scale * P.k) ^ i) <
      (P.M₀ * upper ^ (i + 1) - 1) / (scale * (scale * P.k) ^ i) + 1 :=
    Nat.lt_succ_self _
  have ht := (Nat.div_lt_iff_lt_mul hd).mp hq
  omega

/-- Check the level ceiling from the lower numerator, upper numerator
and common denominator in registers 14 through 16. A set flag in
register 18 certifies that register 0 holds the exact level size. -/
@[expose] def selectInitLevelSize : Stmt :=
  .assign 17 (.bin .div (.bin .sub (.reg 15) (.const 1)) (.reg 16)) ;;
  .assign 18 (.bin .lt (.bin .mul (.reg 17) (.reg 16)) (.reg 14)) ;;
  .assign 0 (.bin .add (.reg 17) (.const 1))

/-- Under the scaled stretch enclosure, a successful machine check
identifies the exact ceiling used by Algorithm 1 (page 20). -/
theorem selectInitLevelSize_runs (TP : SparseCoreParams) (P : ChainParams)
    (i lower upper scale : ℕ) {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hs : 0 < scale) (hu : 0 < P.M₀ * upper ^ (i + 1))
    (hlo : (lower : ℝ) / scale ≤ TP.γ_ℓ (P.M₀ ^ 2))
    (hhi : TP.γ_ℓ (P.M₀ ^ 2) ≤ (upper : ℝ) / scale)
    (hl : st.regs 14 = P.M₀ * lower ^ (i + 1))
    (hh : st.regs 15 = P.M₀ * upper ^ (i + 1))
    (hd : st.regs 16 = scale * (scale * P.k) ^ i)
    (hw : 1 < 2 ^ w) (hword : P.M₀ * upper ^ (i + 1) < 2 ^ w) :
    ∃ out, Runs w p ω selectInitLevelSize st .normal out 18 ∧
      (out.regs 18 = 1 → out.regs 0 = levelM TP P i) ∧
      (out.regs 18 = 1 ↔ (P.M₀ * upper ^ (i + 1) - 1) / (scale * (scale * P.k) ^ i) *
          (scale * (scale * P.k) ^ i) < P.M₀ * lower ^ (i + 1)) ∧
      (out.regs 18 = 0 ∨ out.regs 18 = 1) ∧
      (∀ r, r ≠ 0 → r ≠ 17 → r ≠ 18 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let den := scale * (scale * P.k) ^ i
  let hi := P.M₀ * upper ^ (i + 1)
  let lo := P.M₀ * lower ^ (i + 1)
  let q := (hi - 1) / den
  let flag := if q * den < lo then 1 else 0
  have hq : q ≤ hi - 1 := Nat.div_le_self _ _
  have hcut : q * den ≤ hi - 1 := Nat.div_mul_le_self _ _
  have hsub : hi - 1 < 2 ^ w := by dsimp [q, hi, den] at *; omega
  have hqw : q < 2 ^ w := by dsimp [q, hi, den] at *; omega
  have hsucc : q + 1 < 2 ^ w := by dsimp [q, hi, den] at *; omega
  have hcutw : q * den < 2 ^ w := by dsimp [q, hi, den] at *; omega
  let s₁ := { st with regs := Function.update st.regs 17 q }
  let s₂ := { s₁ with regs := Function.update s₁.regs 18 flag }
  let out := { s₂ with regs := Function.update s₂.regs 0 (q + 1) }
  have hr₁ : Runs w p ω (.assign 17 (.bin .div (.bin .sub (.reg 15) (.const 1)) (.reg 16)))
      st .normal s₁ 6 :=
    runs_assign_iff.mpr ⟨q, by simp [Expr.eval, BinOp.eval, hh, hd, hw, hi, den, q, show P.M₀ * upper ^ (i + 1) - 1 < 2 ^ w from hsub,
      show (P.M₀ * upper ^ (i + 1) - 1) / (scale * (scale * P.k) ^ i) < 2 ^ w from hqw],
      rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 18 (.bin .lt (.bin .mul (.reg 17) (.reg 16)) (.reg 14)))
      s₁ .normal s₂ 6 :=
    runs_assign_iff.mpr ⟨flag, by
      by_cases hc : q * den < lo <;>
        simp [Expr.eval, BinOp.eval, s₁, hd, hl, den, lo, q, hi, hcutw, flag, hc, hw,
          show 0 < 2 ^ w by positivity], rfl, rfl, rfl⟩
  have hr₃ : Runs w p ω (.assign 0 (.bin .add (.reg 17) (.const 1))) s₂ .normal out 4 :=
    runs_assign_iff.mpr ⟨q + 1, by simp [Expr.eval, BinOp.eval, s₂, s₁, hw, hsucc],
      rfl, rfl, rfl⟩
  refine ⟨out, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s₁, 6, 11, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨s₂, 6, 4, hr₂, hr₃, rfl⟩), rfl⟩)
  · intro h
    have hc : q * den < lo := by simpa [out, s₂, flag] using h
    simpa [out] using (initLevelSize_eq_of_upperCandidate TP P i lower upper scale hs hu hlo hhi hc).symm
  · simp [out, s₂, flag, q, den, hi, lo]
  · by_cases hc : q * den < lo <;> simp [out, s₂, flag, hc]
  · intro r h0 h17 h18
    simp [out, s₂, s₁, h0, h17, h18]

/-- Extend the three scaled level-size products by one level. Registers
19 and 20 hold the stretch numerators and 21 holds the denominator
multiplier, scale times the branching factor. -/
@[expose] def advanceInitLevelSizeProducts : Stmt :=
  .assign 14 (.bin .mul (.reg 14) (.reg 19)) ;;
  .assign 15 (.bin .mul (.reg 15) (.reg 20)) ;;
  .assign 16 (.bin .mul (.reg 16) (.reg 21))

/-- One level advances the powers in the lower numerator, upper
numerator, and denominator using three checked multiplications. -/
theorem advanceInitLevelSizeProducts_runs {w M k i lower upper scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hl : st.regs 14 = M * lower ^ (i + 1)) (hu : st.regs 15 = M * upper ^ (i + 1))
    (hd : st.regs 16 = scale * (scale * k) ^ i)
    (hlf : st.regs 19 = lower) (huf : st.regs 20 = upper) (hdf : st.regs 21 = scale * k)
    (hlw : M * lower ^ (i + 2) < 2 ^ w) (huw : M * upper ^ (i + 2) < 2 ^ w)
    (hdw : scale * (scale * k) ^ (i + 1) < 2 ^ w) :
    ∃ out, Runs w p ω advanceInitLevelSizeProducts st .normal out 14 ∧
      out.regs 14 = M * lower ^ (i + 2) ∧ out.regs 15 = M * upper ^ (i + 2) ∧
      out.regs 16 = scale * (scale * k) ^ (i + 1) ∧
      (∀ r, r ≠ 14 → r ≠ 15 → r ≠ 16 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let l := M * lower ^ (i + 2)
  let u := M * upper ^ (i + 2)
  let d := scale * (scale * k) ^ (i + 1)
  let s₁ := { st with regs := Function.update st.regs 14 l }
  let s₂ := { s₁ with regs := Function.update s₁.regs 15 u }
  let out := { s₂ with regs := Function.update s₂.regs 16 d }
  have hl' : M * lower ^ (i + 1) * lower = l := by
    simp only [l, show i + 2 = (i + 1) + 1 by omega, pow_succ, Nat.mul_assoc]
  have hu' : M * upper ^ (i + 1) * upper = u := by
    simp only [u, show i + 2 = (i + 1) + 1 by omega, pow_succ, Nat.mul_assoc]
  have hd' : scale * (scale * k) ^ i * (scale * k) = d := by
    simp only [d, pow_succ, Nat.mul_assoc]
  have hr₁ : Runs w p ω (.assign 14 (.bin .mul (.reg 14) (.reg 19))) st .normal s₁ 4 :=
    runs_assign_iff.mpr ⟨l, by simp [Expr.eval, BinOp.eval, hl, hlf, hl', show l < 2 ^ w from hlw],
      rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 15 (.bin .mul (.reg 15) (.reg 20))) s₁ .normal s₂ 4 :=
    runs_assign_iff.mpr ⟨u, by simp [Expr.eval, BinOp.eval, s₁, hu, huf, hu', show u < 2 ^ w from huw],
      rfl, rfl, rfl⟩
  have hr₃ : Runs w p ω (.assign 16 (.bin .mul (.reg 16) (.reg 21))) s₂ .normal out 4 :=
    runs_assign_iff.mpr ⟨d, by simp [Expr.eval, BinOp.eval, s₂, s₁, hd, hdf, hd', show d < 2 ^ w from hdw],
      rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨s₁, 4, 9, hr₁,
    runs_seq_iff.mpr (Or.inr ⟨s₂, 4, 4, hr₂, hr₃, rfl⟩), rfl⟩),
    by simp [out, s₂, s₁, l], by simp [out, s₂, u], by simp [out, d],
    fun r h14 h15 h16 => by simp [out, s₂, s₁, h14, h15, h16], rfl, rfl⟩

/-- Prepare the scaled products for level zero from the runtime base
size, branching factor, and stretch enclosure. -/
@[expose] def startInitLevelSizeProducts : Stmt :=
  .assign 14 (.bin .mul (.reg 22) (.reg 19)) ;;
  .assign 15 (.bin .mul (.reg 22) (.reg 20)) ;;
  .assign 16 (.reg 23) ;;
  .assign 21 (.bin .mul (.reg 23) (.reg 1))

/-- The initial products and denominator multiplier fit whenever
their three word multiplications fit. -/
theorem startInitLevelSizeProducts_runs {w M k lower upper scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hM : st.regs 22 = M) (hk : st.regs 1 = k)
    (hl : st.regs 19 = lower) (hu : st.regs 20 = upper) (hs : st.regs 23 = scale)
    (hlw : M * lower < 2 ^ w) (huw : M * upper < 2 ^ w)
    (hdw : scale * k < 2 ^ w) :
    ∃ out, Runs w p ω startInitLevelSizeProducts st .normal out 17 ∧
      out.regs 14 = M * lower ∧ out.regs 15 = M * upper ∧
      out.regs 16 = scale ∧ out.regs 21 = scale * k ∧
      (∀ r, r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 21 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let s₁ := { st with regs := Function.update st.regs 14 (M * lower) }
  let s₂ := { s₁ with regs := Function.update s₁.regs 15 (M * upper) }
  let s₃ := { s₂ with regs := Function.update s₂.regs 16 scale }
  let out := { s₃ with regs := Function.update s₃.regs 21 (scale * k) }
  have hr₁ : Runs w p ω (.assign 14 (.bin .mul (.reg 22) (.reg 19))) st .normal s₁ 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hM, hl, hlw], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 15 (.bin .mul (.reg 22) (.reg 20))) s₁ .normal s₂ 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, s₁, hM, hu, huw], rfl, rfl, rfl⟩
  have hr₃ : Runs w p ω (.assign 16 (.reg 23)) s₂ .normal s₃ 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s₂, s₁, hs], rfl, rfl, rfl⟩
  have hr₄ : Runs w p ω (.assign 21 (.bin .mul (.reg 23) (.reg 1))) s₃ .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, s₃, s₂, s₁, hs, hk, hdw],
      rfl, rfl, rfl⟩
  refine ⟨out, ?_, by simp [out, s₃, s₂, s₁], by simp [out, s₃, s₂],
    by simp [out, s₃], by simp [out], ?_, rfl, rfl⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s₁, 4, 12, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨s₂, 4, 7, hr₂,
        runs_seq_iff.mpr (Or.inr ⟨s₃, 2, 4, hr₃, hr₄, rfl⟩), rfl⟩), rfl⟩)
  · intro r h14 h15 h16 h21
    simp [out, s₃, s₂, s₁, h14, h15, h16, h21]

/-- Prepare and check the level-zero ceiling using the same scaled
products that later levels extend. -/
@[expose] def selectInitBaseLevelSize : Stmt :=
  startInitLevelSizeProducts ;; selectInitLevelSize

/-- If the scaled stretch bounds determine the level-zero ceiling,
register zero holds the exact level size for the threshold calculation. -/
theorem selectInitBaseLevelSize_runs (TP : SparseCoreParams) (P : ChainParams)
    (lower upper scale : ℕ) {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hM : st.regs 22 = P.M₀) (hk : st.regs 1 = P.k)
    (hl : st.regs 19 = lower) (hu : st.regs 20 = upper) (hs : st.regs 23 = scale)
    (hscale : 0 < scale) (hupper : 0 < P.M₀ * upper)
    (hlo : (lower : ℝ) / scale ≤ TP.γ_ℓ (P.M₀ ^ 2))
    (hhi : TP.γ_ℓ (P.M₀ ^ 2) ≤ (upper : ℝ) / scale)
    (hlw : P.M₀ * lower < 2 ^ w) (huw : P.M₀ * upper < 2 ^ w)
    (hdw : scale * P.k < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ out, Runs w p ω selectInitBaseLevelSize st .normal out 36 ∧
      (out.regs 18 = 1 → out.regs 0 = levelM TP P 0) ∧
      (out.regs 18 = 1 ↔ (P.M₀ * upper - 1) / scale * scale < P.M₀ * lower) ∧
      (out.regs 18 = 0 ∨ out.regs 18 = 1) ∧
      out.regs 14 = P.M₀ * lower ∧ out.regs 15 = P.M₀ * upper ∧
      out.regs 16 = scale ∧ out.regs 21 = scale * P.k ∧
      (∀ r, r ≠ 0 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 → r ≠ 18 → r ≠ 21 →
        out.regs r = st.regs r) ∧ out.mem = st.mem ∧ out.pos = st.pos := by
  obtain ⟨mid, hr, hloReg, hhiReg, hdReg, hmulReg, hreg, hm, hp⟩ :=
    startInitLevelSizeProducts_runs (p := p) (ω := ω) hM hk hl hu hs hlw huw hdw
  obtain ⟨out, hr', hsize, htest, hflag, hreg', hm', hp'⟩ :=
    selectInitLevelSize_runs (p := p) (ω := ω) TP P 0 lower upper scale hscale
      (by simpa using hupper) hlo hhi (by simpa using hloReg) (by simpa using hhiReg)
      (by simpa using hdReg) hw (by simpa using huw)
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 17, 18, hr, hr', rfl⟩), hsize, by simpa using htest, hflag,
    (hreg' 14 (by decide) (by decide) (by decide)).trans hloReg,
    (hreg' 15 (by decide) (by decide) (by decide)).trans hhiReg,
    (hreg' 16 (by decide) (by decide) (by decide)).trans hdReg,
    (hreg' 21 (by decide) (by decide) (by decide)).trans hmulReg,
    fun r h0 h14 h15 h16 h17 h18 h21 => (hreg' r h0 h17 h18).trans (hreg r h14 h15 h16 h21),
    hm'.trans hm, hp'.trans hp⟩

/-- Advance the scaled products and check the ceiling for the next level. -/
@[expose] def selectInitNextLevelSize : Stmt :=
  advanceInitLevelSizeProducts ;; selectInitLevelSize

/-- The next level's products remain available after the ceiling check.
A set flag certifies the exact threshold numerator for that level. -/
theorem selectInitNextLevelSize_runs (TP : SparseCoreParams) (P : ChainParams)
    (i lower upper scale : ℕ) {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hl : st.regs 14 = P.M₀ * lower ^ (i + 1))
    (hu : st.regs 15 = P.M₀ * upper ^ (i + 1))
    (hd : st.regs 16 = scale * (scale * P.k) ^ i)
    (hlf : st.regs 19 = lower) (huf : st.regs 20 = upper) (hdf : st.regs 21 = scale * P.k)
    (hs : 0 < scale) (hupper : 0 < P.M₀ * upper ^ (i + 2))
    (hlo : (lower : ℝ) / scale ≤ TP.γ_ℓ (P.M₀ ^ 2))
    (hhi : TP.γ_ℓ (P.M₀ ^ 2) ≤ (upper : ℝ) / scale)
    (hlw : P.M₀ * lower ^ (i + 2) < 2 ^ w) (huw : P.M₀ * upper ^ (i + 2) < 2 ^ w)
    (hdw : scale * (scale * P.k) ^ (i + 1) < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ out, Runs w p ω selectInitNextLevelSize st .normal out 33 ∧
      (out.regs 18 = 1 → out.regs 0 = levelM TP P (i + 1)) ∧
      (out.regs 18 = 1 ↔ (P.M₀ * upper ^ (i + 2) - 1) / (scale * (scale * P.k) ^ (i + 1)) *
          (scale * (scale * P.k) ^ (i + 1)) < P.M₀ * lower ^ (i + 2)) ∧
      (out.regs 18 = 0 ∨ out.regs 18 = 1) ∧
      out.regs 14 = P.M₀ * lower ^ (i + 2) ∧ out.regs 15 = P.M₀ * upper ^ (i + 2) ∧
      out.regs 16 = scale * (scale * P.k) ^ (i + 1) ∧
      (∀ r, r ≠ 0 → r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 17 → r ≠ 18 →
        out.regs r = st.regs r) ∧ out.mem = st.mem ∧ out.pos = st.pos := by
  obtain ⟨mid, hr, hl', hu', hd', hreg, hm, hp⟩ :=
    advanceInitLevelSizeProducts_runs (p := p) (ω := ω) hl hu hd hlf huf hdf hlw huw hdw
  obtain ⟨out, hr', hsize, htest, hflag, hreg', hm', hp'⟩ :=
    selectInitLevelSize_runs (p := p) (ω := ω) TP P (i + 1) lower upper scale
      hs hupper hlo hhi hl' hu' hd' hw huw
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 14, 18, hr, hr', rfl⟩), hsize, htest, hflag,
    (hreg' 14 (by decide) (by decide) (by decide)).trans hl',
    (hreg' 15 (by decide) (by decide) (by decide)).trans hu',
    (hreg' 16 (by decide) (by decide) (by decide)).trans hd',
    fun r h0 h14 h15 h16 h17 h18 => (hreg' r h0 h17 h18).trans (hreg r h14 h15 h16),
    hm'.trans hm, hp'.trans hp⟩

/-- A shared bit budget bounds all products through the last level.
It accounts for the powers before cancellation in the ceiling test. -/
theorem initLevelSize_productWordBounds {w bits d i M k lower upper scale : ℕ}
    (hi : i ≤ d) (hlu : lower ≤ upper)
    (hM : M ≤ 2 ^ bits) (hu : upper ≤ 2 ^ bits)
    (hs : scale ≤ 2 ^ bits) (hsk : scale * k ≤ 2 ^ bits)
    (hw : bits * (d + 2) < w) :
    M * lower ^ (i + 1) < 2 ^ w ∧ M * upper ^ (i + 1) < 2 ^ w ∧
      scale * (scale * k) ^ i < 2 ^ w := by
  have hprod (a b j : ℕ) (ha : a ≤ 2 ^ bits) (hb : b ≤ 2 ^ bits)
      (hj : j + 1 ≤ d + 2) : a * b ^ j < 2 ^ w := by
    have hle : a * b ^ j ≤ 2 ^ (bits * (j + 1)) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm (bits * j) bits, pow_add, pow_mul]
      exact Nat.mul_le_mul ha (Nat.pow_le_pow_left hb j)
    exact hle.trans_lt (Nat.pow_lt_pow_right (by decide)
      ((Nat.mul_le_mul_left bits hj).trans_lt hw))
  exact ⟨hprod M lower (i + 1) hM (hlu.trans hu) (by omega),
    hprod M upper (i + 1) hM hu (by omega), hprod scale (scale * k) i hs hsk (by omega)⟩

end MinCostFlow.MinRatio
