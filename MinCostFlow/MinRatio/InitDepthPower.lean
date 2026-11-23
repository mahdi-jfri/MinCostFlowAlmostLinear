module

import Mathlib.Analysis.Complex.ExponentialBounds
public import MinCostFlow.MinRatio.InitParameterEntry

/-!
# Integer powers for Init depth selection

The chain and sparsifier compare logarithm enclosures with integer powers
of small, runtime candidates. These expressions use the fixed exponents
from the two depth formulas.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Rounding a scaled endpoint upward reduces comparison against an integer
cutoff to comparison of unscaled words. The remainder only contributes
a single carry. -/
theorem initDepth_endpoint_le_iff {value scale cutoff : ℕ} (hs : 0 < scale) :
    value / scale + (if value % scale = 0 then 0 else 1) ≤ cutoff ↔
      value ≤ cutoff * scale := by
  have hsplit : value % scale + value / scale * scale = value := by
    simpa only [mul_comm scale] using Nat.mod_add_div value scale
  have hrem := Nat.mod_lt value hs
  by_cases hzero : value % scale = 0
  · simp only [hzero, zero_add] at hsplit
    rw [ite_eq_left hzero, add_zero]
    exact ⟨fun h => hsplit.ge.trans (Nat.mul_le_mul_right scale h),
      fun h => Nat.le_of_mul_le_mul_right (hsplit.le.trans h) hs⟩
  · rw [ite_eq_right hzero]
    constructor
    · intro h
      have hbound := Nat.mul_le_mul_right scale h
      rw [Nat.add_mul, one_mul] at hbound
      exact (show value ≤ value / scale * scale + scale by omega).trans hbound
    · intro h
      by_contra! hbad
      have hq : cutoff ≤ value / scale := by omega
      have hbound := Nat.mul_le_mul_right scale hq
      omega

/-- Expand a fixed exponent into a product of a runtime expression. -/
@[expose] def initDepthPower (base : Expr) : ℕ → Expr
  | 0 => .const 1
  | n + 1 => .bin .mul base (initDepthPower base n)

/-- Every intermediate power fits if the base and final power fit. -/
theorem initDepthPower_eval {w value : ℕ} {st : State} {base : Expr}
    (hb : Expr.eval w st base = some value) (hw : 1 < 2 ^ w) :
    ∀ n, value ^ n < 2 ^ w → Expr.eval w st (initDepthPower base n) = some (value ^ n) := by
  intro n
  by_cases hzero : value = 0
  · subst value
    induction n with
    | zero => simp [initDepthPower, Expr.eval, hw]
    | succ n ih =>
      intro _
      have hp : 0 ^ n < 2 ^ w := by
        cases n <;> simp [hw]
      simp [initDepthPower, Expr.eval, BinOp.eval, hb, ih hp]
  · induction n with
    | zero => simp [initDepthPower, Expr.eval, hw]
    | succ n ih =>
      intro hf
      have hp : value ^ n < 2 ^ w :=
        (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hzero) (Nat.le_succ n)).trans_lt hf
      rw [initDepthPower]
      simp [Expr.eval, BinOp.eval, hb, ih hp, ← pow_succ', hf]

private theorem initDepthPower_size (base : Expr) (n : ℕ) :
    (initDepthPower base n).size = (base.size + 1) * n + 1 := by
  induction n with
  | zero => simp [initDepthPower, Expr.size_const]
  | succ n ih =>
    simp [initDepthPower, Expr.size_bin, ih, Nat.mul_succ]
    omega

/-- Stage the two bounding powers of the candidate in register 110,
using the logarithm scale in register 111. -/
@[expose] def stageInitDepthPowers (exponent : ℕ) : Stmt :=
  .assign 105 (.bin .mul (initDepthPower (.bin .sub (.reg 110) (.const 1)) exponent) (.reg 111)) ;;
  .assign 106 (.bin .mul (initDepthPower (.reg 110) exponent) (.reg 111))

/-- The staged powers are exact if the larger scaled power fits. -/
theorem stageInitDepthPowers_runs {w candidate scale exponent : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hc : st.regs 110 = candidate) (hs : st.regs 111 = scale)
    (hcWord : candidate < 2 ^ w) (hsPos : 0 < scale) (hw : 1 < 2 ^ w)
    (hfit : candidate ^ exponent * scale < 2 ^ w) :
    ∃ out, Runs w p ω (stageInitDepthPowers exponent) st .normal out (6 * exponent + 9) ∧
      out.regs 105 = (candidate - 1) ^ exponent * scale ∧
      out.regs 106 = candidate ^ exponent * scale ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 105 → r ≠ 106 → out.regs r = st.regs r) := by
  let prev := (candidate - 1) ^ exponent * scale
  let next := candidate ^ exponent * scale
  let left := initDepthPower (.bin .sub (.reg 110) (.const 1)) exponent
  let right := initDepthPower (.reg 110) exponent
  let mid := {st with regs := Function.update st.regs 105 prev}
  let out := {mid with regs := Function.update mid.regs 106 next}
  have hn : candidate ^ exponent ≤ next :=
    Nat.le_mul_of_pos_right _ hsPos
  have hp : (candidate - 1) ^ exponent ≤ candidate ^ exponent :=
    Nat.pow_le_pow_left (Nat.sub_le _ _) _
  have hpFit : (candidate - 1) ^ exponent * scale < 2 ^ w := (Nat.mul_le_mul_right scale hp).trans_lt hfit
  have hleft : Expr.eval w st left = some ((candidate - 1) ^ exponent) :=
    initDepthPower_eval (by
      simp [Expr.eval, BinOp.eval, hc, hw, (Nat.sub_le candidate 1).trans_lt hcWord])
      hw _ (hp.trans_lt (hn.trans_lt hfit))
  have hright : Expr.eval w mid right = some (candidate ^ exponent) :=
    initDepthPower_eval (by simp [Expr.eval, mid, hc]) hw _ (hn.trans_lt hfit)
  have h₁ : Runs w p ω (.assign 105 (.bin .mul left (.reg 111))) st .normal mid
      ((Expr.bin .mul left (.reg 111)).size + 1) :=
    runs_assign_iff.mpr ⟨prev, by simp [Expr.eval, BinOp.eval, hleft, hs, prev, hpFit],
      rfl, rfl, rfl⟩
  have h₂ : Runs w p ω (.assign 106 (.bin .mul right (.reg 111))) mid .normal out
      ((Expr.bin .mul right (.reg 111)).size + 1) :=
    runs_assign_iff.mpr ⟨next, by simp [Expr.eval, BinOp.eval, hright, mid, hs, next, hfit],
      rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, _, _, h₁, h₂, by
      simp [left, right, initDepthPower_size, Expr.size_bin, Expr.size_const, Expr.size_reg]
      omega⟩),
    by simp [out, mid, prev], by simp [out, next], rfl,
    fun r h105 h106 => by simp [out, mid, Function.update_of_ne, h105, h106]⟩

/-- Evaluate and test the adjacent powers for Algorithm 1's chain depth. -/
@[expose] def testInitChainDepth : Stmt :=
  stageInitDepthPowers 48 ;; checkInitDepthBounds

/-- A successful chain-depth test certifies the model's exact ceiling. -/
theorem testInitChainDepth_runs {w m candidate lo hi scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hc : st.regs 110 = candidate) (hs : st.regs 111 = scale)
    (hl : st.regs 107 = lo) (hh : st.regs 108 = hi)
    (hcPos : 0 < candidate) (hcWord : candidate < 2 ^ w)
    (hsPos : 0 < scale) (hw : 1 < 2 ^ w) (hfit : candidate ^ 48 * scale < 2 ^ w)
    (hlo : (lo : ℝ) / scale ≤ Real.log ((m : ℝ) + 2))
    (hhi : Real.log ((m : ℝ) + 2) ≤ (hi : ℝ) / scale) :
    ∃ out, Runs w p ω testInitChainDepth st .normal out 308 ∧
      (out.regs 109 = 1 → Chain.chosenD (23 / 24) m = candidate) ∧
      ((candidate - 1) ^ 48 * scale < lo → hi ≤ candidate ^ 48 * scale → out.regs 109 = 1) ∧
      out.regs 106 = candidate ^ 48 * scale ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 105 → r ≠ 106 → r ≠ 109 → out.regs r = st.regs r) := by
  obtain ⟨mid, hr₁, hp, hn, hm₁, hk₁⟩ :=
    stageInitDepthPowers_runs (p := p) (ω := ω) hc hs hcWord hsPos hw hfit
  obtain ⟨out, hr₂, hflag, hm₂, hk₂⟩ :=
    checkInitDepthBounds_runs (ω := ω) hp hn
      ((hk₁ 107 (by decide) (by decide)).trans hl)
      ((hk₁ 108 (by decide) (by decide)).trans hh) hw
  have hcert (h : out.regs 109 = 1) : Chain.chosenD (23 / 24) m = candidate := by
    split at hflag
    · rename_i hpass
      exact minRatioDepth_eq_of_scaledLogBounds m candidate lo hi scale hcPos hsPos hlo hhi hpass.1 hpass.2
    · omega
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, _, 10, hr₁, hr₂, rfl⟩),
    hcert, fun hprev hnext => hflag.trans (by simp [hprev, hnext]), (hk₂ 106 (by decide)).trans hn, hm₂.trans hm₁, fun r h105 h106 h109 => (hk₂ r h109).trans (hk₁ r h105 h106)⟩

/-- Advance only when the candidate's upper power lies below the
lower logarithm bound. -/
@[expose] def advanceInitDepthCandidate (otherwise : Stmt) : Stmt :=
  .cond (.bin .lt (.reg 106) (.reg 107))
    (.assign 110 (.bin .add (.reg 110) (.const 1))) otherwise

/-- Advancing the candidate retains a lower bound on the exact chain depth. -/
theorem advanceInitDepthCandidate_runs {w m candidate lo scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {otherwise : Stmt}
    (hc : st.regs 110 = candidate) (hn : st.regs 106 = candidate ^ 48 * scale)
    (hl : st.regs 107 = lo) (hbelow : candidate ^ 48 * scale < lo)
    (hscale : 0 < scale) (hlog : (lo : ℝ) / scale ≤ Real.log ((m : ℝ) + 2))
    (hw : 1 < 2 ^ w) (hfit : candidate + 1 < 2 ^ w) :
    ∃ out, Runs w p ω (advanceInitDepthCandidate otherwise) st .normal out 8 ∧
      out.regs 110 = candidate + 1 ∧ out.regs 110 ≤ Chain.chosenD (23 / 24) m ∧
      out.mem = st.mem ∧ (∀ r ≠ 110, out.regs r = st.regs r) := by
  have hs : (0 : ℝ) < scale := by exact_mod_cast hscale
  have hlt : (candidate : ℝ) ^ (48 : ℕ) < (lo : ℝ) / scale :=
    (lt_div_iff₀ hs).2 (by exact_mod_cast hbelow)
  have hdepth : candidate < Chain.chosenD (23 / 24) m := by
    apply Nat.lt_of_not_ge
    intro h
    exact (hlt.trans_le hlog).not_ge ((minRatioDepth_le_iff m candidate).1 h)
  let out := {st with regs := Function.update st.regs 110 (candidate + 1)}
  have hr : Runs w p ω (.assign 110 (.bin .add (.reg 110) (.const 1))) st .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hc, hw, hfit], rfl, rfl, rfl⟩
  exact ⟨out, runs_cond_iff.mpr ⟨1, 4, by simp [Expr.eval, BinOp.eval, hn, hl, hw, hbelow],
    hr, rfl⟩, by simp [out], by simpa [out] using hdepth, rfl, fun r hr => by simp [out, hr]⟩

/-- Bound the input logarithm by its binary length. -/
theorem initDepthLog_le_inputBits (m : ℕ) : Real.log ((m : ℝ) + 2) ≤ (m + 2).size := by
  let n := m + 2
  have hpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn : (n : ℝ) ≤ (2 : ℝ) ^ n.size := by
    exact_mod_cast (Nat.size_le.mp (le_refl n.size)).le
  suffices Real.log (n : ℝ) ≤ n.size by simpa [n, Nat.cast_add] using this
  calc
    Real.log (n : ℝ) ≤ Real.log ((2 : ℝ) ^ n.size) := Real.log_le_log hpos hn
    _ = (n.size : ℝ) * Real.log 2 := Real.log_pow ..
    _ ≤ n.size := by
      have htwo : Real.log 2 ≤ 1 := by simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      exact (mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg _)).trans_eq (mul_one _)

/-- The input's bit length bounds the ceiling of its logarithm raised
to either depth exponent. -/
theorem initDepth_le_inputBits (m : ℕ) (exponent : ℝ)
    (hlo : 0 ≤ exponent) (hhi : exponent ≤ 1) :
    Nat.ceil (Real.log ((m : ℝ) + 2) ^ exponent) ≤ (m + 2).size := by
  let n := m + 2
  have hsize : 1 ≤ n.size := by
    by_contra! h
    have hw : n < 2 ^ n.size := Nat.size_le.mp le_rfl
    have hz : n.size = 0 := by omega
    rw [hz] at hw
    simp [n] at hw
  have hcast : (1 : ℝ) ≤ n.size := by exact_mod_cast hsize
  have hl : Real.log (n : ℝ) ≤ n.size := by
    simpa [n, Nat.cast_add] using initDepthLog_le_inputBits m
  apply Nat.ceil_le.mpr
  suffices Real.log (n : ℝ) ^ exponent ≤ n.size by simpa [n, Nat.cast_add] using this
  calc
    _ ≤ (n.size : ℝ) ^ exponent := Real.rpow_le_rpow (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))) hl hlo
    _ ≤ (n.size : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hcast hhi
    _ = _ := Real.rpow_one _

/-- A word can hold a scaled depth power when it has room for the
working precision and the exponent times the depth's bit length. -/
theorem initDepthPower_wordFits {w depth exponent precision : ℕ}
    (he : 0 < exponent) (hw : precision + exponent * depth.size ≤ w) :
    depth ^ exponent * 2 ^ precision < 2 ^ w := by
  have hd : depth < 2 ^ depth.size := Nat.size_le.mp le_rfl
  have hpow := Nat.pow_lt_pow_left hd he.ne'
  have hp := Nat.mul_lt_mul_of_pos_right hpow (Nat.two_pow_pos precision)
  rw [← pow_mul, ← pow_add] at hp
  exact hp.trans_le (Nat.pow_le_pow_right (by decide) (by
    simpa only [Nat.add_comm, Nat.mul_comm] using hw))

/-- For positive input size, the logarithm stays a fixed distance
above the lower cutoff at depth two. -/
theorem initDepthTwo_lowerGap {m exponent : ℕ} (hm : 1 ≤ m) {error : ℝ}
    (he : error ≤ 1 / 16) :
    (((2 - 1 : ℕ) ^ exponent : ℕ) : ℝ) + error < Real.log ((m : ℝ) + 2) := by
  have hratio : Real.exp 1 / 3 - 1 < -(1 / 16 : ℝ) := by
    linarith only [Real.exp_one_lt_d9]
  have hl := Real.log_le_sub_one_of_pos (show 0 < Real.exp 1 / 3 by positivity)
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hl
  have hthree : (1 : ℝ) + 1 / 16 < Real.log 3 := by linarith only [hl, hratio]
  have hmono : Real.log 3 ≤ Real.log ((m : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 3 ≤ m + 2 by omega))
  simp only [Nat.reduceSub, one_pow, Nat.cast_one]
  exact (add_le_add_right he 1).trans_lt (hthree.trans_le hmono)

/-- A bit-length bound strictly below the upper cutoff guarantees
room for the upper endpoint at depth two. -/
theorem initDepthTwo_upperGap {m exponent : ℕ} {error : ℝ}
    (hm : (m + 2).size < 2 ^ exponent) (he : error ≤ 1) :
    Real.log ((m : ℝ) + 2) + error ≤ ((2 ^ exponent : ℕ) : ℝ) := by
  have hbits : ((m + 2).size : ℝ) + 1 ≤ ((2 ^ exponent : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hm)
  exact (add_le_add (initDepthLog_le_inputBits m) he).trans hbits

/-- Five accuracy bits suffice for both depth-two comparisons when
the input bit length fits below the upper cutoff. -/
theorem initDepthTwo_gaps_of_accuracy {m exponent accuracy : ℕ}
    (hm : 1 ≤ m) (hbits : (m + 2).size < 2 ^ exponent) (hacc : 5 ≤ accuracy) :
    let error : ℝ := 2 / (2 : ℝ) ^ accuracy
    (((2 - 1 : ℕ) ^ exponent : ℕ) : ℝ) + error < Real.log ((m : ℝ) + 2) ∧
      Real.log ((m : ℝ) + 2) + error ≤ ((2 ^ exponent : ℕ) : ℝ) := by
  dsimp only
  have hpow : (32 : ℝ) ≤ (2 : ℝ) ^ accuracy := by
    calc
      (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hacc
  have herror : 2 / (2 : ℝ) ^ accuracy ≤ 1 / 16 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hpow]
  exact ⟨initDepthTwo_lowerGap hm herror,
    initDepthTwo_upperGap hbits (herror.trans (by norm_num))⟩

/-- The chain model selects depth two in the input range covered by
the logarithm gap certificate. -/
theorem initChainDepth_eq_two_of_inputBits {m : ℕ}
    (hm : 1 ≤ m) (hbits : (m + 2).size < 2 ^ 48) :
    Chain.chosenD (23 / 24) m = 2 := by
  obtain ⟨hlo, hhi⟩ := initDepthTwo_gaps_of_accuracy hm hbits (by decide : 5 ≤ 5)
  have herror : (0 : ℝ) ≤ 2 / (2 : ℝ) ^ (5 : ℕ) := by positivity
  have hprev := (le_add_of_nonneg_right herror).trans_lt hlo
  have hnext := (le_add_of_nonneg_right herror).trans hhi
  exact minRatioDepth_eq_of_logBounds m 2 _ _ (by decide) le_rfl le_rfl
    (by simpa only [Nat.cast_pow] using hprev)
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hnext)

/-- An enclosure whose error is smaller than the lower gap and no
larger than the upper gap certifies the adjacent depth powers. -/
theorem initDepth_separation_of_error {depth exponent lo hi scale : ℕ} {value error : ℝ}
    (hs : 0 < scale)
    (hlo : value - error ≤ (lo : ℝ) / scale)
    (hhi : (hi : ℝ) / scale ≤ value + error)
    (hprev : (((depth - 1) ^ exponent : ℕ) : ℝ) + error < value)
    (hnext : value + error ≤ ((depth ^ exponent : ℕ) : ℝ)) :
    (depth - 1) ^ exponent * scale < lo ∧ hi ≤ depth ^ exponent * scale := by
  have hs' : (0 : ℝ) < scale := by exact_mod_cast hs
  have hp : (((depth - 1) ^ exponent : ℕ) : ℝ) < (lo : ℝ) / scale := by
    linarith only [hlo, hprev]
  exact ⟨by exact_mod_cast (lt_div_iff₀ hs').mp hp,
    by exact_mod_cast (div_le_iff₀ hs').mp (hhi.trans hnext)⟩

/-- Under the depth-two gap bounds, the computed endpoint words
pass the same comparisons as the general runtime selector. -/
theorem initDepthTwo_separation_of_accuracy {m exponent accuracy lo hi scale : ℕ}
    (hm : 1 ≤ m) (hbits : (m + 2).size < 2 ^ exponent) (hacc : 5 ≤ accuracy)
    (hs : 0 < scale)
    (hlo : Real.log ((m : ℝ) + 2) - 2 / (2 : ℝ) ^ accuracy ≤ (lo : ℝ) / scale)
    (hhi : (hi : ℝ) / scale ≤ Real.log ((m : ℝ) + 2) + 2 / (2 : ℝ) ^ accuracy) :
    scale < lo ∧ hi ≤ 2 ^ exponent * scale := by
  obtain ⟨hprev, hnext⟩ := initDepthTwo_gaps_of_accuracy hm hbits hacc
  simpa only [Nat.reduceSub, one_pow, one_mul] using
    initDepth_separation_of_error (depth := 2) hs hlo hhi hprev hnext

/-- Once the logarithm enclosure separates the powers adjacent to the
model depth, every smaller candidate can advance using the same enclosure. -/
theorem initChainDepth_advance_of_separation {m candidate lo scale : ℕ}
    (hc : candidate < Chain.chosenD (23 / 24) m)
    (hgap : (Chain.chosenD (23 / 24) m - 1) ^ 48 * scale < lo) :
    candidate ^ 48 * scale < lo := by
  have hprev : candidate ≤ Chain.chosenD (23 / 24) m - 1 := by omega
  exact (Nat.mul_le_mul_right scale (Nat.pow_le_pow_left hprev _)).trans_lt hgap

/-- Test one candidate and advance when its power is below the lower
bound. The other continuation can use the certification flag. -/
@[expose] def stepInitChainDepth (otherwise : Stmt) : Stmt :=
  testInitChainDepth ;; advanceInitDepthCandidate otherwise

/-- Every candidate below the exact depth advances in one step when
the current enclosure separates the neighboring powers. -/
theorem stepInitChainDepth_advance_runs {w m candidate lo hi scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {otherwise : Stmt}
    (hc : st.regs 110 = candidate) (hs : st.regs 111 = scale)
    (hl : st.regs 107 = lo) (hh : st.regs 108 = hi)
    (hcPos : 0 < candidate) (hcLt : candidate < Chain.chosenD (23 / 24) m)
    (hsPos : 0 < scale) (hw : 1 < 2 ^ w) (hfit : candidate ^ 48 * scale < 2 ^ w)
    (hnext : candidate + 1 < 2 ^ w)
    (hlo : (lo : ℝ) / scale ≤ Real.log ((m : ℝ) + 2))
    (hhi : Real.log ((m : ℝ) + 2) ≤ (hi : ℝ) / scale)
    (hgap : (Chain.chosenD (23 / 24) m - 1) ^ 48 * scale < lo) :
    ∃ out, Runs w p ω (stepInitChainDepth otherwise) st .normal out 317 ∧
      out.regs 110 = candidate + 1 ∧ out.regs 110 ≤ Chain.chosenD (23 / 24) m ∧
      out.mem = st.mem := by
  obtain ⟨mid, hr₁, _, _, hp, hm₁, hk₁⟩ :=
    testInitChainDepth_runs (p := p) (ω := ω) hc hs hl hh hcPos (by omega) hsPos hw hfit hlo hhi
  obtain ⟨out, hr₂, hc', hd, hm₂, _⟩ :=
    advanceInitDepthCandidate_runs (ω := ω) (otherwise := otherwise)
      ((hk₁ 110 (by decide) (by decide) (by decide)).trans hc) hp
      ((hk₁ 107 (by decide) (by decide) (by decide)).trans hl)
      (initChainDepth_advance_of_separation hcLt hgap) hsPos hlo hw hnext
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 308, 8, hr₁, hr₂, rfl⟩),
    hc', hd, hm₂.trans hm₁⟩

/-- Test the final candidate and choose its branch count. -/
@[expose] def finishInitChainDepth (entry mReg : ℕ) (retry : Stmt) : Stmt :=
  testInitChainDepth ;; initMinRatioCertifiedDimensions entry mReg retry

/-- A separating enclosure for the exact candidate installs the chain
depth and its corresponding number of branches. -/
theorem finishInitChainDepth_runs {w entry mReg m depth lo hi scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (himpl : MeetsContract w p entry (minRatioBranchCountContract w))
    (hc : st.regs 110 = depth) (hs : st.regs 111 = scale)
    (hl : st.regs 107 = lo) (hh : st.regs 108 = hi)
    (hm : st.regs mReg = m)
    (hmReg : mReg ≠ 75) (h105 : mReg ≠ 105) (h106 : mReg ≠ 106) (h109 : mReg ≠ 109)
    (hd : depth = Chain.chosenD (23 / 24) m)
    (hdPos : 0 < depth) (hmPos : 1 ≤ m) (hsPos : 0 < scale)
    (hw : 2 < 2 ^ w) (hmWord : m < 2 ^ w) (hdWord : depth < 2 ^ w)
    (hfit : depth ^ 48 * scale < 2 ^ w)
    (hlo : (lo : ℝ) / scale ≤ Real.log ((m : ℝ) + 2))
    (hhi : Real.log ((m : ℝ) + 2) ≤ (hi : ℝ) / scale)
    (hprev : (depth - 1) ^ 48 * scale < lo) (hnext : hi ≤ depth ^ 48 * scale) :
    ∃ out cost, Runs w p ω (finishInitChainDepth entry mReg retry) st .normal out cost ∧
      out.regs 75 = Chain.chosenD (23 / 24) m ∧
      out.regs 76 = (Chain.mkChainParams depth m hdPos hmPos).k ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 75 → r ≠ 76 → r ≠ 105 → r ≠ 106 → r ≠ 109 → out.regs r = st.regs r) ∧
      cost ≤ (19 * depth + 32) * m.size + 336 := by
  obtain ⟨mid, hr₁, _, hcert, _, hm₁, hk₁⟩ :=
    testInitChainDepth_runs (p := p) (ω := ω) hc hs hl hh hdPos hdWord hsPos (by omega) hfit hlo hhi
  obtain ⟨out, cost, hr₂, hdepth, hbranches, hk₂, hm₂, hcost⟩ :=
    initMinRatioCertifiedDimensions_runs (ω := ω) (retry := retry) himpl (hcert hprev hnext)
      ((hk₁ 110 (by decide) (by decide) (by decide)).trans hc)
      hmReg ((hk₁ mReg h105 h106 h109).trans hm) hd hdPos hmPos hw hdWord hmWord
  exact ⟨out, 308 + cost + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 308, cost, hr₁, hr₂, rfl⟩),
    hdepth, hbranches, hm₂.trans hm₁,
    fun r h75 h76 h105 h106 h109 => (hk₂ r h75 h76).trans (hk₁ r h105 h106 h109), by omega⟩

/-- Scan candidates while their scaled powers are below the lower
logarithm bound. The last candidate is checked against both bounds separately. -/
@[expose] def scanInitDepth (exponent : ℕ) : Stmt :=
  .loop (.bin .lt (.reg 106) (.reg 107))
    (advanceInitDepthCandidate .nop ;; stageInitDepthPowers exponent)

/-- When the enclosure separates the exact depth, the scan reaches it
in one iteration for each smaller candidate. -/
theorem scanInitDepth_runs {exponent w candidate depth lo scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hc : st.regs 110 = candidate) (hp : st.regs 106 = candidate ^ exponent * scale)
    (hl : st.regs 107 = lo) (hs : st.regs 111 = scale)
    (hle : candidate ≤ depth) (hdw : depth < 2 ^ w) (hw : 1 < 2 ^ w)
    (hsPos : 0 < scale) (hfit : depth ^ exponent * scale < 2 ^ w)
    (hgap : (depth - 1) ^ exponent * scale < lo) (hstop : lo ≤ depth ^ exponent * scale) :
    ∃ out, Runs w p ω (scanInitDepth exponent) st .normal out ((6 * exponent + 22) * (depth - candidate) + 4) ∧
      out.regs 110 = depth ∧ out.mem = st.mem ∧ out.regs 107 = lo ∧ out.regs 111 = scale ∧
      (∀ r, r ≠ 105 → r ≠ 106 → r ≠ 110 → out.regs r = st.regs r) := by
  induction hrem : depth - candidate generalizing candidate st with
  | zero =>
    have he : candidate = depth := by omega
    have hcond : Expr.eval w st (.bin .lt (.reg 106) (.reg 107)) = some 0 := by
      simp [Expr.eval, BinOp.eval, hp, hl, he, Nat.not_lt.mpr hstop]
    exact ⟨st, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, by simp [Expr.size_bin, Expr.size_reg]⟩), by omega, rfl, hl, hs, fun _ _ _ _ => rfl⟩
  | succ remaining ih =>
    have hbelow : candidate ^ exponent * scale < lo :=
      (Nat.mul_le_mul_right scale (Nat.pow_le_pow_left (by omega : candidate ≤ depth - 1) _)).trans_lt hgap
    have hnext : candidate + 1 < 2 ^ w := by omega
    have hcond : Expr.eval w st (.bin .lt (.reg 106) (.reg 107)) = some 1 := by
      simp [Expr.eval, BinOp.eval, hp, hl, hbelow, hw]
    let mid := {st with regs := Function.update st.regs 110 (candidate + 1)}
    have ha : Runs w p ω (.assign 110 (.bin .add (.reg 110) (.const 1))) st .normal mid 4 :=
      runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hc, hw, hnext], rfl, rfl, rfl⟩
    have hb : Runs w p ω (advanceInitDepthCandidate .nop) st .normal mid 8 :=
      runs_cond_iff.mpr ⟨1, 4, hcond, ha, rfl⟩
    have hf : (candidate + 1) ^ exponent * scale < 2 ^ w :=
      (Nat.mul_le_mul_right scale (Nat.pow_le_pow_left (by omega : candidate + 1 ≤ depth) _)).trans_lt hfit
    obtain ⟨next, hr, _, hn, hm, hk⟩ :=
      stageInitDepthPowers_runs (p := p) (ω := ω) (st := mid)
        (by simp [mid]) (by simpa [mid] using hs) hnext hsPos hw hf
    have hbody : Runs w p ω (advanceInitDepthCandidate .nop ;; stageInitDepthPowers exponent)
        st .normal next (6 * exponent + 18) :=
      runs_seq_iff.mpr (Or.inr ⟨mid, 8, 6 * exponent + 9, hb, hr, by omega⟩)
    obtain ⟨out, ho, hd, hmem, hlo, hscale, hkeep⟩ :=
      ih ((hk 110 (by decide) (by decide)).trans (by simp [mid])) hn
        ((hk 107 (by decide) (by decide)).trans (by simpa [mid] using hl))
        ((hk 111 (by decide) (by decide)).trans (by simpa [mid] using hs))
        (by omega) (by omega)
    refine ⟨out, runs_loop_iff.mpr (Or.inr (Or.inr
      ⟨1, next, 6 * exponent + 18, _, hcond, by decide, hbody, ho, ?_⟩)), hd, hmem.trans hm, hlo, hscale, ?_⟩
    · simp [Expr.size_bin, Expr.size_reg]
      simp [Nat.mul_succ]
      omega
    · intro r h105 h106 h110
      exact (hkeep r h105 h106 h110).trans ((hk r h105 h106).trans (by simp [mid, h110]))

/-- Begin the depth scan at one, whose scaled power is the scale itself. -/
@[expose] def searchInitDepth (exponent : ℕ) : Stmt :=
  .assign 110 (.const 1) ;; .assign 106 (.reg 111) ;; scanInitDepth exponent

/-- The search reaches the exact candidate when the two neighboring
powers are separated by the enclosure. -/
theorem searchInitDepth_runs {exponent w depth lo scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hl : st.regs 107 = lo) (hs : st.regs 111 = scale)
    (hd : 1 ≤ depth) (hdw : depth < 2 ^ w) (hw : 1 < 2 ^ w)
    (hsPos : 0 < scale) (hfit : depth ^ exponent * scale < 2 ^ w)
    (hgap : (depth - 1) ^ exponent * scale < lo) (hstop : lo ≤ depth ^ exponent * scale) :
    ∃ out, Runs w p ω (searchInitDepth exponent) st .normal out ((6 * exponent + 22) * (depth - 1) + 10) ∧
      out.regs 110 = depth ∧ out.mem = st.mem ∧ out.regs 107 = lo ∧ out.regs 111 = scale ∧
      (∀ r, r ≠ 105 → r ≠ 106 → r ≠ 110 → out.regs r = st.regs r) := by
  let mid := {st with regs := Function.update st.regs 110 1}
  let start := {mid with regs := Function.update mid.regs 106 scale}
  have h₁ : Runs w p ω (.assign 110 (.const 1)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hw], rfl, rfl, rfl⟩
  have h₂ : Runs w p ω (.assign 106 (.reg 111)) mid .normal start 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, mid, hs], rfl, rfl, rfl⟩
  obtain ⟨out, hr, hc, hm, hlo, hscale, hkeep⟩ :=
    scanInitDepth_runs (p := p) (ω := ω) (st := start) (candidate := 1)
      (by simp [start, mid]) (by simp [start]) (by simp [start, mid, hl])
      (by simp [start, mid, hs]) hd hdw hw hsPos hfit hgap hstop
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, _, h₁,
    runs_seq_iff.mpr (Or.inr ⟨start, 2, _, h₂, hr, rfl⟩), by omega⟩), hc, hm, hlo, hscale,
    fun r h105 h106 h110 => (hkeep r h105 h106 h110).trans (by simp [start, mid, h106, h110])⟩

/-- The same scan finds the model depth from a multiword enclosure after
rounding its lower endpoint upward. Only the integer cutoff powers
and the rounded endpoint need to fit in a word. -/
theorem searchInitDepth_rounded_runs {exponent w depth lo scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hl : st.regs 107 = lo / scale + (if lo % scale = 0 then 0 else 1))
    (hs : st.regs 111 = 1)
    (hd : 1 ≤ depth) (hdw : depth < 2 ^ w) (hw : 1 < 2 ^ w) (hsPos : 0 < scale)
    (hfit : depth ^ exponent < 2 ^ w)
    (hgap : (depth - 1) ^ exponent * scale < lo) (hstop : lo ≤ depth ^ exponent * scale) :
    ∃ out, Runs w p ω (searchInitDepth exponent) st .normal out ((6 * exponent + 22) * (depth - 1) + 10) ∧
      out.regs 110 = depth ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 105 → r ≠ 106 → r ≠ 110 → out.regs r = st.regs r) := by
  have hlo := (initDepth_endpoint_le_iff hsPos).mpr hstop
  have hprev := Nat.lt_of_not_ge (fun h =>
    hgap.not_ge ((initDepth_endpoint_le_iff hsPos).mp h))
  obtain ⟨out, hr, hd', hm, _, _, hf⟩ := searchInitDepth_runs hl hs hd hdw hw
    (by decide) (by simpa only [mul_one] using hfit)
    (by simpa only [mul_one] using hprev) (by simpa only [mul_one] using hlo)
  exact ⟨out, hr, hd', hm, hf⟩

/-- Search the runtime depth candidates, then select the branch count. -/
@[expose] def selectInitChainDimensions (entry mReg : ℕ) (retry : Stmt) : Stmt :=
  searchInitDepth 48 ;; finishInitChainDepth entry mReg retry

/-- Given a separating enclosure, the search and branch selection
compute the chain dimensions without a word-size cutoff. -/
theorem selectInitChainDimensions_runs {w entry mReg m depth lo hi scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (himpl : MeetsContract w p entry (minRatioBranchCountContract w))
    (hs : st.regs 111 = scale)
    (hl : st.regs 107 = lo) (hh : st.regs 108 = hi)
    (hm : st.regs mReg = m)
    (hmReg : mReg ≠ 75) (h105 : mReg ≠ 105) (h106 : mReg ≠ 106) (h109 : mReg ≠ 109) (h110 : mReg ≠ 110)
    (hd : depth = Chain.chosenD (23 / 24) m)
    (hdPos : 0 < depth) (hmPos : 1 ≤ m) (hsPos : 0 < scale)
    (hw : 2 < 2 ^ w) (hmWord : m < 2 ^ w) (hdWord : depth < 2 ^ w)
    (hfit : depth ^ 48 * scale < 2 ^ w)
    (hlo : (lo : ℝ) / scale ≤ Real.log ((m : ℝ) + 2))
    (hhi : Real.log ((m : ℝ) + 2) ≤ (hi : ℝ) / scale)
    (hprev : (depth - 1) ^ 48 * scale < lo) (hnext : hi ≤ depth ^ 48 * scale) :
    ∃ out cost, Runs w p ω (selectInitChainDimensions entry mReg retry) st .normal out cost ∧
      out.regs 75 = Chain.chosenD (23 / 24) m ∧
      out.regs 76 = (Chain.mkChainParams depth m hdPos hmPos).k ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 75 → r ≠ 76 → r ≠ 105 → r ≠ 106 → r ≠ 109 → r ≠ 110 → out.regs r = st.regs r) ∧
      cost ≤ (19 * depth + 32) * m.size + 310 * (depth - 1) + 347 := by
  have hstop : lo ≤ depth ^ 48 * scale := by
    have hs' : (0 : ℝ) < scale := by exact_mod_cast hsPos
    have hord := (div_le_div_iff_of_pos_right hs').mp (hlo.trans hhi)
    exact (by exact_mod_cast hord : lo ≤ hi).trans hnext
  obtain ⟨mid, hr₁, hc, hm₁, hl', hs', hf⟩ :=
    searchInitDepth_runs (exponent := 48) (p := p) (ω := ω) hl hs hdPos hdWord (by omega) hsPos hfit hprev hstop
  obtain ⟨out, cost, hr₂, hdepth, hbranches, hm₂, hk₂, hcost⟩ :=
    finishInitChainDepth_runs (ω := ω) (retry := retry) himpl hc hs' hl'
      ((hf 108 (by decide) (by decide) (by decide)).trans hh)
      ((hf mReg h105 h106 h110).trans hm) hmReg h105 h106 h109
      hd hdPos hmPos hsPos hw hmWord hdWord hfit hlo hhi hprev hnext
  exact ⟨out, _, runs_seq_iff.mpr (Or.inr ⟨mid, _, cost, hr₁, hr₂, rfl⟩),
    hdepth, hbranches, hm₂.trans hm₁,
    fun r h75 h76 h105 h106 h109 h110 => (hk₂ r h75 h76 h105 h106 h109).trans (hf r h105 h106 h110), by omega⟩

/-- The adjacent integer comparisons suffice to install an already
identified model depth. -/
theorem selectInitChainDimensions_of_order_runs {w entry mReg m depth lo hi scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (himpl : MeetsContract w p entry (minRatioBranchCountContract w))
    (hs : st.regs 111 = scale)
    (hl : st.regs 107 = lo)
    (hh : st.regs 108 = hi)
    (hm : st.regs mReg = m)
    (hmReg : mReg ≠ 75) (h105 : mReg ≠ 105) (h106 : mReg ≠ 106) (h109 : mReg ≠ 109)
    (h110 : mReg ≠ 110) (hd : depth = Chain.chosenD (23 / 24) m)
    (hdPos : 0 < depth) (hmPos : 1 ≤ m) (hsPos : 0 < scale)
    (hw : 2 < 2 ^ w) (hmWord : m < 2 ^ w) (hdWord : depth < 2 ^ w)
    (hfit : depth ^ 48 * scale < 2 ^ w) (horder : lo ≤ hi)
    (hprev : (depth - 1) ^ 48 * scale < lo) (hnext : hi ≤ depth ^ 48 * scale) :
    ∃ out cost, Runs w p ω (selectInitChainDimensions entry mReg retry) st .normal out cost ∧
      out.regs 75 = Chain.chosenD (23 / 24) m ∧
      out.regs 76 = (Chain.mkChainParams depth m hdPos hmPos).k ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 75 → r ≠ 76 → r ≠ 105 → r ≠ 106 → r ≠ 109 → r ≠ 110 → out.regs r = st.regs r) ∧
      cost ≤ (19 * depth + 32) * m.size + 310 * (depth - 1) + 347 := by
  obtain ⟨mid, hr₁, hc, hm₁, _, _, hf₁⟩ :=
    searchInitDepth_runs (exponent := 48) hl hs hdPos hdWord (by omega) hsPos hfit
      hprev (horder.trans hnext)
  obtain ⟨powers, hr₂, hp, hn, hm₂, hf₂⟩ :=
    stageInitDepthPowers_runs (p := p) (ω := ω) hc
      ((hf₁ 111 (by decide) (by decide) (by decide)).trans hs)
      hdWord hsPos (by omega) hfit
  have keep r (a : r ≠ 105) (b : r ≠ 106) (c : r ≠ 110) :=
    (hf₂ r a b).trans (hf₁ r a b c)
  obtain ⟨checked, hr₃, hflag, hm₃, hf₃⟩ := checkInitDepthBounds_runs (w := w) (p := p) (ω := ω) hp hn
    ((keep 107 (by decide) (by decide) (by decide)).trans hl)
    ((keep 108 (by decide) (by decide) (by decide)).trans hh) (by omega)
  have hcert : checked.regs 109 = 1 := hflag.trans (by simp [hprev, hnext])
  obtain ⟨out, cost, hr₄, hd', hk, hf₄, hm₄, hcost⟩ :=
    initMinRatioCertifiedDimensions_runs (ω := ω) (retry := retry) himpl hcert
      ((hf₃ 110 (by decide)).trans ((hf₂ 110 (by decide) (by decide)).trans hc))
      hmReg ((hf₃ mReg h109).trans ((keep mReg h105 h106 h110).trans hm))
      hd hdPos hmPos hw hdWord hmWord
  have htest : Runs w p ω testInitChainDepth mid .normal checked 308 :=
    runs_seq_iff.mpr (Or.inr ⟨powers, _, _, hr₂, hr₃, rfl⟩)
  refine ⟨out, _, runs_seq_iff.mpr (Or.inr ⟨mid, _, _, hr₁,
    runs_seq_iff.mpr (Or.inr ⟨checked, 308, cost, htest, hr₄, rfl⟩), rfl⟩),
    hd', hk, hm₄.trans (hm₃.trans (hm₂.trans hm₁)), ?_, by omega⟩
  intro r h75 h76 h105 h106 h109 h110
  exact (hf₄ r h75 h76).trans ((hf₃ r h109).trans (keep r h105 h106 h110))

/-- The chain selector also works with rounded endpoints and unit scale.
Its final check still uses the upper endpoint before installing the
model depth and branch count. -/
theorem selectInitChainDimensions_rounded_runs {w entry mReg m depth lo hi scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {retry : Stmt}
    (himpl : MeetsContract w p entry (minRatioBranchCountContract w))
    (hs : st.regs 111 = 1)
    (hl : st.regs 107 = lo / scale + (if lo % scale = 0 then 0 else 1))
    (hh : st.regs 108 = hi / scale + (if hi % scale = 0 then 0 else 1))
    (hm : st.regs mReg = m)
    (hmReg : mReg ≠ 75) (h105 : mReg ≠ 105) (h106 : mReg ≠ 106) (h109 : mReg ≠ 109)
    (h110 : mReg ≠ 110) (hd : depth = Chain.chosenD (23 / 24) m)
    (hdPos : 0 < depth) (hmPos : 1 ≤ m) (hsPos : 0 < scale)
    (hw : 2 < 2 ^ w) (hmWord : m < 2 ^ w) (hdWord : depth < 2 ^ w)
    (hfit : depth ^ 48 < 2 ^ w) (horder : lo ≤ hi)
    (hprev : (depth - 1) ^ 48 * scale < lo) (hnext : hi ≤ depth ^ 48 * scale) :
    ∃ out cost, Runs w p ω (selectInitChainDimensions entry mReg retry) st .normal out cost ∧
      out.regs 75 = Chain.chosenD (23 / 24) m ∧
      out.regs 76 = (Chain.mkChainParams depth m hdPos hmPos).k ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 75 → r ≠ 76 → r ≠ 105 → r ≠ 106 → r ≠ 109 → r ≠ 110 → out.regs r = st.regs r) ∧
      cost ≤ (19 * depth + 32) * m.size + 310 * (depth - 1) + 347 := by
  have hord := (initDepth_endpoint_le_iff hsPos).mpr
    (horder.trans ((initDepth_endpoint_le_iff hsPos).mp le_rfl))
  have hlo : (depth - 1) ^ 48 < lo / scale + (if lo % scale = 0 then 0 else 1) :=
    Nat.lt_of_not_ge fun h => hprev.not_ge ((initDepth_endpoint_le_iff hsPos).mp h)
  have hhi := (initDepth_endpoint_le_iff hsPos).mpr hnext
  exact selectInitChainDimensions_of_order_runs himpl hs hl hh hm hmReg h105 h106 h109 h110
    hd hdPos hmPos (by decide) hw hmWord hdWord (by simpa only [mul_one] using hfit)
    hord (by simpa only [mul_one] using hlo) (by simpa only [mul_one] using hhi)

end MinCostFlow.MinRatio
