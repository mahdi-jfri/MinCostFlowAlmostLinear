module

public import MinCostFlow.MinRatio.InitSparsifierLength
public import MinCostFlow.Num.PositiveExponential
public import MinCostFlow.Num.ShiftRight
import MinCostFlow.Num.PositiveExponentialFacts

/-!
# Runtime exponentiation for the sparsifier path bound

Evaluate the lower and upper exponents at the squared scale and round
their results outward at the caller's working scale.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Take an integer bound on the upper exponent before calling the
positive exponential procedure. -/
@[expose] def setInitSparsifierExpRange : Stmt :=
  .assign 97 (.bin .add (.bin .div (.reg 32) (.reg 33)) (.const 1))

/-- The bound contains the upper exponent at the squared scale. -/
theorem setInitSparsifierExpRange_runs {w numerator denominator : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hn : st.regs 32 = numerator) (hd : st.regs 33 = denominator)
    (hpos : 0 < denominator) (hw : numerator + 1 < 2 ^ w) :
    ∃ out, Runs w p ω setInitSparsifierExpRange st .normal out 6 ∧
      out.regs 97 = numerator / denominator + 1 ∧
      (numerator : ℝ) / denominator ≤ (out.regs 97 : ℝ) ∧ out.mem = st.mem ∧
      (∀ r ≠ 97, out.regs r = st.regs r) := by
  let bound := numerator / denominator + 1
  let out := {st with regs := Function.update st.regs 97 bound}
  have hq := Nat.div_le_self numerator denominator
  have hb : bound < 2 ^ w := (Nat.add_le_add_right hq _).trans_lt hw
  have hqFit : numerator / denominator < 2 ^ w := by omega
  have hr : Runs w p ω setInitSparsifierExpRange st .normal out 6 :=
    runs_assign_iff.mpr ⟨_, by
      simp [bound, Expr.eval, BinOp.eval, hn, hd, hqFit,
        show 1 < 2 ^ w by omega, show numerator / denominator + 1 < 2 ^ w from hb],
      rfl, rfl, rfl⟩
  have hden : (0 : ℝ) < denominator := by exact_mod_cast hpos
  have hlt : numerator < bound * denominator :=
    (Nat.div_lt_iff_lt_mul hpos).mp (Nat.lt_succ_self _)
  refine ⟨out, hr, by simp [out, bound], ?_, rfl, fun r h => by simp [out, h]⟩
  have hreg : out.regs 97 = bound := by simp [out]
  rw [hreg]
  exact ((div_lt_iff₀ hden).mpr (by exact_mod_cast hlt)).le

/-- Call the positive exponential with the runtime argument layout used for
the two path exponent endpoints. -/
@[expose] def approximateInitSparsifierExp (entry : ℕ) : Stmt :=
  .call 99 entry [.reg 95, .reg 96, .reg 67, .reg 68, .reg 97, .reg 98]

/-- The call preserves the caller's registers and returns a lower
approximation with the shared relative error bound. -/
theorem approximateInitSparsifierExp_runs
    {w h entry x one limbs precision range heap accuracy : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {value : ℝ}
    (himpl : MeetsContract w p entry (Num.positiveExponentialContract w h accuracy))
    (hx : st.regs 95 = x) (hone : st.regs 96 = one) (hL : st.regs 67 = limbs)
    (hP : st.regs 68 = precision) (hB : st.regs 97 = range) (hh : st.regs 98 = heap)
    (hwords : ∀ a ∈ [x, one, limbs, precision, range, heap], a < 2 ^ w)
    (hpre : (Num.positiveExponentialContract w h accuracy).pre
      [x, one, limbs, precision, range, heap] st.mem)
    (hvalue : Num.fixVal st.mem x h limbs precision = value) :
    ∃ out c ret, Runs w p ω (approximateInitSparsifierExp entry) st .normal out c ∧
      out.regs 99 = ret ∧ ret = heap + Num.positiveExponentialSpace limbs precision range ∧
      Num.Valid out.mem (ret - limbs) h limbs ∧
      1 ≤ Num.fixVal out.mem (ret - limbs) h limbs precision ∧
      Num.fixVal out.mem (ret - limbs) h limbs precision ≤ Real.exp value ∧
      |Num.fixVal out.mem (ret - limbs) h limbs precision - Real.exp value| ≤
        (1 / (2 : ℝ) ^ accuracy) * Real.exp value ∧
      (∀ r ≠ 99, out.regs r = st.regs r) ∧ (∀ a < heap, out.mem a = st.mem a) ∧
      ZeroFrom out.mem ret ∧ c ≤ Num.positiveExponentialCost limbs precision range + 7 := by
  have hargs : evalArgs w st [.reg 95, .reg 96, .reg 67, .reg 68, .reg 97, .reg 98] =
      some [x, one, limbs, precision, range, heap] :=
    by simp [evalArgs, Expr.eval, hx, hone, hL, hP, hB, hh]
  obtain ⟨out, c, ret, hr, hp, hret, hk, hc⟩ :=
    runs_call_of_meetsContract (r := 99) himpl hargs hwords hpre ω
  obtain ⟨he, _, _, hf, hz, hv, hlo, hhi, herr⟩ := hp
  change ret = heap + Num.positiveExponentialSpace limbs precision range at he
  let top := heap + Num.positiveExponentialSpace limbs precision range
  change Num.fixVal out.mem (top - limbs) h limbs precision ≤
    Real.exp (Num.fixVal st.mem x h limbs precision) at hhi
  change |Num.fixVal out.mem (top - limbs) h limbs precision -
    Real.exp (Num.fixVal st.mem x h limbs precision)| ≤
      (1 / (2 : ℝ) ^ accuracy) * Real.exp (Num.fixVal st.mem x h limbs precision) at herr
  rw [hvalue] at hhi herr
  change c ≤ 6 + Num.positiveExponentialCost limbs precision range + 1 at hc
  exact ⟨out, c, ret, hr, hret, he, he.symm ▸ hv, he.symm ▸ hlo,
    he.symm ▸ hhi, he.symm ▸ herr, hk, hf, hz, by omega⟩

/-- Allocate the fixed-point inputs and exponentiate a nonnegative path exponent
endpoint. The caller supplies the runtime range in register 97. -/
@[expose] def evaluateInitSparsifierExpEndpoint (load exp endpoint : ℕ) : Stmt :=
  setInitLogInputPointers ;;
  encodeInitBucketSigmaLogInputs load endpoint ;;
  approximateInitSparsifierExp exp

/-- The result block approximates the exponential of the represented path
exponent, with cost and allocation charged to its runtime format. -/
theorem evaluateInitSparsifierExpEndpoint_runs
    {w h load exp endpoint numerator precision limbs heap range accuracy : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hexp : MeetsContract w p exp (Num.positiveExponentialContract w h accuracy))
    (hn : st.regs endpoint = numerator) (hs : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision)
    (hh : st.regs 98 = heap) (hE : st.regs 97 = range)
    (h95 : endpoint ≠ 95) (h96 : endpoint ≠ 96)
    (hw : numerator < 2 ^ w) (hsw : 2 ^ precision < 2 ^ w)
    (hfit : 2 * numerator < Num.capacity h limbs)
    (hsfit : 2 * 2 ^ precision < Num.capacity h limbs)
    (hroom : heap + limbs + limbs + Num.positiveExponentialSpace limbs precision range < 2 ^ w)
    (hz : ZeroFrom st.mem heap)
    (hdiv : h ∣ precision) (hacc : accuracy + range + 10 ≤ precision)
    (hcap : precision + 2 * range + 4 ≤ h * limbs) (hprec : 2 * precision + 9 < 2 ^ w)
    (hhi : (numerator : ℝ) / (2 : ℝ) ^ precision ≤ range) :
    ∃ out c ret, Runs w p ω (evaluateInitSparsifierExpEndpoint load exp endpoint) st .normal out c ∧
      out.regs 99 = ret ∧ heap + limbs + limbs ≤ ret ∧
      ret = heap + limbs + limbs + Num.positiveExponentialSpace limbs precision range ∧
      Num.Valid out.mem (ret - limbs) h limbs ∧
      1 ≤ Num.fixVal out.mem (ret - limbs) h limbs precision ∧
      Num.fixVal out.mem (ret - limbs) h limbs precision ≤
        Real.exp ((numerator : ℝ) / (2 : ℝ) ^ precision) ∧
      |Num.fixVal out.mem (ret - limbs) h limbs precision -
        Real.exp ((numerator : ℝ) / (2 : ℝ) ^ precision)| ≤
        (1 / (2 : ℝ) ^ accuracy) * Real.exp ((numerator : ℝ) / (2 : ℝ) ^ precision) ∧
      (∀ r, r ≠ 95 → r ≠ 96 → r ≠ 98 → r ≠ 99 → out.regs r = st.regs r) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      c ≤ 46 * limbs + Num.positiveExponentialCost limbs precision range + 37 := by
  obtain ⟨s₁, hr₁, ha, hone, hk₁, hm₁, _⟩ :=
    setInitLogInputPointers_runs (w := w) (p := p) (ω := ω) hh hL (by omega)
  obtain ⟨s₂, c₂, hr₂, hh₂, hv, hval, hvOne, hOne, hk₂, hf₂, hz₂, hc₂⟩ :=
    encodeInitBucketSigmaLogInputs_runs (ω := ω) hload ((hk₁ endpoint h95 h96).trans hn)
      ((hk₁ 4 (by decide) (by decide)).trans hs) ((hk₁ 67 (by decide) (by decide)).trans hL)
      ((hk₁ 98 (by decide) (by decide)).trans hh) hw hsw hfit hsfit (by omega) (hm₁.symm ▸ hz)
  have hk (r : ℕ) (h98 : r ≠ 98) (h95 : r ≠ 95) (h96 : r ≠ 96) :
      s₂.regs r = st.regs r := (hk₂ r h98).trans (hk₁ r h95 h96)
  let scratch := heap + limbs + limbs
  have hnonneg : 0 ≤ Num.intVal s₂.mem heap h limbs := by
    have hvnonneg : 0 ≤ Num.fixVal s₂.mem heap h limbs precision :=
      hval.symm ▸ div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)
    rw [Num.fixVal, le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _), zero_mul] at hvnonneg
    exact_mod_cast hvnonneg
  have hpre : (Num.positiveExponentialContract w h accuracy).pre
      [heap, heap + limbs, limbs, precision, range, scratch] s₂.mem := by
    refine ⟨⟨heap, heap + limbs, limbs, precision, range, scratch, rfl, hdiv, hacc,
      hcap, hprec, by omega, le_rfl, hv, hvOne, hOne, hnonneg, hval.symm ▸ hhi⟩, hz₂, hroom⟩
  have hwords : ∀ v ∈ [heap, heap + limbs, limbs, precision, range, scratch], v < 2 ^ w := by
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp [scratch] at * <;> omega
  obtain ⟨out, c₃, ret, hr₃, hret, hretEq, hvout, hlo, hupper, herr, hk₃, hf₃, hz₃, hc₃⟩ :=
    approximateInitSparsifierExp_runs (ω := ω) hexp
      ((hk₂ 95 (by decide)).trans ha) ((hk₂ 96 (by decide)).trans hone)
      ((hk 67 (by decide) (by decide) (by decide)).trans hL)
      ((hk 68 (by decide) (by decide) (by decide)).trans hP)
      ((hk 97 (by decide) (by decide) (by decide)).trans hE) hh₂ hwords hpre hval
  refine ⟨out, 7 + (c₂ + c₃ + 1) + 1, ret, ?_, hret, by omega, hretEq, hvout, hlo, hupper, herr,
    fun r h95 h96 h98 h99 => (hk₃ r h99).trans (hk r h98 h95 h96),
    fun a ha => (hf₃ a (by omega)).trans ((hf₂ a ha).trans (congrFun hm₁ a)), hz₃, by omega⟩
  exact runs_seq_iff.mpr (Or.inr ⟨s₁, 7, _, hr₁,
    runs_seq_iff.mpr (Or.inr ⟨s₂, c₂, c₃, hr₂, hr₃, rfl⟩), rfl⟩)

/-- At the working precision, the positive exponential's relative error
fits in one unit if the accuracy includes the range allowance. -/
theorem initSparsifierExpEndpoint_bounds {value approx : ℝ}
    {range accuracy workingPrecision : ℕ}
    (hrange : value ≤ range)
    (haccuracy : workingPrecision + 2 * range ≤ accuracy)
    (hlower : approx ≤ Real.exp value)
    (herror : |approx - Real.exp value| ≤
      (1 / (2 : ℝ) ^ accuracy) * Real.exp value) :
    approx ≤ Real.exp value ∧
      Real.exp value ≤ approx + 1 / (2 : ℝ) ^ workingPrecision := by
  have hexp := Num.exp_le_two_pow_twice hrange
  have hpow : (2 : ℝ) ^ (workingPrecision + 2 * range) ≤ 2 ^ accuracy :=
    pow_le_pow_right₀ (by norm_num) haccuracy
  have hscaled : Real.exp value * (2 : ℝ) ^ workingPrecision ≤ 2 ^ accuracy := by
    calc
      _ ≤ (2 : ℝ) ^ (2 * range) * 2 ^ workingPrecision :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = (2 : ℝ) ^ (workingPrecision + 2 * range) := by
        rw [pow_add, mul_comm]
      _ ≤ _ := hpow
  have habs : (1 / (2 : ℝ) ^ accuracy) * Real.exp value ≤
      1 / (2 : ℝ) ^ workingPrecision := by
    rw [one_div, inv_mul_eq_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    exact hscaled
  have hd := (abs_le.mp (herror.trans habs)).1
  exact ⟨hlower, by linarith only [hd]⟩

/-- Right-shifting the exponential approximation and allowing two units
at the working precision gives an outward enclosure. One unit covers the
shift and one covers the approximation error. -/
theorem initSparsifierExpRounded_bounds {value : ℝ} {numerator : ℕ}
    {range accuracy workingPrecision shift : ℕ}
    (hrange : value ≤ range)
    (haccuracy : workingPrecision + 2 * range ≤ accuracy)
    (hlower : (numerator : ℝ) / 2 ^ (workingPrecision + shift) ≤ Real.exp value)
    (herror : |(numerator : ℝ) / 2 ^ (workingPrecision + shift) - Real.exp value| ≤
      (1 / (2 : ℝ) ^ accuracy) * Real.exp value) :
    let rounded := numerator / 2 ^ shift
    (rounded : ℝ) / 2 ^ workingPrecision ≤ Real.exp value ∧
      Real.exp value ≤ (rounded + 2 : ℝ) / 2 ^ workingPrecision := by
  dsimp only
  obtain ⟨hlo, hhi⟩ := initSparsifierExpEndpoint_bounds hrange haccuracy hlower herror
  have hs : (0 : ℝ) < 2 ^ shift := by positivity
  have hp : (0 : ℝ) < 2 ^ workingPrecision := by positivity
  have ha : ((numerator / 2 ^ shift : ℕ) : ℝ) * 2 ^ shift ≤ numerator := by
    exact_mod_cast Nat.div_mul_le_self numerator (2 ^ shift)
  have hb : (numerator : ℝ) < (((numerator / 2 ^ shift : ℕ) : ℝ) + 1) * 2 ^ shift := by
    exact_mod_cast (Nat.div_lt_iff_lt_mul (by positivity : 0 < (2 : ℕ) ^ shift)).mp
      (Nat.lt_succ_self (numerator / 2 ^ shift))
  rw [pow_add, mul_comm ((2 : ℝ) ^ workingPrecision), ← div_div] at hlo hhi
  refine ⟨le_trans ?_ hlo, le_trans hhi ?_⟩
  · exact div_le_div_of_nonneg_right ((le_div_iff₀ hs).mpr ha) hp.le
  · rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith only [(div_lt_iff₀ hs).mpr hb]) hp.le

/-- Shift the stored exponential endpoint down to the working precision.
Register 94 holds the precision difference. -/
@[expose] def shiftInitSparsifierExpEndpoint (entry : ℕ) : Stmt :=
  .call 99 entry [.bin .sub (.reg 99) (.reg 67), .reg 67, .reg 94, .reg 99]

/-- The shifted block is placed at the end of the new heap allocation. -/
theorem shiftInitSparsifierExpEndpoint_runs
    {w h entry ret limbs shift numerator : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (himpl : MeetsContract w p entry (Num.shiftRightContract w h))
    (hret : st.regs 99 = ret) (hL : st.regs 67 = limbs) (hs : st.regs 94 = shift)
    (hle : limbs ≤ ret) (hsw : shift < 2 ^ w) (hroom : ret + (2 * limbs + 1) < 2 ^ w)
    (hz : ZeroFrom st.mem ret) (hv : Num.Valid st.mem (ret - limbs) h limbs)
    (hval : Num.intVal st.mem (ret - limbs) h limbs = (numerator : ℤ)) :
    ∃ out c top, Runs w p ω (shiftInitSparsifierExpEndpoint entry) st .normal out c ∧
      out.regs 99 = top ∧ top = ret + (2 * limbs + 1) ∧
      Num.Valid out.mem (top - limbs) h limbs ∧
      Num.intVal out.mem (top - limbs) h limbs = ((numerator / 2 ^ shift : ℕ) : ℤ) ∧
      (∀ r ≠ 99, out.regs r = st.regs r) ∧ (∀ a < ret, out.mem a = st.mem a) ∧
      ZeroFrom out.mem top ∧ c ≤ 66 * limbs + 113 := by
  have ha : ret - limbs < 2 ^ w := by omega
  have hargs : evalArgs w st [.bin .sub (.reg 99) (.reg 67), .reg 67, .reg 94, .reg 99] =
      some [ret - limbs, limbs, shift, ret] := by
    simp [evalArgs, Expr.eval, BinOp.eval, hret, hL, hs, ha]
  have hwords : ∀ v ∈ [ret - limbs, limbs, shift, ret], v < 2 ^ w := by
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl | rfl <;> omega
  have hpre : (Num.shiftRightContract w h).pre [ret - limbs, limbs, shift, ret] st.mem :=
    ⟨⟨_, _, _, _, rfl, by omega, hv⟩, hz, hroom⟩
  obtain ⟨out, c, top, hr, hp, ht, hk, hc⟩ :=
    runs_call_of_meetsContract (r := 99) himpl hargs hwords hpre ω
  obtain ⟨he, _, _, hf, hz', hv', hval'⟩ := hp
  change top = ret + (2 * limbs + 1) at he
  change Num.Valid out.mem (ret + limbs + 1) h limbs at hv'
  change Num.intVal out.mem (ret + limbs + 1) h limbs =
    Num.intVal st.mem (ret - limbs) h limbs / (2 : ℤ) ^ shift at hval'
  rw [hval] at hval'
  have haddr : top - limbs = ret + limbs + 1 := by omega
  change c ≤ 6 + (66 * limbs + 106) + 1 at hc
  exact ⟨out, c, top, hr, ht, he, haddr.symm ▸ hv',
    haddr.symm ▸ (by exact_mod_cast hval'), hk, hf, he.symm ▸ hz', by omega⟩

/-- Pack the shifted endpoint and store its upper bound two units above
the lower bound. The two numerators are returned in registers 2 and 3. -/
@[expose] def unpackInitSparsifierExpEndpoint (shiftEntry pack : ℕ) : Stmt :=
  shiftInitSparsifierExpEndpoint shiftEntry ;;
  packInitVertexLog pack ;;
  .assign 3 (.bin .add (.reg 2) (.const 2))

/-- The two returned words enclose the exponential at the working
precision, with the shift and packing costs accounted for. -/
theorem unpackInitSparsifierExpEndpoint_runs
    {w h shiftEntry pack ret limbs shift numerator range accuracy precision : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {value : ℝ}
    (hshift : MeetsContract w p shiftEntry (Num.shiftRightContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hret : st.regs 99 = ret) (hL : st.regs 67 = limbs) (hs : st.regs 94 = shift)
    (hle : limbs ≤ ret) (hsw : shift < 2 ^ w) (hroom : ret + (2 * limbs + 1) < 2 ^ w)
    (hz : ZeroFrom st.mem ret) (hv : Num.Valid st.mem (ret - limbs) h limbs)
    (hval : Num.intVal st.mem (ret - limbs) h limbs = (numerator : ℤ))
    (hfit : numerator / 2 ^ shift + 2 < 2 ^ w)
    (hrange : value ≤ range) (haccuracy : precision + 2 * range ≤ accuracy)
    (hlower : (numerator : ℝ) / 2 ^ (precision + shift) ≤ Real.exp value)
    (herror : |(numerator : ℝ) / 2 ^ (precision + shift) - Real.exp value| ≤
      (1 / (2 : ℝ) ^ accuracy) * Real.exp value) :
    ∃ out c, Runs w p ω (unpackInitSparsifierExpEndpoint shiftEntry pack) st .normal out c ∧
      out.regs 2 = numerator / 2 ^ shift ∧ out.regs 3 = numerator / 2 ^ shift + 2 ∧
      (out.regs 2 : ℝ) / 2 ^ precision ≤ Real.exp value ∧
      Real.exp value ≤ (out.regs 3 : ℝ) / 2 ^ precision ∧
      out.regs 99 = ret + (2 * limbs + 1) ∧
      (∀ r, r ≠ 2 → r ≠ 3 → r ≠ 99 → out.regs r = st.regs r) ∧
      (∀ a < ret, out.mem a = st.mem a) ∧ ZeroFrom out.mem (ret + (2 * limbs + 1)) ∧
      c ≤ 91 * limbs + 130 := by
  obtain ⟨mid, c₁, top, hr₁, ht, he, hv', hn, hk₁, hf, hz', hc₁⟩ :=
    shiftInitSparsifierExpEndpoint_runs (ω := ω) hshift hret hL hs hle hsw hroom hz hv hval
  obtain ⟨packed, c₂, hr₂, hp, hm, hk₂, hc₂⟩ :=
    packInitVertexLog_runs (ω := ω) hpack ht ((hk₁ 67 (by decide)).trans hL)
      (by omega) (by omega) hv' (by rw [hn]; positivity) (by rw [hn]; simpa only [Int.toNat_natCast] using (show
        numerator / 2 ^ shift < 2 ^ w by omega))
  have hp' : packed.regs 2 = numerator / 2 ^ shift := by simpa only [hn, Int.toNat_natCast] using hp
  let out := {packed with regs := Function.update packed.regs 3 (numerator / 2 ^ shift + 2)}
  have hr₃ : Runs w p ω (.assign 3 (.bin .add (.reg 2) (.const 2))) packed .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hp', hfit, show 2 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have hlo : out.regs 2 = numerator / 2 ^ shift := by simpa [out] using hp'
  have hhi : out.regs 3 = numerator / 2 ^ shift + 2 := by simp [out]
  obtain ⟨hl, hu⟩ := initSparsifierExpRounded_bounds hrange haccuracy hlower herror
  refine ⟨out, c₁ + (c₂ + 4 + 1) + 1, ?_, hlo, hhi, hlo.symm ▸ hl, ?_, ?_, ?_, ?_, ?_,
    by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, c₁, _, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨packed, c₂, 4, hr₂, hr₃, rfl⟩), rfl⟩)
  · simpa only [hhi, Nat.cast_add, Nat.cast_ofNat] using hu
  · simpa [out, hk₂ 99 (by decide), ht] using he
  · intro r h2 h3 h99
    simpa only [out, Function.update_of_ne h3] using (hk₂ r h2).trans (hk₁ r h99)
  · intro a ha
    exact (congrFun hm a).trans (hf a ha)
  · simpa only [out, hm, ← he] using hz'

/-- Save the working precision as the shift and use twice that
precision for the exponent numerators at the squared scale. -/
@[expose] def prepareInitSparsifierExpScale : Stmt :=
  .assign 94 (.reg 68) ;;
  .assign 68 (.bin .add (.reg 68) (.reg 68)) ;;
  .assign 4 (.reg 33)

/-- The exponential inputs use the squared scale and can be shifted back
to the original precision using register 94. -/
theorem prepareInitSparsifierExpScale_runs {w precision : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hP : st.regs 68 = precision) (hs : st.regs 33 = 2 ^ (precision + precision))
    (hfit : precision + precision < 2 ^ w) :
    ∃ out, Runs w p ω prepareInitSparsifierExpScale st .normal out 10 ∧
      out.regs 94 = precision ∧ out.regs 68 = precision + precision ∧
      out.regs 4 = 2 ^ (precision + precision) ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 94 → r ≠ 68 → r ≠ 4 → out.regs r = st.regs r) := by
  let saved := {st with regs := Function.update st.regs 94 precision}
  let widened := {saved with regs := Function.update saved.regs 68 (precision + precision)}
  let out := {widened with regs := Function.update widened.regs 4 (2 ^ (precision + precision))}
  have hr₁ : Runs w p ω (.assign 94 (.reg 68)) st .normal saved 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hP], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 68 (.bin .add (.reg 68) (.reg 68))) saved .normal widened 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, saved, hP, hfit], rfl, rfl, rfl⟩
  have hr₃ : Runs w p ω (.assign 4 (.reg 33)) widened .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, widened, saved, hs], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨saved, 2, 7, hr₁,
    runs_seq_iff.mpr (Or.inr ⟨widened, 4, 2, hr₂, hr₃, rfl⟩), rfl⟩),
    by simp [out, widened, saved], by simp [out, widened], by simp [out], rfl,
    fun r h94 h68 h4 => by simp [out, widened, saved, h94, h68, h4]⟩

/-- Evaluate a path exponent and return its enclosure at the working
precision. -/
@[expose] def computeInitSparsifierExpEndpoint (load exp shiftEntry pack endpoint : ℕ) : Stmt :=
  evaluateInitSparsifierExpEndpoint load exp endpoint ;;
  unpackInitSparsifierExpEndpoint shiftEntry pack

/-- The enclosure uses the runtime working scale and shift. The result
fits a word when the exponential range bound fits at that scale. -/
theorem computeInitSparsifierExpEndpoint_runs
    {w h load exp shiftEntry pack endpoint numerator precision shift limbs heap range accuracy : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hexp : MeetsContract w p exp (Num.positiveExponentialContract w h accuracy))
    (hshift : MeetsContract w p shiftEntry (Num.shiftRightContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hn : st.regs endpoint = numerator) (hs : st.regs 4 = 2 ^ (precision + shift))
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision + shift)
    (hh : st.regs 98 = heap) (hE : st.regs 97 = range) (hS : st.regs 94 = shift)
    (h95 : endpoint ≠ 95) (h96 : endpoint ≠ 96)
    (hw : numerator < 2 ^ w) (hsw : 2 ^ (precision + shift) < 2 ^ w)
    (hfit : 2 * numerator < Num.capacity h limbs)
    (hsfit : 2 * 2 ^ (precision + shift) < Num.capacity h limbs)
    (hroom : heap + limbs + limbs + Num.positiveExponentialSpace limbs (precision + shift) range +
      (2 * limbs + 1) < 2 ^ w)
    (hz : ZeroFrom st.mem heap)
    (hdiv : h ∣ precision + shift) (hacc : accuracy + range + 10 ≤ precision + shift)
    (hcap : precision + shift + 2 * range + 4 ≤ h * limbs)
    (hprec : 2 * (precision + shift) + 9 < 2 ^ w)
    (hhi : (numerator : ℝ) / 2 ^ (precision + shift) ≤ range)
    (hq : precision + 2 * range ≤ accuracy)
    (hword : 2 ^ (precision + 2 * range) + 2 < 2 ^ w) :
    ∃ out c, Runs w p ω (computeInitSparsifierExpEndpoint load exp shiftEntry pack endpoint)
      st .normal out c ∧
      (out.regs 2 : ℝ) / 2 ^ precision ≤ Real.exp ((numerator : ℝ) / 2 ^ (precision + shift)) ∧
      Real.exp ((numerator : ℝ) / 2 ^ (precision + shift)) ≤ (out.regs 3 : ℝ) / 2 ^ precision ∧
      out.regs 3 = out.regs 2 + 2 ∧
      max (out.regs 2) (out.regs 3) ≤ 2 ^ (precision + 2 * range) + 2 ∧
      out.regs 99 = heap + limbs + limbs + Num.positiveExponentialSpace limbs (precision + shift) range +
        (2 * limbs + 1) ∧
      (∀ r, r ≠ 2 → r ≠ 3 → r ≠ 95 → r ≠ 96 → r ≠ 98 → r ≠ 99 → out.regs r = st.regs r) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem (out.regs 99) ∧
      c ≤ 137 * limbs + Num.positiveExponentialCost limbs (precision + shift) range + 168 := by
  obtain ⟨mid, c₁, ret, hr₁, hret, hbase, he, hv, hlo, hu, herr, hk₁, hf₁, hz₁, hc₁⟩ :=
    evaluateInitSparsifierExpEndpoint_runs (ω := ω) hload hexp hn hs hL hP hh hE h95 h96 hw hsw
      hfit hsfit (by omega) hz hdiv hacc hcap hprec hhi
  let raw := Num.intVal mid.mem (ret - limbs) h limbs
  have hnonneg : 0 ≤ raw := by
    have hn' := (show (0 : ℝ) ≤ 1 by norm_num).trans hlo
    rw [Num.fixVal, le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (precision + shift)), zero_mul] at hn'
    exact_mod_cast hn'
  have hraw : raw = (raw.toNat : ℤ) := (Int.toNat_of_nonneg hnonneg).symm
  have hvalue : Num.fixVal mid.mem (ret - limbs) h limbs (precision + shift) =
      (raw.toNat : ℝ) / 2 ^ (precision + shift) := by
    rw [Num.fixVal]
    change (raw : ℝ) / _ = _
    exact congrArg (fun z : ℤ => (z : ℝ) / 2 ^ (precision + shift)) hraw |>.trans (by rw [Int.cast_natCast])
  rw [hvalue] at hu herr
  have hrounded := (initSparsifierExpRounded_bounds hhi hq hu herr).1
  have hfit' : raw.toNat / 2 ^ shift ≤ 2 ^ (precision + 2 * range) := by
    have hb := hrounded.trans (Num.exp_le_two_pow_twice hhi)
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ precision), ← pow_add, Nat.add_comm] at hb
    exact_mod_cast hb
  obtain ⟨out, c₂, hr₂, h2, h3, hlow, hhigh, ht, hk₂, hf₂, hz₂, hc₂⟩ :=
    unpackInitSparsifierExpEndpoint_runs (ω := ω) hshift hpack hret
      ((hk₁ 67 (by decide) (by decide) (by decide) (by decide)).trans hL)
      ((hk₁ 94 (by decide) (by decide) (by decide) (by decide)).trans hS)
      (by omega) (by omega) (by omega) hz₁ hv hraw (by omega) hhi hq hu herr
  exact ⟨out, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩),
    hlow, hhigh, by rw [h2, h3], by rw [h2, h3, max_eq_right (by omega)]; omega, by rw [ht, he], fun r h2 h3 h95 h96 h98 h99 =>
      (hk₂ r h2 h3 h99).trans (hk₁ r h95 h96 h98 h99),
    fun a ha => (hf₂ a (by omega)).trans (hf₁ a ha), ht.symm ▸ hz₂, by omega⟩

/-- Save the lower powered endpoint and advance the heap before
evaluating the upper endpoint. -/
@[expose] def saveInitSparsifierPowerLower : Stmt :=
  .assign 48 (.reg 2) ;; .assign 98 (.reg 99)

/-- Both saved words come from the preceding endpoint evaluation. -/
theorem saveInitSparsifierPowerLower_runs {w : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} :
    ∃ out, Runs w p ω saveInitSparsifierPowerLower st .normal out 5 ∧
      out.regs 48 = st.regs 2 ∧ out.regs 98 = st.regs 99 ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 48 → r ≠ 98 → out.regs r = st.regs r) := by
  let mid := {st with regs := Function.update st.regs 48 (st.regs 2)}
  let out := {mid with regs := Function.update mid.regs 98 (st.regs 99)}
  have hr₁ : Runs w p ω (.assign 48 (.reg 2)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 98 (.reg 99)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, mid], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, 2, hr₁, hr₂, rfl⟩),
    by simp [out, mid], by simp [out], rfl, fun r h48 h98 => by simp [out, mid, h48, h98]⟩

/-- Save the upper endpoint and restore the working scale, keeping the
returned heap available to the next path calculation. -/
@[expose] def finishInitSparsifierPower : Stmt :=
  .assign 49 (.reg 3) ;;
  .assign 98 (.reg 99) ;;
  .assign 68 (.reg 94) ;;
  .assign 4 (.bin .shiftLeft (.const 1) (.reg 94))

/-- The working precision and scale are recovered from the saved shift. -/
theorem finishInitSparsifierPower_runs {w precision : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hP : st.regs 94 = precision) (hwidth : precision < w) :
    ∃ out, Runs w p ω finishInitSparsifierPower st .normal out 13 ∧
      out.regs 49 = st.regs 3 ∧ out.regs 98 = st.regs 99 ∧
      out.regs 68 = precision ∧ out.regs 4 = 2 ^ precision ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 49 → r ≠ 98 → r ≠ 68 → r ≠ 4 → out.regs r = st.regs r) := by
  let a := {st with regs := Function.update st.regs 49 (st.regs 3)}
  let b := {a with regs := Function.update a.regs 98 (st.regs 99)}
  let c := {b with regs := Function.update b.regs 68 precision}
  let out := {c with regs := Function.update c.regs 4 (2 ^ precision)}
  have hr₁ : Runs w p ω (.assign 49 (.reg 3)) st .normal a 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 98 (.reg 99)) a .normal b 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, a], rfl, rfl, rfl⟩
  have hr₃ : Runs w p ω (.assign 68 (.reg 94)) b .normal c 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, a, b, hP], rfl, rfl, rfl⟩
  have hf := Nat.pow_lt_pow_right (show 1 < 2 by decide) hwidth
  have hone : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hr₄ : Runs w p ω (.assign 4 (.bin .shiftLeft (.const 1) (.reg 94))) c .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, a, b, c, hP, hone, Nat.shiftLeft_eq, hf],
      rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨a, 2, 10, hr₁,
    runs_seq_iff.mpr (Or.inr ⟨b, 2, 7, hr₂,
      runs_seq_iff.mpr (Or.inr ⟨c, 2, 4, hr₃, hr₄, rfl⟩), rfl⟩), rfl⟩),
    by simp [out, c, b, a], by simp [out, c, b], by simp [out, c], by simp [out], rfl,
    fun r h49 h98 h68 h4 => by simp [out, c, b, a, h49, h98, h68, h4]⟩

/-- Evaluate both prepared exponent endpoints and restore the working
scale for the fallback calculation. -/
@[expose] def computeInitSparsifierPower (load exp shiftEntry pack : ℕ) : Stmt :=
  computeInitSparsifierExpEndpoint load exp shiftEntry pack 31 ;;
  saveInitSparsifierPowerLower ;;
  computeInitSparsifierExpEndpoint load exp shiftEntry pack 32 ;;
  finishInitSparsifierPower

/-- The endpoint calls enclose the exponential of every exponent in
the supplied interval. Both allocations are charged to the cost. -/
theorem computeInitSparsifierPower_runs
    {w h load exp shiftEntry pack lo hi precision limbs heap range accuracy : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {target : ℝ}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hexp : MeetsContract w p exp (Num.positiveExponentialContract w h accuracy))
    (hshift : MeetsContract w p shiftEntry (Num.shiftRightContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hlo : st.regs 31 = lo) (hhi : st.regs 32 = hi)
    (hs : st.regs 4 = 2 ^ (precision + precision)) (hL : st.regs 67 = limbs)
    (hP : st.regs 68 = precision + precision) (hh : st.regs 98 = heap)
    (hE : st.regs 97 = range) (hS : st.regs 94 = precision)
    (hw : max lo hi < 2 ^ w) (hsw : 2 ^ (precision + precision) < 2 ^ w)
    (hfit : 2 * max lo hi < Num.capacity h limbs)
    (hsfit : 2 * 2 ^ (precision + precision) < Num.capacity h limbs)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision + precision)
    (hacc : accuracy + range + 10 ≤ precision + precision)
    (hcap : precision + precision + 2 * range + 4 ≤ h * limbs)
    (hprec : 2 * (precision + precision) + 9 < 2 ^ w) (hwidth : precision < w)
    (hl : (lo : ℝ) / 2 ^ (precision + precision) ≤ target)
    (hu : target ≤ (hi : ℝ) / 2 ^ (precision + precision))
    (hbound : (hi : ℝ) / 2 ^ (precision + precision) ≤ range)
    (hq : precision + 2 * range ≤ accuracy)
    (hword : 2 ^ (precision + 2 * range) + 2 < 2 ^ w) :
    let space := limbs + limbs + Num.positiveExponentialSpace limbs (precision + precision) range +
      (2 * limbs + 1)
    heap + space + space < 2 ^ w →
    ∃ out cost, Runs w p ω (computeInitSparsifierPower load exp shiftEntry pack) st .normal out cost ∧
      (out.regs 48 : ℝ) / 2 ^ precision ≤ Real.exp target ∧
      Real.exp target ≤ (out.regs 49 : ℝ) / 2 ^ precision ∧
      Real.exp ((lo : ℝ) / 2 ^ (precision + precision)) ≤
        ((out.regs 48 : ℝ) + 2) / 2 ^ precision ∧
      ((out.regs 49 : ℝ) - 2) / 2 ^ precision ≤
        Real.exp ((hi : ℝ) / 2 ^ (precision + precision)) ∧
      max (out.regs 48) (out.regs 49) ≤ 2 ^ (precision + 2 * range) + 2 ∧
      out.regs 4 = 2 ^ precision ∧ out.regs 68 = precision ∧
      out.regs 98 = heap + space + space ∧ ZeroFrom out.mem (heap + space + space) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧
      (∀ r, r ∉ ([2, 3, 4, 48, 49, 68, 95, 96, 98, 99] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ 274 * limbs + 2 * Num.positiveExponentialCost limbs (precision + precision) range + 357 := by
  intro space hroom
  obtain ⟨a, c₁, hr₁, lb, aUpper, haGap, hw₁, ht₁, hk₁, hf₁, hz₁, hc₁⟩ :=
    computeInitSparsifierExpEndpoint_runs (ω := ω) hload hexp hshift hpack hlo hs hL hP hh hE hS
      (by decide) (by decide) ((le_max_left ..).trans_lt hw) hsw
      ((Nat.mul_le_mul_left 2 (le_max_left ..)).trans_lt hfit) hsfit
      (by dsimp [space] at hroom; omega) hz hdiv hacc hcap hprec
      (hl.trans (hu.trans hbound)) hq hword
  obtain ⟨b, hr₂, hsaved, hh₂, hm₂, hk₂⟩ :=
    saveInitSparsifierPowerLower_runs (w := w) (p := p) (ω := ω) (st := a)
  have keep (r : ℕ) (h2 : r ≠ 2) (h3 : r ≠ 3) (h48 : r ≠ 48)
      (h95 : r ≠ 95) (h96 : r ≠ 96) (h98 : r ≠ 98) (h99 : r ≠ 99) :
      b.regs r = st.regs r := (hk₂ r h48 h98).trans (hk₁ r h2 h3 h95 h96 h98 h99)
  have hheap : b.regs 98 = heap + space := by rw [hh₂, ht₁]; dsimp [space]; omega
  obtain ⟨c, c₂, hr₃, cLower, ub, hcGap, hw₃, ht₃, hk₃, hf₃, hz₃, hc₂⟩ :=
    computeInitSparsifierExpEndpoint_runs (ω := ω) hload hexp hshift hpack
      ((keep 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hhi)
      ((keep 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs)
      ((keep 67 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL)
      ((keep 68 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hP)
      hheap
      ((keep 97 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hE)
      ((keep 94 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hS)
      (by decide) (by decide) ((le_max_right ..).trans_lt hw) hsw
      ((Nat.mul_le_mul_left 2 (le_max_right ..)).trans_lt hfit) hsfit
      (by dsimp [space] at hroom ⊢; omega) (by rw [hm₂, ← hheap, hh₂]; exact hz₁)
      hdiv hacc hcap hprec hbound hq hword
  obtain ⟨out, hr₄, h49, h98, h68, h4, hm₄, hk₄⟩ := finishInitSparsifierPower_runs (p := p) (ω := ω)
    ((hk₃ 94 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((keep 94 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hS))
    hwidth
  have h48 : out.regs 48 = a.regs 2 :=
    (hk₄ 48 (by decide) (by decide) (by decide) (by decide)).trans
      ((hk₃ 48 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsaved)
  have htop : c.regs 99 = heap + space + space := by rw [ht₃]; dsimp [space]; omega
  refine ⟨out, c₁ + (5 + (c₂ + 13 + 1) + 1) + 1, ?_, ?_, ?_, ?_, ?_, ?_, h4, h68, h98.trans htop,
    ?_, ?_, ?_, by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨a, c₁, _, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨b, 5, _, hr₂,
        runs_seq_iff.mpr (Or.inr ⟨c, c₂, 13, hr₃, hr₄, rfl⟩), rfl⟩), rfl⟩)
  · rw [h48]
    exact lb.trans (Real.exp_le_exp.mpr hl)
  · rw [h49]
    exact (Real.exp_le_exp.mpr hu).trans ub
  · rw [h48]
    simpa only [haGap, Nat.cast_add, Nat.cast_ofNat] using aUpper
  · rw [h49, hcGap, Nat.cast_add, Nat.cast_ofNat, add_sub_cancel_right]
    exact cLower
  · rw [h48, h49, max_le_iff]
    exact ⟨(le_max_left ..).trans hw₁, (le_max_right ..).trans hw₃⟩
  · rw [hm₄, ← htop]
    exact hz₃
  · intro x hx
    exact (congrFun hm₄ x).trans ((hf₃ x (by omega)).trans ((congrFun hm₂ x).trans (hf₁ x hx)))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h2, h3, h4, h48, h49, h68, h95, h96, h98, h99⟩ := hr
    exact (hk₄ r h49 h98 h68 h4).trans ((hk₃ r h2 h3 h95 h96 h98 h99).trans
      (keep r h2 h3 h48 h95 h96 h98 h99))

/-- Prepare the range and precision for the two powered endpoint calls. -/
@[expose] def prepareInitSparsifierPower : Stmt :=
  setInitSparsifierExpRange ;; prepareInitSparsifierExpScale

/-- The machine bounds the exponent using its upper numerator and
switches to the precision at which both numerators were computed. -/
theorem prepareInitSparsifierPower_runs {w precision hi : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hP : st.regs 68 = precision) (hhi : st.regs 32 = hi)
    (hs : st.regs 33 = 2 ^ (precision + precision))
    (hfit : hi + 1 < 2 ^ w) (hp : precision + precision < 2 ^ w) :
    ∃ out, Runs w p ω prepareInitSparsifierPower st .normal out 17 ∧
      out.regs 97 = hi / 2 ^ (precision + precision) + 1 ∧
      (hi : ℝ) / 2 ^ (precision + precision) ≤ (out.regs 97 : ℝ) ∧
      out.regs 94 = precision ∧ out.regs 68 = precision + precision ∧
      out.regs 4 = 2 ^ (precision + precision) ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 97 → r ≠ 94 → r ≠ 68 → r ≠ 4 → out.regs r = st.regs r) := by
  obtain ⟨mid, hr₁, h97, hbound, hm₁, hk₁⟩ :=
    setInitSparsifierExpRange_runs (p := p) (ω := ω) hhi hs (by positivity) hfit
  obtain ⟨out, hr₂, h94, h68, h4, hm₂, hk₂⟩ :=
    prepareInitSparsifierExpScale_runs (p := p) (ω := ω)
      ((hk₁ 68 (by decide)).trans hP) ((hk₁ 33 (by decide)).trans hs) hp
  have he : out.regs 97 = mid.regs 97 := hk₂ 97 (by decide) (by decide) (by decide)
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 6, 10, hr₁, hr₂, rfl⟩),
    he.trans h97, ?_, h94, h68, h4, hm₂.trans hm₁,
    fun r h97 h94 h68 h4 => (hk₂ r h94 h68 h4).trans (hk₁ r h97)⟩
  rw [he]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hbound

/-- Prepare the runtime range and evaluate the powered endpoint pair. -/
@[expose] def evaluateInitSparsifierPower (load exp shiftEntry pack : ℕ) : Stmt :=
  prepareInitSparsifierPower ;; computeInitSparsifierPower load exp shiftEntry pack

/-- The powered endpoint pair uses the range derived from the input
words and restores the working precision on return. -/
theorem evaluateInitSparsifierPower_runs
    {w h load exp shiftEntry pack lo hi precision limbs heap accuracy : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {target : ℝ}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hexp : MeetsContract w p exp (Num.positiveExponentialContract w h accuracy))
    (hshift : MeetsContract w p shiftEntry (Num.shiftRightContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hlo : st.regs 31 = lo) (hhi : st.regs 32 = hi)
    (hs : st.regs 33 = 2 ^ (precision + precision)) (hL : st.regs 67 = limbs)
    (hP : st.regs 68 = precision) (hh : st.regs 98 = heap)
    (hup : hi + 1 < 2 ^ w)
    (hw : max lo hi < 2 ^ w) (hsw : 2 ^ (precision + precision) < 2 ^ w)
    (hfit : 2 * max lo hi < Num.capacity h limbs)
    (hsfit : 2 * 2 ^ (precision + precision) < Num.capacity h limbs)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision + precision)
    (hprec : 2 * (precision + precision) + 9 < 2 ^ w) (hwidth : precision < w)
    (hl : (lo : ℝ) / 2 ^ (precision + precision) ≤ target)
    (hu : target ≤ (hi : ℝ) / 2 ^ (precision + precision)) :
    let range := hi / 2 ^ (precision + precision) + 1
    accuracy + range + 10 ≤ precision + precision →
    precision + precision + 2 * range + 4 ≤ h * limbs →
    precision + 2 * range ≤ accuracy →
    2 ^ (precision + 2 * range) + 2 < 2 ^ w →
    let space := limbs + limbs + Num.positiveExponentialSpace limbs (precision + precision) range +
      (2 * limbs + 1)
    heap + space + space < 2 ^ w →
    ∃ out cost, Runs w p ω (evaluateInitSparsifierPower load exp shiftEntry pack) st .normal out cost ∧
      (out.regs 48 : ℝ) / 2 ^ precision ≤ Real.exp target ∧
      Real.exp target ≤ (out.regs 49 : ℝ) / 2 ^ precision ∧
      Real.exp ((lo : ℝ) / 2 ^ (precision + precision)) ≤
        ((out.regs 48 : ℝ) + 2) / 2 ^ precision ∧
      ((out.regs 49 : ℝ) - 2) / 2 ^ precision ≤
        Real.exp ((hi : ℝ) / 2 ^ (precision + precision)) ∧
      max (out.regs 48) (out.regs 49) ≤ 2 ^ (precision + 2 * range) + 2 ∧
      out.regs 4 = 2 ^ precision ∧ out.regs 68 = precision ∧
      out.regs 98 = heap + space + space ∧ ZeroFrom out.mem (heap + space + space) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧
      (∀ r, r ∉ ([2, 3, 4, 48, 49, 68, 94, 95, 96, 97, 98, 99] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ 274 * limbs + 2 * Num.positiveExponentialCost limbs (precision + precision) range + 375 := by
  intro range hacc hcap hq hword space hroom
  obtain ⟨mid, hr₁, h97, hbound, h94, h68, h4, hm, hk⟩ :=
    prepareInitSparsifierPower_runs (p := p) (ω := ω) hP hhi hs hup (by omega)
  obtain ⟨out, cost, hr₂, lb, ub, ha, hb, hwordOut, hscale, hprec', hheap, hz', hf, hk', hc⟩ :=
    computeInitSparsifierPower_runs (ω := ω) hload hexp hshift hpack
      ((hk 31 (by decide) (by decide) (by decide) (by decide)).trans hlo)
      ((hk 32 (by decide) (by decide) (by decide) (by decide)).trans hhi)
      h4 ((hk 67 (by decide) (by decide) (by decide) (by decide)).trans hL) h68
      ((hk 98 (by decide) (by decide) (by decide) (by decide)).trans hh)
      h97 h94 hw hsw hfit hsfit (hm.symm ▸ hz) hdiv hacc hcap hprec hwidth hl hu
      (h97 ▸ hbound) hq hword hroom
  change cost ≤ 274 * limbs + 2 * Num.positiveExponentialCost limbs (precision + precision) range + 357 at hc
  refine ⟨out, 17 + cost + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 17, cost, hr₁, hr₂, rfl⟩),
    lb, ub, ha, hb, hwordOut, hscale, hprec', hheap, hz', fun a ha => (hf a ha).trans (congrFun hm a), ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h2, h3, h4, h48, h49, h68, h94, h95, h96, h97, h98, h99⟩ := hr
    exact (hk' r (by simp [h2, h3, h4, h48, h49, h68, h95, h96, h98, h99])).trans
      (hk r h97 h94 h68 h4)
  · omega

/-- Form the exponent products and evaluate the powered path bound. -/
@[expose] def computeInitSparsifierPathPower (load exp shiftEntry pack : ℕ) : Stmt :=
  initSparsifierPathExponent ;; evaluateInitSparsifierPower load exp shiftEntry pack

/-- Multiplying the two scaled exponent inputs gives an error bound
from the endpoint gaps of the coefficient and logarithm. -/
theorem initSparsifierPathExponent_gap
    {kLo kHi logLo logHi q exponent scale kBound logBound kErr logErr : ℕ}
    (hk : kLo ≤ kHi) (hl : logLo ≤ logHi)
    (hkBound : kHi ≤ kBound * scale) (hlBound : logHi ≤ logBound * scale)
    (hkErr : kHi - kLo ≤ kErr) (hlErr : logHi - logLo ≤ logErr) :
    kHi * q * (exponent * logHi) - kLo * q * (exponent * logLo) ≤
      (q * exponent * (kErr * logBound + kBound * logErr)) * scale := by
  have hdiff : kHi * logHi =
      kLo * logLo + ((kHi - kLo) * logHi + kLo * (logHi - logLo)) := by
    calc
      _ = kLo * logHi + (kHi - kLo) * logHi := by
        conv_lhs => rw [← Nat.add_sub_of_le hk]
        rw [Nat.add_mul]
      _ = _ := by
        conv_lhs => lhs; rw [← Nat.add_sub_of_le hl]
        ring
  have hbound : (kHi - kLo) * logHi + kLo * (logHi - logLo) ≤
      (kErr * logBound + kBound * logErr) * scale := by
    calc
      _ ≤ kErr * (logBound * scale) + (kBound * scale) * logErr :=
        Nat.add_le_add (Nat.mul_le_mul hkErr hlBound) (Nat.mul_le_mul (hk.trans hkBound) hlErr)
      _ = _ := by ring
  have hu : kHi * logHi ≤ kLo * logLo + (kErr * logBound + kBound * logErr) * scale := by
    rw [hdiff]
    exact Nat.add_le_add_left hbound _
  apply Nat.sub_le_iff_le_add.mpr
  calc
    _ = (q * exponent) * (kHi * logHi) := by ring
    _ ≤ (q * exponent) * (kLo * logLo + (kErr * logBound + kBound * logErr) * scale) :=
      Nat.mul_le_mul_left _ hu
    _ = _ := by ring

/-- The powered path enclosure inherits the exponent gap with a factor
bounded by the upper exponential, plus two rounding units at each end. -/
theorem initSparsifierPoweredGap
    {lo hi lower upper precision range err : ℕ}
    (horder : lo ≤ hi) (hgap : hi - lo ≤ err * 2 ^ precision)
    (hrange : (hi : ℝ) / 2 ^ (precision + precision) ≤ range)
    (hl : Real.exp ((lo : ℝ) / 2 ^ (precision + precision)) ≤
      ((lower : ℝ) + 2) / 2 ^ precision)
    (hu : ((upper : ℝ) - 2) / 2 ^ precision ≤
      Real.exp ((hi : ℝ) / 2 ^ (precision + precision))) :
    upper - lower ≤ 2 ^ (2 * range) * err + 4 := by
  let scale : ℝ := 2 ^ precision
  let x : ℝ := (lo : ℝ) / (scale * scale)
  let y : ℝ := (hi : ℝ) / (scale * scale)
  have hs : 0 < scale := by dsimp [scale]; positivity
  have he : (2 : ℝ) ^ (precision + precision) = scale * scale := pow_add _ _ _
  rw [he] at hl hu hrange
  have hx : x ≤ y := div_le_div_of_nonneg_right (by exact_mod_cast horder) (mul_pos hs hs).le
  have hy : y ≤ range := hrange
  have hwidth : y - x ≤ (err : ℝ) / scale := by
    have hn : (hi : ℝ) - (lo : ℝ) ≤ (err : ℝ) * scale := by
      dsimp [scale]
      simpa only [Nat.cast_sub horder, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat] using (show ((hi - lo : ℕ) : ℝ) ≤ ((err * 2 ^ precision : ℕ) : ℝ) by exact_mod_cast hgap)
    change (hi : ℝ) / (scale * scale) - (lo : ℝ) / (scale * scale) ≤ _
    rw [← sub_div, div_le_div_iff₀ (mul_pos hs hs) hs]
    calc
      _ ≤ ((err : ℝ) * scale) * scale := mul_le_mul_of_nonneg_right hn hs.le
      _ = _ := by ring
  have heDiff : Real.exp y - Real.exp x ≤ Real.exp y * (y - x) := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (x - y)) (Real.exp_pos y).le
    rw [← Real.exp_add, sub_add_cancel] at h
    rw [add_mul, one_mul] at h
    linarith only [h]
  have hdiff : Real.exp y - Real.exp x ≤ (2 : ℝ) ^ (2 * range) * ((err : ℝ) / scale) :=
    heDiff.trans (mul_le_mul (Num.exp_le_two_pow_twice hy) hwidth
      (sub_nonneg.mpr hx) (by positivity))
  have hout : ((upper : ℝ) - (lower : ℝ) - 4) / scale ≤
      (2 : ℝ) ^ (2 * range) * ((err : ℝ) / scale) := by
    change Real.exp x ≤ ((lower : ℝ) + 2) / scale at hl
    change ((upper : ℝ) - 2) / scale ≤ Real.exp y at hu
    rw [add_div] at hl
    rw [sub_div] at hu
    rw [sub_div, sub_div]
    linarith only [hl, hu, hdiff, show (4 : ℝ) / scale = 2 / scale + 2 / scale by ring]
  have hbound := (div_le_iff₀ hs).mp hout
  rw [mul_assoc, div_mul_cancel₀ _ hs.ne'] at hbound
  apply Nat.sub_le_iff_le_add.mpr
  have hfinal : (upper : ℝ) ≤ (2 : ℝ) ^ (2 * range) * (err : ℝ) + 4 + (lower : ℝ) := by
    linarith only [hbound]
  exact_mod_cast hfinal

/-- The returned words enclose the powered term of the concrete path bound. -/
theorem computeInitSparsifierPathPower_runs
    {w h load exp shiftEntry pack precision limbs heap accuracy Kγ M kLo kHi logLo logHi : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {K : ℝ}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hexp : MeetsContract w p exp (Num.positiveExponentialContract w h accuracy))
    (hshift : MeetsContract w p shiftEntry (Num.shiftRightContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hs : st.regs 33 = 2 ^ (precision + precision)) (hL : st.regs 67 = limbs)
    (hP : st.regs 68 = precision) (hh : st.regs 98 = heap)
    (hsw : 2 ^ (precision + precision) < 2 ^ w)
    (hsfit : 2 * 2 ^ (precision + precision) < Num.capacity h limbs)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision + precision)
    (hprec : 2 * (precision + precision) + 9 < 2 ^ w) (hwidth : precision < w)
    (h39 : st.regs 39 = kLo) (h40 : st.regs 40 = kHi) (h38 : st.regs 38 = Expander.qOf M)
    (h34 : st.regs 34 = logLo) (h35 : st.regs 35 = logHi)
    (hkLo : (kLo : ℝ) / (2 ^ precision : ℕ) ≤ max K 1)
    (hkHi : max K 1 ≤ (kHi : ℝ) / (2 ^ precision : ℕ))
    (hlLo : (logLo : ℝ) / (2 ^ precision : ℕ) ≤ Real.log (Cited.csGamma Kγ (3 * M)))
    (hlHi : Real.log (Cited.csGamma Kγ (3 * M)) ≤ (logHi : ℝ) / (2 ^ precision : ℕ))
    (hkl : kLo * Expander.qOf M < 2 ^ w) (hkh : kHi * Expander.qOf M < 2 ^ w) :
    let lo := kLo * Expander.qOf M * logLo
    let hi := kHi * Expander.qOf M * logHi
    hi + 1 < 2 ^ w →
    max lo hi < 2 ^ w →
    2 * max lo hi < Num.capacity h limbs →
    let range := hi / 2 ^ (precision + precision) + 1
    accuracy + range + 10 ≤ precision + precision →
    precision + precision + 2 * range + 4 ≤ h * limbs →
    precision + 2 * range ≤ accuracy →
    2 ^ (precision + 2 * range) + 2 < 2 ^ w →
    let space := limbs + limbs + Num.positiveExponentialSpace limbs (precision + precision) range +
      (2 * limbs + 1)
    heap + space + space < 2 ^ w →
    let power := (Cited.csGamma Kγ (3 * M) : ℝ) ^ (max K 1 * (Expander.qOf M : ℝ))
    ∃ out cost, Runs w p ω (computeInitSparsifierPathPower load exp shiftEntry pack) st .normal out cost ∧
      (out.regs 48 : ℝ) / 2 ^ precision ≤ power ∧
      power ≤ (out.regs 49 : ℝ) / 2 ^ precision ∧
      Real.exp ((lo : ℝ) / 2 ^ (precision + precision)) ≤
        ((out.regs 48 : ℝ) + 2) / 2 ^ precision ∧
      ((out.regs 49 : ℝ) - 2) / 2 ^ precision ≤
        Real.exp ((hi : ℝ) / 2 ^ (precision + precision)) ∧
      max (out.regs 48) (out.regs 49) ≤ 2 ^ (precision + 2 * range) + 2 ∧
      out.regs 4 = 2 ^ precision ∧ out.regs 68 = precision ∧
      out.regs 98 = heap + space + space ∧ ZeroFrom out.mem (heap + space + space) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧
      (∀ r, r ∉ ([2, 3, 4, 31, 32, 48, 49, 68, 94, 95, 96, 97, 98, 99] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ 274 * limbs + 2 * Num.positiveExponentialCost limbs (precision + precision) range + 389 := by
  intro lo hi hup hw hfit range hacc hcap hq hword space hroom power
  have hscale : (0 : ℝ) < ((2 ^ precision : ℕ) : ℝ) := by positivity
  obtain ⟨mid, hr₁, lb, ub, h31, h32, hm, hk⟩ :=
    initSparsifierPathExponent_runs K M (2 ^ precision) kLo kHi logLo logHi
      (p := p) (ω := ω) hscale h39 h40 h38 h34 h35 hkLo hkHi hlLo hlHi hkl hkh
      ((le_max_left lo hi).trans_lt hw) ((le_max_right lo hi).trans_lt hw)
  have hden : (((2 ^ precision : ℕ) : ℝ) ^ 2) = (2 : ℝ) ^ (precision + precision) := by
    simp [pow_add, pow_two]
  rw [hden] at lb ub
  obtain ⟨out, cost, hr₂, hlo, hhi, ha, hb, hwordOut, hs', hp', hh', hz', hf, hk', hc⟩ :=
    evaluateInitSparsifierPower_runs (ω := ω) hload hexp hshift hpack h31 h32
      ((hk 33 (by decide) (by decide)).trans hs) ((hk 67 (by decide) (by decide)).trans hL)
      ((hk 68 (by decide) (by decide)).trans hP) ((hk 98 (by decide) (by decide)).trans hh)
      hup hw hsw hfit hsfit (hm.symm ▸ hz) hdiv hprec hwidth (h31 ▸ lb) (h32 ▸ ub)
      hacc hcap hq hword hroom
  have hbase : (0 : ℝ) < Cited.csGamma Kγ (3 * M) := by unfold Cited.csGamma; positivity
  have he : power = Real.exp (max K 1 * (Expander.qOf M : ℝ) *
      Real.log (Cited.csGamma Kγ (3 * M))) := by
    dsimp [power]
    rw [Real.rpow_def_of_pos hbase, mul_comm (Real.log _)]
  change cost ≤ 274 * limbs + 2 * Num.positiveExponentialCost limbs (precision + precision) range + 375 at hc
  refine ⟨out, 13 + cost + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 13, cost, hr₁, hr₂, rfl⟩),
    he.symm ▸ hlo, he.symm ▸ hhi, ha, hb, hwordOut, hs', hp', hh', hz', fun a ha => (hf a ha).trans (congrFun hm a),
    ?_, by omega⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h2, h3, h4, h31, h32, h48, h49, h68, h94, h95, h96, h97, h98, h99⟩ := hr
  exact (hk' r (by simp [h2, h3, h4, h48, h49, h68, h94, h95, h96, h97, h98, h99])).trans
    (hk r h31 h32)

end MinCostFlow.MinRatio
