module

public import MinCostFlow.Num.IsZero
public import MinCostFlow.Num.LoadSmall
public import MinCostFlow.Num.Logarithm
public import MinCostFlow.Num.IPM.BitLength
public import MinCostFlow.Num.PackWord
import MinCostFlow.Num.ShiftFacts
import MinCostFlow.Num.DivisionSigns
import MinCostFlow.Num.WordBounds
import MinCostFlow.Num.NormalizedLogarithm
import MinCostFlow.Num.RangeLogarithm
import MinCostFlow.Num.FixedDivide
import MinCostFlow.Num.IntegerDivide
import MinCostFlow.Num.UnsignedDivide
import MinCostFlow.Num.LogHorner
public import MinCostFlow.MinRatio.InitDepthPower
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Rounding a depth logarithm endpoint

Pack the whole limbs above the binary point and add a carry when the
fractional limbs are nonzero. The fixed-point scale can span many words.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Num

/-- Arguments `[address, limbs, fractionalLimbs]`. Return the endpoint rounded up. -/
@[expose] def initDepthEndpointBody (pack zeroEntry : ℕ) : Stmt :=
  .call 3 pack [.bin .add (.reg 0) (.reg 2), .bin .sub (.reg 1) (.reg 2)] ;;
  .call 4 zeroEntry [.reg 0, .reg 2] ;;
  .cond (.reg 4) (.ret (.reg 3)) (.ret (.bin .add (.reg 3) (.const 1)))

/-- Splitting a valid block at the binary point gives the quotient and remainder. -/
theorem initDepthEndpoint_split {mem : ℕ → ℕ} {a h L k : ℕ}
    (hv : Valid mem a h L) (hk : k ≤ L) :
    unsignedVal mem a h L / capacity h k = unsignedVal mem (a + k) h (L - k) ∧
      unsignedVal mem a h L % capacity h k = unsignedVal mem a h k := by
  have hcap : 0 < capacity h k := capacity_pos h k
  have hlo : unsignedVal mem a h k < capacity h k :=
    unsignedVal_lt (fun i hi => hv i (hi.trans_le hk))
  refine ⟨?_, unsignedVal_mod_prefix hv hk⟩
  conv_lhs => rw [show L = k + (L - k) by omega, unsignedVal_split]
  rw [Nat.add_mul_div_left _ _ hcap, Nat.div_eq_of_lt hlo, zero_add]

/-- Read-only endpoint rounding with a one-word result. -/
@[expose] def initDepthEndpointContract (w h : ℕ) : Contract where
  pre args mem := ∃ a L k, args = [a, L, k] ∧ k ≤ L ∧ a + L < 2 ^ w ∧ Valid mem a h L ∧
    unsignedVal mem a h L / capacity h k + 1 < 2 ^ w
  post args mem v mem' :=
    let value := unsignedVal mem (args.getD 0 0) h (args.getD 1 0)
    let scale := capacity h (args.getD 2 0)
    mem' = mem ∧ v = value / scale + (if value % scale = 0 then 0 else 1)
  cost args _ := 25 * args.getD 1 0 + 50

/-- The packed upper block gives the quotient and the zero scan gives its carry. -/
theorem initDepthEndpoint_meetsContract {w h entry pack zeroEntry : ℕ} {p : Program}
    (hw : 1 < 2 ^ w) (hp : p.procs[entry]? = some (initDepthEndpointBody pack zeroEntry))
    (hpack : MeetsContract w p pack (packWordContract w h))
    (hzero : MeetsContract w p zeroEntry (isZeroContract w h)) :
    MeetsContract w p entry (initDepthEndpointContract w h) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨a, L, k, rfl, hk, ha, hv, hfit⟩
  have haw : a < 2 ^ w := hwords a (by simp)
  have hLw : L < 2 ^ w := hwords L (by simp)
  have hkw : k < 2 ^ w := hwords k (by simp)
  obtain ⟨hq, hr⟩ := initDepthEndpoint_split hv hk
  have hqfit : unsignedVal mem (a + k) h (L - k) + 1 < 2 ^ w := hq ▸ hfit
  have hlow : Valid mem a h k := fun i hi => hv i (hi.trans_le hk)
  have hhigh : Valid mem (a + k) h (L - k) := by
    intro i hi
    simpa only [Nat.add_assoc] using hv (k + i) (by omega)
  apply runs_start_le
  unfold initDepthEndpointBody
  refine runs_seq_call_le hpack (vs := [a + k, L - k]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨a + k, L - k, rfl, by omega, hhigh, by change unsignedVal mem (a + k) h (L - k) < 2 ^ w; omega⟩
  · intro q mem₁ pos₁ hp₁
    obtain ⟨hm₁, hqval⟩ := hp₁
    subst mem₁
    change q = unsignedVal mem (a + k) h (L - k) at hqval
    have hqw : q + 1 < 2 ^ w := hqval.symm ▸ hqfit
    refine runs_seq_call_le hzero (vs := [a, k]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨a, k, rfl, by omega, hlow⟩
    · intro z mem₂ pos₂ hp₂
      obtain ⟨hm₂, hz⟩ := hp₂
      subst mem₂
      change z = (if intVal mem a h k = 0 then 1 else 0) at hz
      simp only [intVal_eq_zero_iff hlow, ← hr] at hz
      have hret (v : ℕ) (he : v = q + (if unsignedVal mem a h L % capacity h k = 0 then 0 else 1)) :
          (initDepthEndpointContract w h).post [a, L, k] mem v mem :=
        ⟨rfl, he.trans (by simp only [List.getD_cons_zero, List.getD_cons_succ, hq, hqval])⟩
      wram_step
      · have hz' : z ≠ 0 := by simpa using hcond
        have hrem : unsignedVal mem a h L % capacity h k = 0 := by
          by_contra h
          exact hz' (by simpa only [ite_eq_right h] using hz)
        refine runs_ret_le (v := q) (by eval_expr) (hret q (by simp [hrem])) ?_
        simp [packWordContract, isZeroContract, initDepthEndpointContract, argsSize]
        omega
      · have hz' : z = 0 := by simpa using hcond
        have hrem : unsignedVal mem a h L % capacity h k ≠ 0 := by
          intro h
          simp [h, hz'] at hz
        refine runs_ret_le (v := q + 1) (by eval_expr) (hret (q + 1) (by simp [hrem])) ?_
        simp [packWordContract, isZeroContract, initDepthEndpointContract, argsSize]
        omega

/-- Round the approximation stored below register `99` and prepare the
unit-scale scan. The same rounded value serves both checks once the
error bound separates the approximation from the cutoffs. -/
@[expose] def initRoundDepthLog (roundEntry h : ℕ) : Stmt :=
  .call 107 roundEntry [.bin .sub (.reg 99) (.reg 67), .reg 67,
    .bin .div (.reg 68) (.const h)] ;;
  .assign 108 (.reg 107) ;;
  .assign 111 (.const 1)

/-- The rounding handoff installs both endpoints without changing the
logarithm block or any other registers. -/
theorem initRoundDepthLog_runs {w h entry L P heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hround : MeetsContract w p entry (initDepthEndpointContract w h))
    (hw : 1 < 2 ^ w) (hhw : h < 2 ^ w)
    (hL : st.regs 67 = L) (hP : st.regs 68 = P) (hheap : st.regs 99 = heap)
    (hfit : heap < 2 ^ w) (hPfit : P < 2 ^ w) (hlen : L ≤ heap) (hfrac : P / h ≤ L)
    (hv : Valid st.mem (heap - L) h L)
    (hq : unsignedVal st.mem (heap - L) h L / capacity h (P / h) + 1 < 2 ^ w) :
    let x := unsignedVal st.mem (heap - L) h L
    let s := capacity h (P / h)
    let rounded := x / s + (if x % s = 0 then 0 else 1)
    ∃ out cost, Runs w p ω (initRoundDepthLog entry h) st .normal out cost ∧
      out.regs 107 = rounded ∧ out.regs 108 = rounded ∧ out.regs 111 = 1 ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 107 → r ≠ 108 → r ≠ 111 → out.regs r = st.regs r) ∧
      cost ≤ 25 * L + 65 := by
  dsimp only
  have hLfit : L < 2 ^ w := hlen.trans_lt hfit
  have hkfit : P / h < 2 ^ w := (Nat.div_le_self _ _).trans_lt hPfit
  have ha : heap - L < 2 ^ w := by omega
  have hargs : evalArgs w st [.bin .sub (.reg 99) (.reg 67), .reg 67,
      .bin .div (.reg 68) (.const h)] = some [heap - L, L, P / h] := by
    simp [evalArgs, Expr.eval, BinOp.eval, hL, hP, hheap, hhw, ha, hkfit]
  obtain ⟨mid, c, v, hc, hp, hr, hf, hcost⟩ :=
    runs_call_of_meetsContract (r := 107) hround hargs (by wram_words)
      ⟨heap - L, L, P / h, rfl, hfrac, by omega, hv, hq⟩ ω
  obtain ⟨hm, hv⟩ := hp
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hv
  let next := {mid with regs := Function.update mid.regs 108 v}
  let out := {next with regs := Function.update next.regs 111 1}
  have h₁ : Runs w p ω (.assign 108 (.reg 107)) mid .normal next 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hr], rfl, rfl, rfl⟩
  have h₂ : Runs w p ω (.assign 111 (.const 1)) next .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hw], rfl, rfl, rfl⟩
  refine ⟨out, c + 6, runs_seq_iff.mpr (Or.inr ⟨mid, c, 5, hc,
    runs_seq_iff.mpr (Or.inr ⟨next, 2, 2, h₁, h₂, rfl⟩), by omega⟩),
    ?_, ?_, ?_, hm, ?_, ?_⟩
  · simpa [out, next, hr] using hv
  · simpa [out, next] using hv
  · simp [out]
  · intro r h107 h108 h111
    simpa [out, next, h108, h111] using hf r h107
  · simp [initDepthEndpointContract, argsSize, Expr.size_bin, Expr.size_reg, Expr.size_const] at hcost
    omega

/-- An approximation separated from both adjacent cutoffs can supply
both comparisons. The lower gap also ensures the stored value is
nonnegative, so its unsigned decoding is valid. -/
theorem initDepthApproximation_separates {mem : ℕ → ℕ} {a h L P depth exponent : ℕ}
    {value error : ℝ} (hv : Valid mem a h L) (hP : h ∣ P)
    (happrox : |fixVal mem a h L P - value| ≤ error)
    (hprev : (((depth - 1) ^ exponent : ℕ) : ℝ) + error < value)
    (hnext : value + error ≤ ((depth ^ exponent : ℕ) : ℝ)) :
    let x := unsignedVal mem a h L
    let scale := capacity h (P / h)
    (depth - 1) ^ exponent * scale < x ∧ x ≤ depth ^ exponent * scale := by
  dsimp only
  obtain ⟨hlo, hhi⟩ := abs_le.mp happrox
  have hpos : 0 < fixVal mem a h L P := by
    linarith only [hlo, hprev, (show (0 : ℝ) ≤ (((depth - 1) ^ exponent : ℕ) : ℝ) by positivity)]
  have hiR : 0 ≤ (intVal mem a h L : ℝ) := by
    unfold fixVal at hpos
    exact ((div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ P)).mp hpos).le
  have hi : 0 ≤ intVal mem a h L := by exact_mod_cast hiR
  have hu : (unsignedVal mem a h L : ℤ) = intVal mem a h L := by
    rw [unsignedVal_nonnegative_abs hv (not_lt.mpr hi), Int.natCast_natAbs, abs_of_nonneg hi]
  have hs : capacity h (P / h) = 2 ^ P := by
    rw [capacity_eq_two_pow, Nat.mul_div_cancel' hP]
  have hval : fixVal mem a h L P = (unsignedVal mem a h L : ℝ) / (capacity h (P / h) : ℕ) := by
    rw [fixVal, hs, Nat.cast_pow, Nat.cast_ofNat, ← hu]
    rfl
  rw [hval] at hlo hhi
  exact initDepth_separation_of_error (capacity_pos _ _) (by linarith only [hlo])
    (by linarith only [hhi]) hprev hnext

/-- A separated logarithm approximation installs the unscaled comparisons
that the depth scan checks. -/
theorem initRoundDepthLog_certified_runs {w h entry L P heap depth exponent : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {value error : ℝ}
    (hround : MeetsContract w p entry (initDepthEndpointContract w h))
    (hw : 1 < 2 ^ w) (hhw : h < 2 ^ w)
    (hL : st.regs 67 = L) (hP : st.regs 68 = P) (hheap : st.regs 99 = heap)
    (hfit : heap < 2 ^ w) (hPfit : P < 2 ^ w) (hlen : L ≤ heap) (hfrac : P / h ≤ L)
    (hv : Valid st.mem (heap - L) h L) (halign : h ∣ P)
    (happrox : |fixVal st.mem (heap - L) h L P - value| ≤ error)
    (hprev : (((depth - 1) ^ exponent : ℕ) : ℝ) + error < value)
    (hnext : value + error ≤ ((depth ^ exponent : ℕ) : ℝ))
    (hcutoff : depth ^ exponent + 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω (initRoundDepthLog entry h) st .normal out cost ∧
      (depth - 1) ^ exponent < out.regs 107 ∧ out.regs 108 ≤ depth ^ exponent ∧
      out.regs 107 = out.regs 108 ∧ out.regs 111 = 1 ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 107 → r ≠ 108 → r ≠ 111 → out.regs r = st.regs r) ∧
      cost ≤ 25 * L + 65 := by
  obtain ⟨hl, hu⟩ := initDepthApproximation_separates hv halign happrox hprev hnext
  have hs := capacity_pos h (P / h)
  have hq : unsignedVal st.mem (heap - L) h L / capacity h (P / h) ≤ depth ^ exponent :=
    (Nat.div_le_iff_le_mul_add_pred hs).mpr
    (hu.trans (by rw [Nat.mul_comm (capacity h (P / h))]; exact Nat.le_add_right _ _))
  obtain ⟨out, cost, hr, hlo, hhi, hscale, hm, hk, hc⟩ :=
    initRoundDepthLog_runs hround hw hhw hL hP hheap hfit hPfit hlen hfrac hv
      ((Nat.add_le_add_right hq 1).trans_lt hcutoff)
  refine ⟨out, cost, hr, ?_, ?_, hlo.trans hhi.symm, hscale, hm, hk, hc⟩
  · rw [hlo]
    exact Nat.lt_of_not_ge fun h => hl.not_ge ((initDepth_endpoint_le_iff hs).mp h)
  · rw [hhi]
    exact (initDepth_endpoint_le_iff hs).mpr hu

/-- A word loaded above a zero fractional block represents that word
exactly at the aligned fixed-point precision. -/
theorem initDepthLog_aligned_input {mem : ℕ → ℕ} {a h L P value : ℕ}
    (halign : h ∣ P) (hfrac : P / h ≤ L)
    (hzero : ∀ i < P / h, mem (a + i) = 0)
    (hvalue : unsignedVal mem (a + P / h) h (L - P / h) = value)
    (hfit : 2 * (value * capacity h (P / h)) < capacity h L) :
    intVal mem a h L = (value : ℤ) * (2 : ℤ) ^ P ∧
      fixVal mem a h L P = value := by
  have hu : unsignedVal mem a h L = value * capacity h (P / h) := by
    conv_lhs => rw [show L = P / h + (L - P / h) by omega, unsignedVal_split]
    rw [unsignedVal_zero hzero, zero_add, hvalue, Nat.mul_comm]
  have hs : capacity h (P / h) = 2 ^ P := by
    rw [capacity_eq_two_pow, Nat.mul_div_cancel' halign]
  have hi : intVal mem a h L = (value : ℤ) * (2 : ℤ) ^ P := by
    rw [intVal, hu, signedVal, ite_eq_right (not_le.mpr hfit), sub_zero, hs]
    push_cast
    rfl
  refine ⟨hi, ?_⟩
  rw [fixVal, hi]
  push_cast
  exact mul_div_cancel_right₀ _ (by positivity)

/-- Leave the fractional limbs untouched and write the word into the
upper limbs of the aligned logarithm input. -/
@[expose] def loadInitDepthLogInput (load dst valueReg baseReg h : ℕ) : Stmt :=
  .call dst load [.reg valueReg, .bin .sub (.reg 67) (.bin .div (.reg 68) (.const h)),
    .bin .add (.reg baseReg) (.bin .div (.reg 68) (.const h))]

/-- The input block encodes the supplied word at the requested precision,
with the frame and zero suffix supplied by the loader. -/
theorem loadInitDepthLogInput_runs {w h entry dst valueReg baseReg a L P value : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p entry (loadSmallContract w h))
    (hhw : h < 2 ^ w) (hL : st.regs 67 = L) (hP : st.regs 68 = P)
    (ha : st.regs baseReg = a) (hv : st.regs valueReg = value) (hvword : value < 2 ^ w)
    (hroom : a + L < 2 ^ w) (hfrac : P / h ≤ L) (halign : h ∣ P)
    (hz : ZeroFrom st.mem a) (hvalue : value < capacity h (L - P / h))
    (hfit : 2 * (value * capacity h (P / h)) < capacity h L) :
    ∃ out cost, Runs w p ω (loadInitDepthLogInput entry dst valueReg baseReg h) st .normal out cost ∧
      out.regs dst = a + L ∧ Valid out.mem a h L ∧
      intVal out.mem a h L = (value : ℤ) * (2 : ℤ) ^ P ∧ fixVal out.mem a h L P = value ∧
      (∀ x < a, out.mem x = st.mem x) ∧ ZeroFrom out.mem (a + L) ∧
      (∀ r ≠ dst, out.regs r = st.regs r) ∧ cost ≤ 23 * L + 18 := by
  let k := P / h
  change k ≤ L at hfrac
  have hdiff : L - k ≤ L := Nat.sub_le _ _
  have hkw : P / h < 2 ^ w := by omega
  have hargs : evalArgs w st [.reg valueReg, .bin .sub (.reg 67) (.bin .div (.reg 68) (.const h)),
      .bin .add (.reg baseReg) (.bin .div (.reg 68) (.const h))] = some [value, L - k, a + k] := by
    have htail : L - k < 2 ^ w := by omega
    have hbase : a + k < 2 ^ w := by omega
    simp [evalArgs, Expr.eval, BinOp.eval, hL, hP, ha, hv, hhw, hkw, htail, hbase, k]
  have hsum : a + k + (L - k) = a + L := by omega
  have hpre : (loadSmallContract w h).pre [value, L - k, a + k] st.mem := by
    exact ⟨⟨value, L - k, a + k, rfl⟩, fun x hx => hz x ((Nat.le_add_right a k).trans hx), by change a + k + (L - k) < 2 ^ w; rwa [hsum]⟩
  obtain ⟨out, cost, ret, hr, hpost, hret, hf, hc⟩ :=
    runs_call_of_meetsContract (r := dst) hload hargs (by wram_words) hpre ω
  change ret = a + k + (L - k) ∧ a + k ≤ ret ∧ ret ≤ a + k + (L - k) ∧
    (∀ x < a + k, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
    ListAt out.mem (a + k) (digits h (L - k) value) at hpost
  obtain ⟨hr', _, _, hframe, hzero, hdigits⟩ := hpost
  rw [hsum] at hr'
  obtain ⟨hvalid, hu, _⟩ := loadSmall_value hdigits
  have hz' (i : ℕ) (hi : i < k) : out.mem (a + i) = 0 :=
    (hframe _ (by omega)).trans (hz _ (by omega))
  obtain ⟨hi, hx⟩ := initDepthLog_aligned_input halign hfrac hz'
    (hu.trans (Nat.mod_eq_of_lt hvalue)) hfit
  refine ⟨out, cost, hr, hret.trans hr', ?_, hi, hx,
    fun x hx => hframe x (hx.trans_le (Nat.le_add_right a k)), hr' ▸ hzero, hf, ?_⟩
  · intro i hi
    by_cases hk : i < k
    · rw [hz' i hk]; exact base_pos h
    · have h := hvalid (i - k) (by omega)
      rwa [show a + k + (i - k) = a + i by omega] at h
  · simp [loadSmallContract, heapContract, argsSize, Expr.size_bin, Expr.size_reg, Expr.size_const] at hc
    omega

/-- Load the logarithm argument and its fixed-point unit into consecutive blocks. -/
@[expose] def loadInitDepthLogPair (load h : ℕ) : Stmt :=
  loadInitDepthLogInput load 123 124 98 h ;;
  loadInitDepthLogInput load 125 126 123 h

/-- The two input blocks share the same aligned precision and preserve the
memory below the initial cursor. -/
theorem loadInitDepthLogPair_runs {w h load a L P value : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (loadSmallContract w h))
    (hhw : h < 2 ^ w) (hL : st.regs 67 = L) (hP : st.regs 68 = P)
    (ha : st.regs 98 = a) (hv : st.regs 124 = value) (hone : st.regs 126 = 1)
    (hvaluePos : 1 ≤ value) (hvword : value < 2 ^ w)
    (hroom : a + L + L < 2 ^ w) (hfrac : P / h ≤ L) (halign : h ∣ P)
    (hz : ZeroFrom st.mem a) (hvalue : value < capacity h (L - P / h))
    (hfit : 2 * (value * capacity h (P / h)) < capacity h L) :
    ∃ out cost, Runs w p ω (loadInitDepthLogPair load h) st .normal out cost ∧
      out.regs 123 = a + L ∧ out.regs 125 = a + L + L ∧
      Valid out.mem a h L ∧ Valid out.mem (a + L) h L ∧
      fixVal out.mem a h L P = value ∧ intVal out.mem (a + L) h L = (2 : ℤ) ^ P ∧
      (∀ x < a, out.mem x = st.mem x) ∧ ZeroFrom out.mem (a + L + L) ∧
      (∀ r, r ≠ 123 → r ≠ 125 → out.regs r = st.regs r) ∧ cost ≤ 46 * L + 37 := by
  obtain ⟨mid, c, hr, hm, hvalid, _, hfix, hf, hz', hk, hc⟩ :=
    loadInitDepthLogInput_runs (dst := 123) hload hhw hL hP ha hv hvword
      (by omega) hfrac halign hz hvalue hfit
  have hunit : 2 * (1 * capacity h (P / h)) < capacity h L :=
    (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hvaluePos)).trans_lt hfit
  obtain ⟨out, d, hr', hret, huvalid, hu, _, hf', hz'', hk', hc'⟩ :=
    loadInitDepthLogInput_runs (dst := 125) hload hhw
      ((hk 67 (by decide)).trans hL) ((hk 68 (by decide)).trans hP)
      hm ((hk 126 (by decide)).trans hone) (hvaluePos.trans_lt hvword)
      hroom hfrac halign hz' (hvaluePos.trans_lt hvalue) hunit
  have hsame (i : ℕ) (hi : i < L) : out.mem (a + i) = mid.mem (a + i) :=
    hf' _ (Nat.add_lt_add_left hi a)
  refine ⟨out, c + d + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, hr', rfl⟩),
    (hk' 123 (by decide)).trans hm, hret, fun i hi => (hsame i hi).trans_lt (hvalid i hi),
    huvalid, ?_, by simpa only [Int.cast_ofNat_Int, Nat.cast_one, one_mul] using hu,
    fun x hx => (hf' x (hx.trans_le (Nat.le_add_right _ _))).trans (hf x hx),
    hz'', fun r h100 h102 => (hk' r h102).trans (hk r h100), by omega⟩
  unfold fixVal
  rw [intVal_congr hsame]
  exact hfix

/-- Compute a logarithm from the two aligned input blocks and return
the cursor above the approximation in register `99`. -/
@[expose] def computeInitDepthLogBlock (load log h : ℕ) : Stmt :=
  loadInitDepthLogPair load h ;;
  .call 99 log [.reg 98, .reg 123, .reg 67, .reg 68, .reg 127, .reg 125]

/-- The logarithm block is valid and approximates the logarithm of the input
word at the requested accuracy. -/
theorem computeInitDepthLogBlock_runs {w h load log a L P E q value : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (loadSmallContract w h))
    (hlog : MeetsContract w p log (logarithmContract w h q))
    (hhw : h < 2 ^ w) (hL : st.regs 67 = L) (hP : st.regs 68 = P)
    (hE : st.regs 127 = E) (ha : st.regs 98 = a) (hv : st.regs 124 = value)
    (hone : st.regs 126 = 1) (hvaluePos : 1 ≤ value) (hvword : value < 2 ^ w)
    (hPword : P < 2 ^ w) (hEword : E < 2 ^ w)
    (hroom : a + L + L + logarithmSpace L P E < 2 ^ w)
    (hfrac : P / h ≤ L) (halign : h ∣ P) (hz : ZeroFrom st.mem a)
    (hvalue : value < capacity h (L - P / h))
    (hfit : 2 * (value * capacity h (P / h)) < capacity h L)
    (hacc : q + E + 10 ≤ P) (hcap : P + E + 4 ≤ h * L)
    (hprec : 2 * P + 9 < 2 ^ w) (hrange : value ≤ 2 ^ E) :
    ∃ out cost ret, Runs w p ω (computeInitDepthLogBlock load log h) st .normal out cost ∧
      out.regs 99 = ret ∧ a + L + L ≤ ret ∧ ret < 2 ^ w ∧
      ret ≤ a + L + L + logarithmSpace L P E ∧
      Valid out.mem (ret - L) h L ∧
      |fixVal out.mem (ret - L) h L P - Real.log (value : ℝ)| ≤ 1 / (2 : ℝ) ^ q ∧
      (∀ x < a, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
      (∀ r, r ≠ 99 → r ≠ 123 → r ≠ 125 → out.regs r = st.regs r) ∧
      cost ≤ 46 * L + logarithmCost L P E + 45 := by
  obtain ⟨mid, c, hr, h100, h102, hva, hvone, hxa, hxone, hf, hz', hk, hc⟩ :=
    loadInitDepthLogPair_runs hload hhw hL hP ha hv hone hvaluePos hvword
      (by omega) hfrac halign hz hvalue hfit
  let args := [a, a + L, L, P, E, a + L + L]
  have hargs : evalArgs w mid [.reg 98, .reg 123, .reg 67, .reg 68, .reg 127, .reg 125] = some args := by
    simp [evalArgs, Expr.eval, args, h100, h102, (hk 98 (by decide) (by decide)).trans ha,
      (hk 67 (by decide) (by decide)).trans hL, (hk 68 (by decide) (by decide)).trans hP,
      (hk 127 (by decide) (by decide)).trans hE]
  have hpre : (logarithmContract w h q).pre args mid.mem := by
    refine ⟨⟨a, a + L, L, P, E, a + L + L, rfl, halign, hacc, hcap, hprec, by omega,
      le_rfl, hva, hvone, hxone, ?_, ?_⟩, hz', hroom⟩
    · rw [hxa]
      exact (div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)).trans
        (by exact_mod_cast hvaluePos)
    · rw [hxa]
      exact_mod_cast hrange
  obtain ⟨out, d, ret, hr', hp, hret, hk', hd⟩ :=
    runs_call_of_meetsContract (r := 99) hlog hargs (by dsimp [args]; wram_words) hpre ω
  obtain ⟨⟨hlo, hhi, hf', hz'', _⟩, hvalid, herror⟩ := hp
  change a + L + L ≤ ret at hlo
  change ret ≤ a + L + L + logarithmSpace L P E at hhi
  change |fixVal out.mem (ret - L) h L P - Real.log (fixVal mid.mem a h L P)| ≤ _ at herror
  rw [hxa] at herror
  refine ⟨out, c + d + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, hr', rfl⟩),
    hret, hlo, hhi.trans_lt hroom, hhi, hvalid, herror, ?_, hz'',
    fun r h99 h100' h102' => (hk' r h99).trans (hk r h100' h102'), ?_⟩
  · intro x hx
    exact (hf' x (show x < a + L + L by omega)).trans (hf x hx)
  · change d ≤ argsSize [Expr.reg 98, .reg 123, .reg 67, .reg 68, .reg 127, .reg 125] +
      logarithmCost L P E + 1 at hd
    simp [argsSize, Expr.size_reg] at hd
    omega

/-- Form the positive logarithm input and compute its range from its bit length. -/
@[expose] def stageInitDepthLogBlock (sizeReg bits : ℕ) : Stmt :=
  .assign 124 (.bin .add (.reg sizeReg) (.const 2)) ;;
  .assign 126 (.const 1) ;;
  .call 127 bits [.reg 124]

/-- The runtime input and its range are available without forming the fixed-point scale. -/
theorem stageInitDepthLogBlock_runs {w sizeReg bits M : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hM : st.regs sizeReg = M) (hw : M + 2 < 2 ^ w) :
    ∃ out cost, Runs w p ω (stageInitDepthLogBlock sizeReg bits) st .normal out cost ∧
      out.regs 124 = M + 2 ∧ out.regs 126 = 1 ∧ out.regs 127 = (M + 2).size ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 124 → r ≠ 126 → r ≠ 127 → out.regs r = st.regs r) ∧
      cost ≤ 14 * (M + 2).size + 16 := by
  let mid := {st with regs := Function.update st.regs 124 (M + 2)}
  let ready := {mid with regs := Function.update mid.regs 126 1}
  have hr : Runs w p ω (.assign 124 (.bin .add (.reg sizeReg) (.const 2))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hM, hw, show 2 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have hs : Runs w p ω (.assign 126 (.const 1)) mid .normal ready 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, show 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hargs : evalArgs w ready [.reg 124] = some [M + 2] := by
    simp [evalArgs, Expr.eval, ready, mid]
  obtain ⟨out, c, ret, hc, ⟨hm, hv⟩, hret, hf, hcost⟩ :=
    runs_call_of_meetsContract (r := 127) hbits hargs (by simpa using hw) ⟨_, rfl⟩ ω
  change ret = (M + 2).size at hv
  change c ≤ 1 + (14 * (M + 2).size + 6) + 1 at hcost
  refine ⟨out, c + 8, runs_seq_iff.mpr (Or.inr ⟨mid, 4, c + 3, hr,
    runs_seq_iff.mpr (Or.inr ⟨ready, 2, c, hs, hc, by omega⟩), by omega⟩),
    (hf 124 (by decide)).trans (by simp [ready, mid]), (hf 126 (by decide)).trans (by simp [ready]),
    hret.trans hv, hm, ?_, by omega⟩
  intro r h101 h103 h104
  exact (hf r h104).trans (by simp [ready, mid, h101, h103])

/-- Compute the depth logarithm directly from the runtime edge count. -/
@[expose] def computeInitDepthLogFromSize (sizeReg bits load log h : ℕ) : Stmt :=
  stageInitDepthLogBlock sizeReg bits ;; computeInitDepthLogBlock load log h

/-- Computing the logarithm of the padded edge count leaves a certified
multiword approximation above the input blocks. -/
theorem computeInitDepthLogFromSize_runs {w h sizeReg bits load log a L P q M : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (loadSmallContract w h))
    (hlog : MeetsContract w p log (logarithmContract w h q))
    (hM : st.regs sizeReg = M) (hMw : M + 2 < 2 ^ w)
    (hhw : h < 2 ^ w) (hL : st.regs 67 = L) (hP : st.regs 68 = P)
    (ha : st.regs 98 = a) (hPword : P < 2 ^ w)
    (hroom : a + L + L + logarithmSpace L P (M + 2).size < 2 ^ w)
    (hfrac : P / h ≤ L) (halign : h ∣ P) (hz : ZeroFrom st.mem a)
    (hvalue : M + 2 < capacity h (L - P / h))
    (hfit : 2 * ((M + 2) * capacity h (P / h)) < capacity h L)
    (hacc : q + (M + 2).size + 10 ≤ P) (hcap : P + (M + 2).size + 4 ≤ h * L)
    (hprec : 2 * P + 9 < 2 ^ w) :
    ∃ out cost ret, Runs w p ω (computeInitDepthLogFromSize sizeReg bits load log h) st .normal out cost ∧
      out.regs 99 = ret ∧ a + L + L ≤ ret ∧ ret < 2 ^ w ∧
      Valid out.mem (ret - L) h L ∧
      |fixVal out.mem (ret - L) h L P - Real.log ((M : ℝ) + 2)| ≤ 1 / (2 : ℝ) ^ q ∧
      (∀ x < a, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 99, out.regs r = st.regs r) ∧
      cost ≤ 46 * L + logarithmCost L P (M + 2).size + 14 * (M + 2).size + 62 := by
  obtain ⟨mid, c, hr, hv, hone, hE, hm, hf, hc⟩ := stageInitDepthLogBlock_runs hbits hM hMw
  have hEword : (M + 2).size < 2 ^ w := (Nat.size_le.mpr (Nat.lt_pow_self (by decide : 1 < (2 : ℕ)))).trans_lt hMw
  obtain ⟨out, d, ret, hr', h99, hlo, hhi, _, hvalid, herror, hf', hz', hk, hd⟩ :=
    computeInitDepthLogBlock_runs hload hlog hhw
      ((hf 67 (by decide) (by decide) (by decide)).trans hL)
      ((hf 68 (by decide) (by decide) (by decide)).trans hP) hE
      ((hf 98 (by decide) (by decide) (by decide)).trans ha) hv hone (by omega) hMw
      hPword hEword hroom hfrac halign (hm.symm ▸ hz) hvalue hfit hacc hcap hprec
      (Nat.lt_size_self _).le
  refine ⟨out, c + d + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, hr', rfl⟩),
    h99, hlo, hhi, hvalid, ?_, fun x hx => (hf' x hx).trans (congrFun hm x),
    hz', fun r h => (hk r (by omega) (by omega) (by omega)).trans
      (hf r (by omega) (by omega) (by omega)), by omega⟩
  simpa only [Nat.cast_add, Nat.cast_ofNat] using herror

/-- Align the working precision to whole limbs and reserve enough limbs
for the logarithm range and guard bits. -/
theorem initDepthLog_workspace_bounds {h q E : ℕ} (hh : 0 < h) :
    let P := h * (q + E + 10)
    let L := P + E + 4
    h ∣ P ∧ P / h ≤ L ∧ q + E + 10 ≤ P ∧ P + E + 4 ≤ h * L ∧
      (∀ value ≤ 2 ^ E, value < capacity h (L - P / h) ∧
        2 * (value * capacity h (P / h)) < capacity h L) := by
  dsimp only
  let P := h * (q + E + 10)
  let L := P + E + 4
  have hh' : 1 ≤ h := hh
  have hP : q + E + 10 ≤ P := by
    simpa only [one_mul, P] using Nat.mul_le_mul_right (q + E + 10) hh'
  have hk : P / h ≤ P := Nat.div_le_self _ _
  have hl : P / h ≤ L := hk.trans (by dsimp [L]; omega)
  have hcap : L ≤ h * L := by simpa only [one_mul] using Nat.mul_le_mul_right L hh'
  refine ⟨⟨_, rfl⟩, hl, hP, hcap, fun value hvalue => ?_⟩
  have htail : E + 4 ≤ L - P / h := by dsimp [L]; omega
  have htail' : E + 4 ≤ h * (L - P / h) := htail.trans (by
    simpa only [one_mul] using Nat.mul_le_mul_right (L - P / h) hh')
  have hsmall : 2 * value < capacity h (L - P / h) := by
    rw [capacity_eq_two_pow]
    calc
      2 * value ≤ 2 * 2 ^ E := Nat.mul_le_mul_left _ hvalue
      _ = 2 ^ (E + 1) := by rw [pow_succ, Nat.mul_comm]
      _ < 2 ^ (h * (L - P / h)) := Nat.pow_lt_pow_right (by decide) (by omega)
  refine ⟨(show value ≤ 2 * value by omega).trans_lt hsmall, ?_⟩
  calc
    2 * (value * capacity h (P / h)) = (2 * value) * capacity h (P / h) := by rw [mul_assoc]
    _ < capacity h (L - P / h) * capacity h (P / h) :=
      Nat.mul_lt_mul_of_pos_right hsmall (capacity_pos _ _)
    _ = capacity h L := by rw [← capacity_add, Nat.sub_add_cancel hl]

/-- Use the range in register `127` and accuracy in register `112`
to set the working precision and limb count. -/
@[expose] def stageInitDepthLogWorkspace (h : ℕ) : Stmt :=
  .assign 68 (.bin .mul (.const h) (.bin .add (.bin .add (.reg 112) (.reg 127)) (.const 10))) ;;
  .assign 67 (.bin .add (.bin .add (.reg 68) (.reg 127)) (.const 4))

/-- The workspace registers hold the dimensions of the aligned logarithm block. -/
theorem stageInitDepthLogWorkspace_runs {w h q E : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hh : 0 < h) (hhw : h < 2 ^ w) (hq : st.regs 112 = q) (hE : st.regs 127 = E)
    (hword : h * (q + E + 10) + E + 4 < 2 ^ w) :
    let P := h * (q + E + 10)
    let L := P + E + 4
    ∃ out, Runs w p ω (stageInitDepthLogWorkspace h) st .normal out 15 ∧
      out.regs 68 = P ∧ out.regs 67 = L ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 68 → r ≠ 67 → out.regs r = st.regs r) := by
  dsimp only
  let P := h * (q + E + 10)
  let L := P + E + 4
  have hP : P < 2 ^ w := by change P + E + 4 < 2 ^ w at hword; omega
  have hL : L < 2 ^ w := hword
  have hbase : q + E + 10 ≤ P := by
    simpa only [one_mul, P] using Nat.mul_le_mul_right (q + E + 10) (show 1 ≤ h from hh)
  have h₁ : q + E < 2 ^ w := by omega
  have h₂ : q + E + 10 < 2 ^ w := by omega
  have h₃ : P + E < 2 ^ w := by change P + E + 4 < 2 ^ w at hword; omega
  have h₄ : 10 < 2 ^ w := by omega
  have h₅ : 4 < 2 ^ w := by omega
  let mid := {st with regs := Function.update st.regs 68 P}
  let out := {mid with regs := Function.update mid.regs 67 L}
  have hr : Runs w p ω
      (.assign 68 (.bin .mul (.const h) (.bin .add (.bin .add (.reg 112) (.reg 127)) (.const 10))))
      st .normal mid 8 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hq, hE, hhw, h₁, h₂, h₄, P, hP],
      rfl, rfl, rfl⟩
  have hs : Runs w p ω (.assign 67 (.bin .add (.bin .add (.reg 68) (.reg 127)) (.const 4)))
      mid .normal out 6 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, mid, hE, h₃, h₅, L, hL],
      rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 8, 6, hr, hs, rfl⟩),
    by simp [out, mid, P], by simp [out, L, P], rfl,
    fun r h68 h67 => by simp [out, mid, h68, h67]⟩

/-- Compute the sufficient accuracy from the runtime bit length. The
coefficient depends only on the fixed exponent of the depth formula. -/
@[expose] def stageInitDepthLogAccuracy (exponent : ℕ) : Stmt :=
  .assign 112 (.bin .add
    (.bin .mul (.const (38 * 2 ^ (exponent * 8))) (initDepthPower (.reg 127) 8))
    (.reg 127))

/-- The accuracy calculation fits whenever its result does. -/
theorem stageInitDepthLogAccuracy_runs {w exponent E : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hE : st.regs 127 = E) (he : 0 < E)
    (hword : 38 * (2 ^ exponent * E) ^ 8 + E < 2 ^ w) :
    ∃ out, Runs w p ω (stageInitDepthLogAccuracy exponent) st .normal out 22 ∧
      out.regs 112 = 38 * (2 ^ exponent * E) ^ 8 + E ∧ out.mem = st.mem ∧
      (∀ r ≠ 112, out.regs r = st.regs r) := by
  let coefficient := 38 * 2 ^ (exponent * 8)
  have hcoeff : 1 ≤ coefficient := by dsimp [coefficient]; exact Nat.succ_le_of_lt (by positivity)
  have hep : 1 ≤ E ^ 8 := Nat.one_le_pow _ _ he
  have hprod : coefficient * E ^ 8 = 38 * (2 ^ exponent * E) ^ 8 := by
    rw [mul_pow, ← pow_mul]
    simp [coefficient, mul_assoc]
  have hbound : coefficient * E ^ 8 < 2 ^ w := hprod.symm ▸ (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hword)
  have hcf : coefficient < 2 ^ w :=
    (Nat.le_mul_of_pos_right _ hep).trans_lt hbound
  have hpf : E ^ 8 < 2 ^ w :=
    (Nat.le_mul_of_pos_left _ hcoeff).trans_lt hbound
  have hw : 1 < 2 ^ w := by omega
  have hp := initDepthPower_eval (w := w) (st := st) (base := .reg 127)
    (by simp [Expr.eval, hE]) hw 8 hpf
  let out := {st with regs := Function.update st.regs 112 (38 * (2 ^ exponent * E) ^ 8 + E)}
  refine ⟨out, runs_assign_iff.mpr ⟨_, ?_, rfl, rfl, rfl⟩, by simp [out], rfl, ?_⟩
  · change Expr.eval w st (.bin .add
      (.bin .mul (.const coefficient) (initDepthPower (.reg 127) 8)) (.reg 127)) = _
    simp [Expr.eval, BinOp.eval, hcf, hp, hE, hprod, hword, show 38 * (2 ^ exponent * E) ^ 8 < 2 ^ w by omega]
  · intro r hr
    simp [out, hr]

/-- Set the input range, accuracy, and workspace dimensions from the runtime size. -/
@[expose] def prepareInitDepthLogWorkspace (sizeReg bits exponent h : ℕ) : Stmt :=
  stageInitDepthLogBlock sizeReg bits ;; stageInitDepthLogAccuracy exponent ;;
  stageInitDepthLogWorkspace h

/-- The runtime workspace preparation preserves memory and computes the
dimensions required by the logarithm procedure. -/
theorem prepareInitDepthLogWorkspace_runs {w sizeReg bits exponent h M : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hM : st.regs sizeReg = M) (hMw : M + 2 < 2 ^ w)
    (hh : 0 < h) (hhw : h < 2 ^ w) :
    let E := (M + 2).size
    let q := 38 * (2 ^ exponent * E) ^ 8 + E
    let P := h * (q + E + 10)
    let L := P + E + 4
    L < 2 ^ w →
    ∃ out cost, Runs w p ω (prepareInitDepthLogWorkspace sizeReg bits exponent h) st .normal out cost ∧
      out.regs 124 = M + 2 ∧ out.regs 126 = 1 ∧ out.regs 127 = E ∧
      out.regs 112 = q ∧ out.regs 68 = P ∧ out.regs 67 = L ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 124 → r ≠ 126 → r ≠ 127 → r ≠ 112 → r ≠ 68 → r ≠ 67 →
        out.regs r = st.regs r) ∧ cost ≤ 14 * E + 55 := by
  dsimp only
  intro hword
  let E := (M + 2).size
  let q := 38 * (2 ^ exponent * E) ^ 8 + E
  have hpos : 0 < E := Nat.lt_size.mpr (by norm_num : 2 ^ 0 ≤ M + 2)
  have hq : q < 2 ^ w := by
    have hp : q + E + 10 ≤ h * (q + E + 10) := by
      simpa only [one_mul] using Nat.mul_le_mul_right (q + E + 10) (show 1 ≤ h from hh)
    change h * (q + E + 10) + E + 4 < 2 ^ w at hword
    omega
  obtain ⟨mid, c, hr, hv, hu, he, hm, hf, hc⟩ := stageInitDepthLogBlock_runs hbits hM hMw
  obtain ⟨ready, hr', h112, hm', hf'⟩ := stageInitDepthLogAccuracy_runs he hpos hq
  obtain ⟨out, hr'', h68, h67, hm'', hf''⟩ :=
    stageInitDepthLogWorkspace_runs hh hhw h112 ((hf' 127 (by decide)).trans he) hword
  have keep r (h₁ : r ≠ 112) (h₂ : r ≠ 68) (h₃ : r ≠ 67) :=
    (hf'' r h₂ h₃).trans (hf' r h₁)
  refine ⟨out, c + 39, runs_seq_iff.mpr (Or.inr ⟨mid, c, 38, hr,
    runs_seq_iff.mpr (Or.inr ⟨ready, 22, 15, hr', hr'', rfl⟩), by omega⟩),
    (keep 124 (by decide) (by decide) (by decide)).trans hv,
    (keep 126 (by decide) (by decide) (by decide)).trans hu,
    (keep 127 (by decide) (by decide) (by decide)).trans he,
    (hf'' 112 (by decide) (by decide)).trans h112,
    h68, h67, hm''.trans (hm'.trans hm), ?_, by omega⟩
  intro r h101 h103 h104 h112' h68' h67'
  exact (keep r h112' h68' h67').trans (hf r h101 h103 h104)

/-- Compute a depth logarithm with workspace dimensions chosen from the
input size. -/
@[expose] def computeInitDepthLogRuntime (sizeReg bits load log exponent h : ℕ) : Stmt :=
  prepareInitDepthLogWorkspace sizeReg bits exponent h ;; computeInitDepthLogBlock load log h

/-- The runtime logarithm fits in the supplied address budget and uses
the precision needed by the depth comparisons. -/
theorem computeInitDepthLogRuntime_runs {w h sizeReg bits load log exponent M a : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (loadSmallContract w h))
    (hM : st.regs sizeReg = M) (hMw : M + 2 < 2 ^ w) (ha : st.regs 98 = a)
    (hh : 0 < h) (hhw : h < 2 ^ w) (hz : ZeroFrom st.mem a) :
    let E := (M + 2).size
    let q := 38 * (2 ^ exponent * E) ^ 8 + E
    let P := h * (q + E + 10)
    let L := P + E + 4
    MeetsContract w p log (logarithmContract w h q) →
    a + L + L + logarithmSpace L P E < 2 ^ w → 2 * P + 9 < 2 ^ w →
    ∃ out cost ret, Runs w p ω (computeInitDepthLogRuntime sizeReg bits load log exponent h)
        st .normal out cost ∧
      out.regs 99 = ret ∧ out.regs 67 = L ∧ out.regs 68 = P ∧
      a + L + L ≤ ret ∧ ret < 2 ^ w ∧
      ret ≤ a + L + L + logarithmSpace L P E ∧ Valid out.mem (ret - L) h L ∧
      |fixVal out.mem (ret - L) h L P - Real.log ((M : ℝ) + 2)| ≤ 1 / (2 : ℝ) ^ q ∧
      (∀ x < a, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 99, r ≠ 67 → r ≠ 68 → out.regs r = st.regs r) ∧
      (∀ r, (101 ≤ r ∧ r ≤ 104) ∨ 128 ≤ r → out.regs r = st.regs r) ∧
      cost ≤ 46 * L + logarithmCost L P E + 14 * E + 101 := by
  dsimp only
  intro hlog hroom hprec
  let E := (M + 2).size
  let q := 38 * (2 ^ exponent * E) ^ 8 + E
  let P := h * (q + E + 10)
  let L := P + E + 4
  change a + L + L + logarithmSpace L P E < 2 ^ w at hroom
  have hLw : L < 2 ^ w := by omega
  have hPw : P < 2 ^ w := by dsimp [L] at hLw; omega
  have hEw : E < 2 ^ w :=
    (Nat.size_le.mpr (Nat.lt_pow_self (by decide : 1 < (2 : ℕ)))).trans_lt hMw
  have hval : M + 2 ≤ 2 ^ E := (Nat.lt_size_self _).le
  obtain ⟨halign, hfrac, hacc, hcap, hbounds⟩ := initDepthLog_workspace_bounds (q := q) (E := E) hh
  obtain ⟨hv, hfit⟩ := hbounds (M + 2) hval
  obtain ⟨mid, c, hr, h101, h103, h104, _, h68, h67, hm, hf, hc⟩ :=
    prepareInitDepthLogWorkspace_runs (exponent := exponent) hbits hM hMw hh hhw hLw
  obtain ⟨out, d, ret, hr', h99, hlo, hhi, hroomRet, hvalid, herr, hf', hz', hk, hd⟩ :=
    computeInitDepthLogBlock_runs hload hlog hhw h67 h68 h104
      ((hf 98 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha)
      h101 h103 (by omega) hMw hPw hEw hroom hfrac halign (hm.symm ▸ hz)
      hv hfit hacc hcap hprec hval
  refine ⟨out, c + d + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, hr', rfl⟩),
    h99, (hk 67 (by decide) (by decide) (by decide)).trans h67,
    (hk 68 (by decide) (by decide) (by decide)).trans h68, hlo, hhi, hroomRet, hvalid,
    ?_, fun x hx => (hf' x hx).trans (congrFun hm x), hz', ?_, ?_, by omega⟩
  · simpa only [Nat.cast_add, Nat.cast_ofNat] using herr
  · intro r hr h67' h68'
    exact (hk r (by omega) (by omega) (by omega)).trans
      (hf r (by omega) (by omega) (by omega) (by omega) h68' h67')

  · intro r hr
    exact (hk r (by omega) (by omega) (by omega)).trans
      (hf r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))

/-- The workspace of the depth logarithm is cubic in a common bound on
the limb count, working precision, and input bit length. -/
theorem initDepthLog_space_le {L P E B : ℕ} (hB : 1 ≤ B)
    (hL : L ≤ B) (hP : P ≤ B) (hE : E ≤ B) :
    L + L + logarithmSpace L P E ≤ 1000 * B ^ 3 := by
  have hmono : L + L + logarithmSpace L P E ≤ B + B + logarithmSpace B B B := by
    unfold logarithmSpace rangeLogarithmSpace normalizedLogarithmSpace fixedDivideSpace
      logHornerSpace logHornerStepSpace integerDivideSpace unsignedDivideSpace
    gcongr
  have heq : B + B + logarithmSpace B B B = 10 * B ^ 3 + 181 * B ^ 2 + 342 * B + 32 := by
    unfold logarithmSpace rangeLogarithmSpace normalizedLogarithmSpace fixedDivideSpace
      logHornerSpace logHornerStepSpace integerDivideSpace unsignedDivideSpace
    ring
  rw [heq] at hmono
  have h₁ := Nat.le_self_pow (by decide : 3 ≠ 0) B
  have h₂ := Nat.pow_le_pow_right hB (by decide : 2 ≤ 3)
  have h₀ := Nat.one_le_pow 3 B hB
  exact hmono.trans (by omega)

/-- The logarithm and input preparation cost is cubic in a common bound
on the limb count, working precision, and input range. -/
theorem initDepthLog_cost_le {L P E B : ℕ} (hB : 1 ≤ B)
    (hL : L ≤ B) (hP : P ≤ B) (hE : E ≤ B) :
    71 * L + logarithmCost L P E + 14 * E ≤ 100000 * B ^ 3 := by
  have hmono : 71 * L + logarithmCost L P E + 14 * E ≤ 85 * B + logarithmCost B B B := by
    calc
      _ ≤ 71 * B + logarithmCost B B B + 14 * B := by
        unfold logarithmCost
        gcongr
      _ = _ := by ring
  have heq : 85 * B + logarithmCost B B B =
      1000 * B ^ 3 + 18400 * B ^ 2 + 41585 * B + 38000 := by
    unfold logarithmCost
    ring
  rw [heq] at hmono
  have h₁ := Nat.le_self_pow (by decide : 3 ≠ 0) B
  have h₂ := Nat.pow_le_pow_right hB (by decide : 2 ≤ 3)
  have h₀ := Nat.one_le_pow 3 B hB
  exact hmono.trans (by omega)

/-- At the selected accuracy the workspace is polynomial in the bit
length. This bound also covers the guard used by the logarithm series. -/
theorem initDepthLog_runtime_budget {h exponent E : ℕ} (hE : 1 ≤ E) :
    let q := 38 * (2 ^ exponent * E) ^ 8 + E
    let P := h * (q + E + 10)
    let L := P + E + 4
    let B := (h * (38 * (2 ^ exponent) ^ 8 + 12) + 5) * E ^ 8
    L + L + logarithmSpace L P E ≤ 1000 * B ^ 3 ∧
      2 * P + 9 ≤ 11 * B ∧
      71 * L + logarithmCost L P E + 14 * E ≤ 100000 * B ^ 3 := by
  dsimp only
  let A := 38 * (2 ^ exponent) ^ 8
  let P := h * (38 * (2 ^ exponent * E) ^ 8 + E + E + 10)
  let L := P + E + 4
  let B := (h * (A + 12) + 5) * E ^ 8
  have hpow : 1 ≤ E ^ 8 := Nat.one_le_pow _ _ hE
  have hle : E ≤ E ^ 8 := Nat.le_self_pow (by decide) _
  have hp : P ≤ h * ((A + 12) * E ^ 8) := by
    unfold P
    apply Nat.mul_le_mul_left
    rw [mul_pow]
    calc
      _ = A * E ^ 8 + E + E + 10 := by unfold A; ring
      _ ≤ A * E ^ 8 + E ^ 8 + E ^ 8 + 10 * E ^ 8 := by omega
      _ = _ := by ring
  have hL : L ≤ B := by
    unfold L B
    calc
      P + E + 4 ≤ h * ((A + 12) * E ^ 8) + E ^ 8 + 4 * E ^ 8 := by omega
      _ = _ := by ring
  have hP : P ≤ B := (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hL)
  have hE' : E ≤ B := (Nat.le_add_left _ _).trans ((Nat.le_add_right _ _).trans hL)
  have hB : 1 ≤ B := hE.trans hE'
  exact ⟨initDepthLog_space_le hB hL hP hE', by change 2 * P + 9 ≤ 11 * B; omega,
    initDepthLog_cost_le hB hL hP hE'⟩

/-- A power bound on the current cursor and the bit length gives a power
bound on the cursor after allocating the depth logarithm workspace. -/
theorem initDepthLog_runtime_address_bound {h exponent E a base cursorDegree bitsDegree coefficientDegree : ℕ}
    (hbase : 2 ≤ base) (hE : 1 ≤ E) (hbits : E ≤ base ^ bitsDegree)
    (ha : a ≤ base ^ cursorDegree)
    (hcoeff : h * (38 * (2 ^ exponent) ^ 8 + 12) + 5 ≤ base ^ coefficientDegree) :
    let q := 38 * (2 ^ exponent * E) ^ 8 + E
    let P := h * (q + E + 10)
    let L := P + E + 4
    let degree := 10 + 3 * (coefficientDegree + 8 * bitsDegree)
    a + L + L + logarithmSpace L P E ≤ base ^ (max cursorDegree degree + 1) := by
  dsimp only
  let B := (h * (38 * (2 ^ exponent) ^ 8 + 12) + 5) * E ^ 8
  let degree := 10 + 3 * (coefficientDegree + 8 * bitsDegree)
  obtain ⟨hspace, _, _⟩ := initDepthLog_runtime_budget (h := h) (exponent := exponent) hE
  have h8 : E ^ 8 ≤ base ^ (8 * bitsDegree) := by
    rw [Nat.mul_comm 8, pow_mul]
    exact Nat.pow_le_pow_left hbits _
  have hB : B ≤ base ^ (coefficientDegree + 8 * bitsDegree) := by
    rw [pow_add]
    exact Nat.mul_le_mul hcoeff h8
  have h1000 : 1000 ≤ base ^ 10 :=
    (by decide : 1000 ≤ 2 ^ 10).trans (Nat.pow_le_pow_left hbase _)
  have htotal : 1000 * B ^ 3 ≤ base ^ degree := by
    unfold degree
    rw [pow_add, Nat.mul_comm 3, pow_mul]
    exact Nat.mul_le_mul h1000 (Nat.pow_le_pow_left hB _)
  calc
    _ ≤ a + 1000 * B ^ 3 := by simpa only [Nat.add_assoc] using Nat.add_le_add_left hspace a
    _ ≤ base ^ cursorDegree + base ^ degree := Nat.add_le_add ha htotal
    _ ≤ base ^ max cursorDegree degree + base ^ max cursorDegree degree :=
      Nat.add_le_add (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
        (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
    _ ≤ base ^ (max cursorDegree degree + 1) := by
      rw [pow_succ, ← Nat.mul_two]
      exact Nat.mul_le_mul_left _ hbase

/-- The usual solver word-size formula covers the depth logarithm once
its multiplier covers the workspace degree. The series guard fits in
the same budget because it is smaller than the two input blocks. -/
theorem initDepthLog_runtime_word_budget
    {h exponent E a cursorDegree bitsDegree coefficientDegree multiplier : ℕ}
    (input : List ℕ) (hE : 1 ≤ E) :
    let base := input.length + input.foldr max 0 + 2
    let degree := 10 + 3 * (coefficientDegree + 8 * bitsDegree)
    E ≤ base ^ bitsDegree →
    a ≤ base ^ cursorDegree →
    h * (38 * (2 ^ exponent) ^ 8 + 12) + 5 ≤ base ^ coefficientDegree →
    max cursorDegree degree + 1 ≤ multiplier →
    let q := 38 * (2 ^ exponent * E) ^ 8 + E
    let P := h * (q + E + 10)
    let L := P + E + 4
    a + L + L + logarithmSpace L P E < 2 ^ wordSize multiplier input ∧
      2 * P + 9 < 2 ^ wordSize multiplier input := by
  dsimp only
  intro hbits ha hc hm
  let base := input.length + input.foldr max 0 + 2
  have hb : 2 ≤ base := by unfold base; omega
  have hm' : 1 ≤ multiplier := by omega
  have hspace := initDepthLog_runtime_address_bound hb hE hbits ha hc
  have hword := (hspace.trans (Nat.pow_le_pow_right (by omega : 0 < base) hm)).trans_lt
    (pow_lt_two_pow_wordSize hm' input)
  exact ⟨hword, by omega⟩

/-- The address budget for the two logarithm input blocks covers the
series guard as well. -/
theorem initDepthLog_series_guard {w a P E : ℕ} (hE : 1 ≤ E)
    (hroom : a + (P + E + 4) + (P + E + 4) +
      logarithmSpace (P + E + 4) P E < 2 ^ w) :
    2 * P + 9 < 2 ^ w := by
  omega

/-- A power bound on the padded input supplies both the logarithm's
input word bound and its scratch address bound. -/
theorem initDepthLog_runtime_size_budget
    {h exponent M a cursorDegree sizeDegree coefficientDegree multiplier : ℕ}
    (input : List ℕ) :
    let base := input.length + input.foldr max 0 + 2
    let degree := 10 + 3 * (coefficientDegree + 8 * sizeDegree)
    M + 2 ≤ base ^ sizeDegree →
    a ≤ base ^ cursorDegree →
    h * (38 * (2 ^ exponent) ^ 8 + 12) + 5 ≤ base ^ coefficientDegree →
    max cursorDegree degree + 1 ≤ multiplier →
    let E := (M + 2).size
    let q := 38 * (2 ^ exponent * E) ^ 8 + E
    let P := h * (q + E + 10)
    let L := P + E + 4
    M + 2 < 2 ^ wordSize multiplier input ∧ h < 2 ^ wordSize multiplier input ∧
      a + L + L + logarithmSpace L P E < 2 ^ wordSize multiplier input := by
  dsimp only
  intro hsize ha hcoeff hdegree
  let base := input.length + input.foldr max 0 + 2
  have hb : 0 < base := by unfold base; omega
  have hmult : 1 ≤ multiplier := by omega
  have hsizeDegree : sizeDegree ≤ multiplier := by omega
  have hcoefDegree : coefficientDegree ≤ multiplier := by omega
  have hword := pow_lt_two_pow_wordSize hmult input
  have hMw := (hsize.trans (Nat.pow_le_pow_right hb hsizeDegree)).trans_lt hword
  have hhw : h < 2 ^ wordSize multiplier input := by
    have hh : h ≤ h * (38 * (2 ^ exponent) ^ 8 + 12) + 5 := by
      exact (Nat.le_mul_of_pos_right h (by omega)).trans (Nat.le_add_right _ _)
    exact ((hh.trans hcoeff).trans (Nat.pow_le_pow_right hb hcoefDegree)).trans_lt hword
  have hE : 1 ≤ (M + 2).size := Nat.lt_size.mpr (by norm_num)
  have hbits : (M + 2).size ≤ base ^ sizeDegree :=
    (Nat.size_le.mpr (Nat.lt_pow_self (by decide : 1 < (2 : ℕ)))).trans hsize
  exact ⟨hMw, hhw, (initDepthLog_runtime_word_budget input hE hbits ha hcoeff hdegree).1⟩

/-- The linked numeric procedures provide both depth selectors with
bit length, loading, rounding, and logarithms at every requested accuracy. -/
theorem initDepthNumeric_meetsContracts {w h bits load log roundEntry pack zeroEntry : ℕ}
    {p : Program} (hh : 0 < h) (hw : 3 * h + 2 ≤ w)
    (hbits : p.HasAt bits (Num.IPM.bitLengthModule bits))
    (hload : p.HasAt load (loadSmallModule load h))
    (hlog : p.HasAt log (logarithmModule log h))
    (hround : p.HasAt roundEntry [initDepthEndpointBody pack zeroEntry])
    (hpack : p.HasAt pack (packWordModule pack h)) (hzero : p.HasAt zeroEntry (isZeroModule zeroEntry)) :
    MeetsContract w p bits Num.IPM.bitLengthContract ∧
      MeetsContract w p load (loadSmallContract w h) ∧
      MeetsContract w p roundEntry (initDepthEndpointContract w h) ∧
      ∀ q, MeetsContract w p log (logarithmContract w h q) := by
  have htwo : (2 : ℕ) < 2 ^ w := by
    simpa only [pow_one] using Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) (show 1 < w by omega)
  have hbase : base h < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by omega)
  exact ⟨Num.IPM.bitLength_meetsContract htwo hbits,
    loadSmall_meetsContract (by omega) hbase hload,
    initDepthEndpoint_meetsContract (by omega) hround.head
      (packWord_meetsContract (by omega) hbase hpack) (isZero_meetsContract (by omega) hzero),
    fun _ => logarithm_meetsContract hh hw hlog⟩

/-- The endpoint rounding module links the rounding body, the word
packer, and the zero scan at consecutive entries. -/
@[expose] def initDepthEndpointModule (entry h : ℕ) : List Stmt :=
  [initDepthEndpointBody (entry + 1) (entry + 2), packWordBody (entry + 1) h,
    isZeroBody (entry + 2)]

/-- A linked endpoint rounding module supplies its read-only contract. -/
theorem initDepthEndpointModule_meetsContract {w h entry : ℕ} {p : Program}
    (hw : 1 < 2 ^ w) (hb : base h < 2 ^ w)
    (hp : p.HasAt entry (initDepthEndpointModule entry h)) :
    MeetsContract w p entry (initDepthEndpointContract w h) := by
  have hpack : p.HasAt (entry + 1) (packWordModule (entry + 1) h) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [initDepthEndpointModule, packWordModule] using hp 1 (by simp [initDepthEndpointModule])
  have hzero : p.HasAt (entry + 2) (isZeroModule (entry + 2)) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [initDepthEndpointModule, isZeroModule] using hp 2 (by simp [initDepthEndpointModule])
  exact initDepthEndpoint_meetsContract hw hp.head
    (packWord_meetsContract hw hb hpack) (isZero_meetsContract hw hzero)

/-- Adding a quadratic scan to the runtime logarithm preserves a fixed
degree-24 bound in the input bit length. -/
theorem initDepthLog_runtime_cost_with_scan {h exponent E scan : ℕ}
    (hE : 1 ≤ E) (hscan : scan ≤ 915 * E ^ 2) :
    let q := 38 * (2 ^ exponent * E) ^ 8 + E
    let P := h * (q + E + 10)
    let L := P + E + 4
    let B := h * (38 * (2 ^ exponent) ^ 8 + 12) + 5
    71 * L + logarithmCost L P E + 14 * E + scan ≤
      100915 * B ^ 3 * E ^ 24 := by
  dsimp only
  let B := h * (38 * (2 ^ exponent) ^ 8 + 12) + 5
  obtain ⟨_, _, hlog⟩ := initDepthLog_runtime_budget (h := h) (exponent := exponent) hE
  have hb : 1 ≤ B := by unfold B; omega
  have hpow : E ^ 2 ≤ E ^ 24 := Nat.pow_le_pow_right hE (by decide)
  have hpow' : E ^ 24 ≤ B ^ 3 * E ^ 24 :=
    Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hb)
  have hs : scan ≤ 915 * (B ^ 3 * E ^ 24) :=
    hscan.trans (Nat.mul_le_mul_left 915 (hpow.trans hpow'))
  have he : (E ^ 8) ^ 3 = E ^ 24 := (pow_mul E 8 3).symm
  calc
    _ ≤ 100000 * (B * E ^ 8) ^ 3 + 915 * (B ^ 3 * E ^ 24) := by
      exact Nat.add_le_add hlog hs
    _ = 100915 * B ^ 3 * E ^ 24 := by
      rw [mul_pow, he]
      ring

end MinCostFlow.MinRatio
