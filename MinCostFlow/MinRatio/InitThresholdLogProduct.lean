module

public import MinCostFlow.MinRatio.InitThresholdLogEndpoints
public import MinCostFlow.Num.ExtendCopy
public import MinCostFlow.Num.ShiftLeft
public import MinCostFlow.Spanner.Runtime
import MinCostFlow.Num.ExtendFacts

/-!
# Products of rebuild growth factors

Widen a path factor and multiply it by the squared logarithm
at the sum of the input precisions.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Extend a nonnegative factor to the common width used for exact
multiplication with the squared logarithm. -/
@[expose] def extendRebuildFactor (entry src width wide cursor next : ℕ) : Stmt :=
  .call next entry [.reg src, .reg width, .reg wide, .const 0, .reg cursor]

/-- Zero extension retains the signed value of a nonnegative factor. -/
theorem extendRebuildFactor_runs
    {w h entry src width wide cursor next addr M K heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hext : MeetsContract w p entry (Num.extendCopyContract w h))
    (ha : st.regs src = addr) (hM : st.regs width = M)
    (hK : st.regs wide = K) (hh : st.regs cursor = heap)
    (hlen : M ≤ K) (hbelow : addr + M ≤ heap)
    (hv : Num.Valid st.mem addr h M)
    (hpos : 2 * Num.unsignedVal st.mem addr h M < Num.capacity h M)
    (hz : ZeroFrom st.mem heap) (hroom : heap + K < 2 ^ w) :
    ∃ out cost, Runs w p ω (extendRebuildFactor entry src width wide cursor next) st .normal out cost ∧
      out.regs next = heap + K ∧ Num.Valid out.mem heap h K ∧
      Num.intVal out.mem heap h K = Num.intVal st.mem addr h M ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + K) ∧
      (∀ r, r ≠ next → out.regs r = st.regs r) ∧ cost ≤ 30 * K + 12 := by
  let args := [addr, M, K, 0, heap]
  have hargs : evalArgs w st [.reg src, .reg width, .reg wide, .const 0, .reg cursor] =
      some args := by simp [evalArgs, Expr.eval, ha, hM, hK, hh, args]
  have hpre : (Num.extendCopyContract w h).pre args st.mem :=
    ⟨⟨addr, M, K, 0, heap, rfl, hlen, hbelow, Num.base_pos _, hv⟩, hz, hroom⟩
  obtain ⟨out, cost, ret, hr, hp, hret, hk, hc⟩ :=
    runs_call_of_meetsContract (r := next) hext hargs (by dsimp [args]; wram_words) hpre ω
  change ret = heap + K ∧ heap ≤ ret ∧ ret ≤ heap + K ∧
    (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
    ListAt out.mem heap (Num.extendedLimbs st.mem addr 0 M K) at hp
  obtain ⟨heq, _, _, hf, hzero, hdigits⟩ := hp
  have hvalid := Num.valid_listAt hdigits (Num.extendedLimbs_lt hv (Num.base_pos h))
  rw [Num.extendedLimbs_length] at hvalid
  have hval := Num.unsignedVal_listAt (h := h) hdigits
  rw [Num.extendedLimbs_length, Num.listVal_extended_zero hlen] at hval
  have hpos' : 2 * Num.unsignedVal st.mem addr h M < Num.capacity h K := by
    apply hpos.trans_le
    simp only [Num.capacity_eq_two_pow]
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hlen)
  refine ⟨out, cost, hr, hret.trans heq, hvalid, ?_, hf, heq ▸ hzero, hk, ?_⟩
  · simp only [Num.intVal, hval, Num.signedVal, ite_eq_right (not_le_of_gt hpos'),
      ite_eq_right (not_le_of_gt hpos)]
  · simp [Num.extendCopyContract, heapContract, args, argsSize, Expr.size] at hc
    omega

/-- Multiply the upper logarithm square by a factor widened into
the block starting at the previous cursor. -/
@[expose] def multiplyRebuildLogFactor (mul : ℕ) : Stmt :=
  .call 115 mul [.reg 112, .reg 108, .reg 111, .reg 114]

/-- The mixed product is exact at twice the common limb width. -/
theorem multiplyRebuildLogFactor_runs
    {w h mul square factor limbs : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hmul : MeetsContract w p mul (Num.multiplyContract w h))
    (h112 : st.regs 112 = square) (h108 : st.regs 108 = factor)
    (h111 : st.regs 111 = limbs) (h114 : st.regs 114 = factor + limbs)
    (hsquare : square + limbs ≤ factor)
    (hv₁ : Num.Valid st.mem square h limbs) (hv₂ : Num.Valid st.mem factor h limbs)
    (hz : ZeroFrom st.mem (factor + limbs)) (hroom : factor + limbs + 6 * limbs < 2 ^ w) :
    ∃ out cost, Runs w p ω (multiplyRebuildLogFactor mul) st .normal out cost ∧
      out.regs 115 = factor + limbs + 6 * limbs ∧
      Num.Valid out.mem (factor + limbs + 4 * limbs) h (2 * limbs) ∧
      Num.intVal out.mem (factor + limbs + 4 * limbs) h (2 * limbs) =
        Num.intVal st.mem square h limbs * Num.intVal st.mem factor h limbs ∧
      (∀ x < factor + limbs, out.mem x = st.mem x) ∧
      ZeroFrom out.mem (factor + limbs + 6 * limbs) ∧
      (∀ r ≠ 115, out.regs r = st.regs r) ∧
      cost ≤ (2 * limbs) * (38 * (2 * limbs) + 35) + 120 * limbs + 104 := by
  let args := [square, factor, limbs, factor + limbs]
  have ha : evalArgs w st [.reg 112, .reg 108, .reg 111, .reg 114] = some args := by
    simp [evalArgs, Expr.eval, h112, h108, h111, h114, args]
  have hp : (Num.multiplyContract w h).pre args st.mem :=
    ⟨⟨square, factor, limbs, factor + limbs, rfl,
      hsquare.trans (Nat.le_add_right _ _), le_rfl, hv₁, hv₂⟩, hz, hroom⟩
  obtain ⟨out, cost, ret, hr, hpost, hret, hk, hc⟩ :=
    runs_call_of_meetsContract (r := 115) hmul ha (by dsimp [args]; wram_words) hp ω
  change ret = factor + limbs + 6 * limbs ∧ factor + limbs ≤ ret ∧
    ret ≤ factor + limbs + 6 * limbs ∧ (∀ x < factor + limbs, out.mem x = st.mem x) ∧
    ZeroFrom out.mem ret ∧ Num.Valid out.mem (factor + limbs + 4 * limbs) h (2 * limbs) ∧ _ at hpost
  obtain ⟨heq, _, _, hf, hzero, hv, hprod⟩ := hpost
  refine ⟨out, cost, hr, hret.trans heq, hv, hprod, hf, heq ▸ hzero, hk, ?_⟩
  simp [Num.multiplyContract, heapContract, args, argsSize, Expr.size] at hc
  omega

/-- Widen the factor in the block named by register 116 and multiply
it with the staged squared logarithm. -/
@[expose] def rebuildLogFactorProduct (extend mul : ℕ) : Stmt :=
  extendRebuildFactor extend 116 67 111 108 114 ;; multiplyRebuildLogFactor mul

/-- The two linked calls form the exact product and preserve the
original factor and squared logarithm. -/
theorem rebuildLogFactorProduct_runs
    {w h extend mul addr square heap limbs : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hext : MeetsContract w p extend (Num.extendCopyContract w h))
    (hmul : MeetsContract w p mul (Num.multiplyContract w h))
    (h116 : st.regs 116 = addr) (h112 : st.regs 112 = square)
    (h67 : st.regs 67 = limbs) (h111 : st.regs 111 = 2 * limbs)
    (h108 : st.regs 108 = heap)
    (ha : addr + limbs ≤ heap) (hs : square + 2 * limbs ≤ heap)
    (hv : Num.Valid st.mem addr h limbs) (hsv : Num.Valid st.mem square h (2 * limbs))
    (hpos : 2 * Num.unsignedVal st.mem addr h limbs < Num.capacity h limbs)
    (hz : ZeroFrom st.mem heap) (hroom : heap + 2 * limbs + 6 * (2 * limbs) < 2 ^ w) :
    ∃ out cost, Runs w p ω (rebuildLogFactorProduct extend mul) st .normal out cost ∧
      out.regs 115 = heap + 2 * limbs + 6 * (2 * limbs) ∧
      Num.Valid out.mem (heap + 2 * limbs + 4 * (2 * limbs)) h (2 * (2 * limbs)) ∧
      Num.intVal out.mem (heap + 2 * limbs + 4 * (2 * limbs)) h (2 * (2 * limbs)) =
        Num.intVal st.mem square h (2 * limbs) * Num.intVal st.mem addr h limbs ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + 2 * limbs + 6 * (2 * limbs)) ∧
      (∀ r, r ≠ 114 → r ≠ 115 → out.regs r = st.regs r) ∧
      cost ≤ (4 * limbs) * (38 * (4 * limbs) + 35) + 300 * limbs + 117 := by
  obtain ⟨mid, c, hr, h114, hv', hval, hf, hz', hk, hc⟩ :=
    extendRebuildFactor_runs (ω := ω) (next := 114) hext h116 h67 h111 h108
      (by omega) ha hv hpos hz (by omega)
  have hsv' : Num.Valid mid.mem square h (2 * limbs) := by
    intro j hj
    rw [hf _ (by omega)]
    exact hsv j hj
  obtain ⟨out, d, ht, h115, hvout, hprod, hf', hzout, hk', hd⟩ :=
    multiplyRebuildLogFactor_runs (ω := ω) hmul ((hk 112 (by decide)).trans h112)
      ((hk 108 (by decide)).trans h108) ((hk 111 (by decide)).trans h111) h114 hs
      hsv' hv' hz' hroom
  refine ⟨out, c + d + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, ht, rfl⟩),
    h115, hvout, ?_, fun x hx => (hf' x (by omega)).trans (hf x hx), hzout, fun r hr₁ hr₂ => (hk' r hr₂).trans (hk r hr₁), ?_⟩
  · rw [hprod, hval, Num.intVal_congr (fun j hj => hf (square + j) (by omega))]
  · rw [show 4 * limbs = 2 * (2 * limbs) by omega]
    omega

/-- The exact product adds the input fractional precisions. A
nonnegative upper factor preserves the logarithm-square upper bound. -/
theorem rebuildLogFactorProduct_bound
    {h heap square addr limbs precision input : ℕ} {mem out : ℕ → ℕ}
    {factor : ℝ}
    (hprod : Num.intVal out (heap + 2 * limbs + 4 * (2 * limbs)) h (2 * (2 * limbs)) =
      Num.intVal mem square h (2 * limbs) * Num.intVal mem addr h limbs)
    (hlog : Real.log ((input + 2 : ℕ) : ℝ) ^ 2 ≤
      Num.fixVal mem square h (2 * limbs) (2 * precision))
    (hfactor : factor ≤ Num.fixVal mem addr h limbs precision)
    (hnonneg : 0 ≤ factor) :
    Real.log ((input + 2 : ℕ) : ℝ) ^ 2 * factor ≤
      Num.fixVal out (heap + 2 * limbs + 4 * (2 * limbs)) h (2 * (2 * limbs))
        (2 * precision + precision) := by
  have hu := mul_le_mul hlog hfactor hnonneg ((sq_nonneg _).trans hlog)
  unfold Num.fixVal at hu ⊢
  rw [hprod, Int.cast_mul, pow_add, ← div_mul_div_comm]
  exact hu

/-- Bound the product error using the exact squared logarithm and the
upper path factor. This controls the upper endpoint used for the rebuild table. -/
theorem rebuildLogFactorProduct_error
    {logSq factor logUpper factorUpper logError factorError : ℝ}
    (hlog : 0 ≤ logSq) (hfactor : 0 ≤ factor)
    (hl : logSq ≤ logUpper) (hf : factor ≤ factorUpper)
    (hle : logUpper - logSq ≤ logError)
    (hfe : factorUpper - factor ≤ factorError) :
    0 ≤ logUpper * factorUpper - logSq * factor ∧
      logUpper * factorUpper - logSq * factor ≤
        logError * factorUpper + logSq * factorError := by
  have hfu : 0 ≤ factorUpper := hfactor.trans hf
  constructor
  · exact sub_nonneg.mpr (mul_le_mul hl hf hfactor (hlog.trans hl))
  · calc
      logUpper * factorUpper - logSq * factor =
          (logUpper - logSq) * factorUpper + logSq * (factorUpper - factor) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hle hfu)
        (mul_le_mul_of_nonneg_left hfe hlog)

/-- A nonnegative upper path factor and the upper squared logarithm
give a certified product bound in the newly allocated result block. -/
theorem rebuildLogFactorProduct_upper_runs
    {w h extend mul addr square heap limbs precision input : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {factor : ℝ}
    (hext : MeetsContract w p extend (Num.extendCopyContract w h))
    (hmul : MeetsContract w p mul (Num.multiplyContract w h))
    (h116 : st.regs 116 = addr) (h112 : st.regs 112 = square)
    (h67 : st.regs 67 = limbs) (h111 : st.regs 111 = 2 * limbs) (h108 : st.regs 108 = heap)
    (ha : addr + limbs ≤ heap) (hs : square + 2 * limbs ≤ heap)
    (hv : Num.Valid st.mem addr h limbs) (hsv : Num.Valid st.mem square h (2 * limbs))
    (hlog : Real.log ((input + 2 : ℕ) : ℝ) ^ 2 ≤
      Num.fixVal st.mem square h (2 * limbs) (2 * precision))
    (hfactor : factor ≤ Num.fixVal st.mem addr h limbs precision) (hnonneg : 0 ≤ factor)
    (hz : ZeroFrom st.mem heap) (hroom : heap + 2 * limbs + 6 * (2 * limbs) < 2 ^ w) :
    ∃ out cost, Runs w p ω (rebuildLogFactorProduct extend mul) st .normal out cost ∧
      out.regs 115 = heap + 2 * limbs + 6 * (2 * limbs) ∧
      Num.Valid out.mem (heap + 2 * limbs + 4 * (2 * limbs)) h (2 * (2 * limbs)) ∧
      Real.log ((input + 2 : ℕ) : ℝ) ^ 2 * factor ≤
        Num.fixVal out.mem (heap + 2 * limbs + 4 * (2 * limbs)) h (2 * (2 * limbs))
          (2 * precision + precision) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (heap + 2 * limbs + 6 * (2 * limbs)) ∧
      cost ≤ (4 * limbs) * (38 * (4 * limbs) + 35) + 300 * limbs + 117 := by
  have hval := hnonneg.trans hfactor
  unfold Num.fixVal at hval
  have hi : 0 ≤ Num.intVal st.mem addr h limbs := by
    have hn := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ precision)).mp hval
    exact_mod_cast (show (0 : ℝ) ≤ (Num.intVal st.mem addr h limbs : ℝ) by simpa using hn)
  have hpos : 2 * Num.unsignedVal st.mem addr h limbs < Num.capacity h limbs := by
    by_contra! h
    rw [Num.intVal, Num.signedVal, ite_eq_left h] at hi
    have hu := Num.unsignedVal_lt hv
    omega
  obtain ⟨out, cost, hr, hcursor, hout, hp, hf, hz', _, hc⟩ :=
    rebuildLogFactorProduct_runs (ω := ω) hext hmul h116 h112 h67 h111 h108 ha hs hv hsv
      hpos hz hroom
  exact ⟨out, cost, hr, hcursor, hout, rebuildLogFactorProduct_bound hp hlog hfactor hnonneg,
    hf, hz', hc⟩

/-- Shift the upper endpoint by the coarse exponent before rounding
at the original aligned binary point. This gives the exact same ceiling
as division by the smaller power of two. -/
theorem rebuildGrowth_round_shift
    {upper precision coarse : ℕ} (hle : coarse ≤ precision) :
    let divisor := 2 ^ (precision - coarse)
    (upper * 2 ^ coarse + 2 ^ precision - 1) / 2 ^ precision =
      (upper + divisor - 1) / divisor := by
  dsimp only
  let scale := 2 ^ coarse
  let divisor := 2 ^ (precision - coarse)
  have hs : 0 < scale := Nat.two_pow_pos _
  have hd : 0 < divisor := Nat.two_pow_pos _
  have hp : 2 ^ precision = divisor * scale := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hp]
  change (upper * scale + divisor * scale - 1) / (divisor * scale) =
    (upper + divisor - 1) / divisor
  rw [← Nat.add_mul, Nat.mul_comm divisor scale, ← Nat.div_div_eq_div_mul]
  congr 1
  have htotal : 0 < upper + divisor := by omega
  have he : (upper + divisor) * scale - 1 = (upper + divisor - 1) * scale + (scale - 1) := by
    have h := Nat.sub_add_cancel (show 1 ≤ upper + divisor by omega)
    have hm := congrArg (fun v : ℕ => v * scale) h
    rw [Nat.add_mul, Nat.one_mul] at hm
    omega
  rw [he, Nat.add_comm, Nat.mul_comm (upper + divisor - 1) scale, Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt (by omega), zero_add]

/-- Shift the growth numerator by the coarse exponent before rounding. -/
@[expose] def shiftRebuildGrowth (entry src width exponent cursor next : ℕ) : Stmt :=
  .call next entry [.reg src, .reg width, .reg exponent, .reg cursor]

/-- The shifted block keeps the original fractional precision. The
coarse exponent is passed as a word even when its power is multiword. -/
theorem shiftRebuildGrowth_runs
    {w h entry src width exponent cursor next addr limbs e heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hshift : MeetsContract w p entry (Num.shiftLeftContract w h))
    (ha : st.regs src = addr) (hL : st.regs width = limbs)
    (he : st.regs exponent = e) (hh : st.regs cursor = heap)
    (heword : e < 2 ^ w) (hbelow : addr + limbs ≤ heap)
    (hv : Num.Valid st.mem addr h limbs) (hz : ZeroFrom st.mem heap)
    (hroom : heap + limbs < 2 ^ w)
    (hfit : Num.Fits h limbs (Num.intVal st.mem addr h limbs * (2 : ℤ) ^ e)) :
    ∃ out cost, Runs w p ω (shiftRebuildGrowth entry src width exponent cursor next)
        st .normal out cost ∧
      out.regs next = heap + limbs ∧ Num.Valid out.mem heap h limbs ∧
      Num.intVal out.mem heap h limbs = Num.intVal st.mem addr h limbs * (2 : ℤ) ^ e ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem (heap + limbs) ∧
      (∀ r, r ≠ next → out.regs r = st.regs r) ∧ cost ≤ 35 * limbs + 40 := by
  let args := [addr, limbs, e, heap]
  have hargs : evalArgs w st [.reg src, .reg width, .reg exponent, .reg cursor] = some args := by
    simp [evalArgs, Expr.eval, ha, hL, he, hh, args]
  have hp : (Num.shiftLeftContract w h).pre args st.mem :=
    ⟨⟨addr, limbs, e, heap, rfl, hbelow, hv⟩, hz, hroom⟩
  obtain ⟨out, cost, ret, hr, hpost, hret, hf, hc⟩ :=
    runs_call_of_meetsContract (r := next) hshift hargs (by dsimp [args]; wram_words) hp ω
  have hval := Num.shiftLeft_value_of_fits (w := w) (v := ret) hpost hfit
  change ret = heap + limbs ∧ heap ≤ ret ∧ ret ≤ heap + limbs ∧
    (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
    Num.Valid out.mem heap h limbs ∧ _ at hpost
  obtain ⟨heq, _, _, hframe, hzero, hvalid, _⟩ := hpost
  refine ⟨out, cost, hr, hret.trans heq, hvalid, hval, hframe, heq ▸ hzero, hf, ?_⟩
  simp [Num.shiftLeftContract, heapContract, args, argsSize, Expr.size] at hc
  omega

/-- Read the rounded numerator from a shifted, nonnegative limb block. -/
@[expose] def roundRebuildGrowthBlock (entry src width precision dst h : ℕ) : Stmt :=
  .call dst entry [.reg src, .reg width, .bin .div (.reg precision) (.const h)]

/-- Whole-limb rounding reads the exact ceiling at the aligned binary point. -/
theorem roundRebuildGrowthBlock_runs
    {w h entry src width precision dst addr limbs P value : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hr : MeetsContract w p entry (initDepthEndpointContract w h))
    (ha : st.regs src = addr) (hL : st.regs width = limbs) (hP : st.regs precision = P)
    (hhword : h < 2 ^ w) (hdvd : h ∣ P)
    (hfrac : P / h ≤ limbs) (hroom : addr + limbs < 2 ^ w)
    (hv : Num.Valid st.mem addr h limbs)
    (hvalue : Num.unsignedVal st.mem addr h limbs = value)
    (hfit : value / 2 ^ P + 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω (roundRebuildGrowthBlock entry src width precision dst h)
        st .normal out cost ∧
      out.regs dst = (value + 2 ^ P - 1) / 2 ^ P ∧ out.mem = st.mem ∧
      (∀ r, r ≠ dst → out.regs r = st.regs r) ∧ cost ≤ 25 * limbs + 56 := by
  have hscale : Num.capacity h (P / h) = 2 ^ P := by
    rw [Num.capacity_eq_two_pow, Nat.mul_div_cancel' hdvd]
  let args := [addr, limbs, P / h]
  have hargs : evalArgs w st [.reg src, .reg width, .bin .div (.reg precision) (.const h)] =
      some args := by
    simp [evalArgs, Expr.eval, BinOp.eval, ha, hL, hP, args, hhword,
      show P / h < 2 ^ w by omega]
  have hp : (initDepthEndpointContract w h).pre args st.mem :=
    ⟨addr, limbs, P / h, rfl, hfrac, hroom, hv, by rwa [hvalue, hscale]⟩
  obtain ⟨out, c, ret, ht, ⟨hm, hret⟩, hreg, hk, hc⟩ :=
    runs_call_of_meetsContract (r := dst) hr hargs (by dsimp [args]; wram_words) hp ω
  change ret = Num.unsignedVal st.mem addr h limbs / Num.capacity h (P / h) +
    (if Num.unsignedVal st.mem addr h limbs % Num.capacity h (P / h) = 0 then 0 else 1) at hret
  rw [hvalue, hscale] at hret
  have he : value / 2 ^ P + (if value % 2 ^ P = 0 then 0 else 1) =
      (value + 2 ^ P - 1) / 2 ^ P := by
    have hp := Nat.two_pow_pos P
    have hm := Nat.mod_add_div value (2 ^ P)
    have hmod := Nat.mod_lt value hp
    rw [Nat.mul_comm (2 ^ P)] at hm
    apply Eq.symm
    by_cases hz : value % 2 ^ P = 0
    · rw [ite_eq_left hz, Nat.add_zero]
      apply Nat.div_eq_of_lt_le <;> (try simp only [Nat.add_mul, Nat.one_mul]) <;> omega
    · rw [ite_eq_right hz]
      apply Nat.div_eq_of_lt_le <;> simp only [Nat.add_mul, Nat.one_mul] <;> omega
  exact ⟨out, c, ht, hreg.trans (hret.trans he), hm, hk, by
    simp [initDepthEndpointContract, args, argsSize, Expr.size] at hc
    omega⟩

/-- Shift the upper growth numerator and round it into the word used by
the integer threshold recurrence. -/
@[expose] def roundMultiwordRebuildGrowth (shift round h : ℕ) : Stmt :=
  shiftRebuildGrowth shift 117 118 119 115 120 ;;
  roundRebuildGrowthBlock round 115 118 121 12 h

/-- The two routines return the same coarse numerator as a single exact
ceiling division, without storing the fine scale in a word. -/
theorem roundMultiwordRebuildGrowth_runs
    {w h shift round addr limbs e heap P upper : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w h))
    (hround : MeetsContract w p round (initDepthEndpointContract w h))
    (ha : st.regs 117 = addr) (hL : st.regs 118 = limbs)
    (he : st.regs 119 = e) (hh : st.regs 115 = heap) (hP : st.regs 121 = P)
    (hword : h < 2 ^ w) (heword : e < 2 ^ w) (hdvd : h ∣ P) (heP : e ≤ P)
    (hfrac : P / h ≤ limbs) (hbelow : addr + limbs ≤ heap)
    (hv : Num.Valid st.mem addr h limbs) (hz : ZeroFrom st.mem heap)
    (hroom : heap + limbs < 2 ^ w)
    (hvalue : Num.intVal st.mem addr h limbs = (upper : ℤ))
    (hfit : Num.Fits h limbs ((upper : ℤ) * (2 : ℤ) ^ e))
    (hrounded : upper * 2 ^ e / 2 ^ P + 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω (roundMultiwordRebuildGrowth shift round h) st .normal out cost ∧
      out.regs 12 = (upper + 2 ^ (P - e) - 1) / 2 ^ (P - e) ∧
      out.regs 120 = heap + limbs ∧ (∀ a < heap, out.mem a = st.mem a) ∧
      ZeroFrom out.mem (heap + limbs) ∧
      (∀ r, r ≠ 12 → r ≠ 120 → out.regs r = st.regs r) ∧ cost ≤ 60 * limbs + 97 := by
  obtain ⟨mid, c, hr, h120, hvalid, hi, hf, hz', hk, hc⟩ :=
    shiftRebuildGrowth_runs (ω := ω) (next := 120) hshift ha hL he hh heword hbelow hv hz hroom
      (hvalue.symm ▸ hfit)
  have hi' : Num.intVal mid.mem heap h limbs = ((upper * 2 ^ e : ℕ) : ℤ) := by
    rw [hi, hvalue]
    push_cast
    rfl
  have hu : Num.unsignedVal mid.mem heap h limbs = upper * 2 ^ e := by
    have hl := Num.unsignedVal_lt hvalid
    unfold Num.intVal Num.signedVal at hi'
    split at hi' <;> omega
  obtain ⟨out, d, hs, h12, hm, hk', hd⟩ :=
    roundRebuildGrowthBlock_runs (ω := ω) (dst := 12) hround ((hk 115 (by decide)).trans hh)
      ((hk 118 (by decide)).trans hL) ((hk 121 (by decide)).trans hP) hword hdvd hfrac
      hroom hvalid hu hrounded
  exact ⟨out, c + d + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, hs, rfl⟩),
    h12.trans (rebuildGrowth_round_shift heP), (hk' 120 (by decide)).trans h120,
    fun a ha => (congrFun hm a).trans (hf a ha), hm.symm ▸ hz', fun r h12' h120' => (hk' r h12').trans (hk r h120'), by omega⟩

/-- Pass the coarse scale and the fresh cursor to the existing table
writer after rounding the multiword numerator. -/
@[expose] def stageMultiwordRebuildTable : Stmt :=
  .assign 4 (.reg 30) ;; .assign 77 (.reg 120)

/-- The handoff preserves the rounded numerator, the chain dimensions,
and all allocated blocks. -/
theorem stageMultiwordRebuildTable_runs
    {w scale heap : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h30 : st.regs 30 = scale) (h120 : st.regs 120 = heap) :
    ∃ out, Runs w p ω stageMultiwordRebuildTable st .normal out 5 ∧
      out.regs 4 = scale ∧ out.regs 77 = heap ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 4 → r ≠ 77 → out.regs r = st.regs r) := by
  let mid := {st with regs := Function.update st.regs 4 scale}
  let out := {mid with regs := Function.update mid.regs 77 heap}
  have hr : Runs w p ω (.assign 4 (.reg 30)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨_, congrArg some h30, rfl, rfl, rfl⟩
  have hs : Runs w p ω (.assign 77 (.reg 120)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, mid, h120], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, 2, hr, hs, rfl⟩),
    by simp [out, mid], by simp [out], rfl, fun r h4 h77 => by simp [out, mid, h4, h77]⟩

/-- Install the integer threshold table from the multiword growth upper bound. -/
@[expose] def initMultiwordIntegerThresholdTable (shift round h : ℕ) : Stmt :=
  roundMultiwordRebuildGrowth shift round h ;;
  stageMultiwordRebuildTable ;;
  reserveAndInitIntegerThresholdTable

/-- Rounding and table construction preserve earlier allocations and
give the certified threshold bounds at every level. -/
theorem initMultiwordIntegerThresholdTable_runs
    (TP : Chain.SparseCoreParams) (C : Chain.ChainParams)
    {w h shift round addr limbs e heap P upper vertices scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w h))
    (hround : MeetsContract w p round (initDepthEndpointContract w h))
    (ha : st.regs 117 = addr) (hL : st.regs 118 = limbs)
    (he : st.regs 119 = e) (hh : st.regs 115 = heap) (hP : st.regs 121 = P)
    (hword : h < 2 ^ w) (heword : e < 2 ^ w) (hdvd : h ∣ P) (heP : e ≤ P)
    (hfrac : P / h ≤ limbs) (hbelow : addr + limbs ≤ heap)
    (hv : Num.Valid st.mem addr h limbs) (hz : ZeroFrom st.mem heap)
    (hroom : heap + limbs < 2 ^ w)
    (hvalue : Num.intVal st.mem addr h limbs = (upper : ℤ))
    (hfit : Num.Fits h limbs ((upper : ℤ) * (2 : ℤ) ^ e))
    (hrounded : upper * 2 ^ e / 2 ^ P + 1 < 2 ^ w)
    (hwordTwo : 1 < 2 ^ w) (hbase : heap + limbs + C.d + 1 < 2 ^ w)
    (h30 : st.regs 30 = scale) (hscale : scale = 2 ^ e)
    (hTP : TP.Valid) (hγM : TP.γ_ℓ (C.M₀ ^ 2) ≤ C.M₀)
    (hγk : TP.γ_ℓ (C.M₀ ^ 2) ≤ C.k)
    (hlow : TP.γ_ℓ (C.M₀ ^ 2) ≤ (upper : ℝ) / (2 : ℝ) ^ P)
    (hhigh : (upper : ℝ) / (2 : ℝ) ^ P + 1 / scale ≤
      TP.γ_ℓ (C.M₀ ^ 2) + 1 / ((C.d : ℝ) + 1))
    (h22 : st.regs 22 = C.M₀) (h14 : st.regs 14 = Nat.clog 2 (vertices + 2))
    (h76 : st.regs 76 = C.k) (h75 : st.regs 75 = C.d)
    (hden : 3 * C.k * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w)
    (hcapacity : (3 * C.M₀ ^ 2 + 1) * (C.M₀ * (2 * scale) ^ (C.d + 1)) < 2 ^ w) :
    let a := (upper + 2 ^ (P - e) - 1) / 2 ^ (P - e)
    let base := heap + limbs
    ∃ out cost, Runs w p ω (initMultiwordIntegerThresholdTable shift round h) st .normal out cost ∧
      out.regs 83 = base ∧ out.regs 98 = base + C.d + 1 ∧
      (∀ j ≤ C.d, out.mem (base + j) = Chain.concreteLevelRebuildCount C.M₀ C.k a scale j vertices ∧
        (out.mem (base + j) : ℝ) ≤ Chain.SparseCoreTool.updateThreshold C.k (Chain.levelM TP C j) vertices ∧
        Chain.SparseCoreTool.updateThreshold C.k (Chain.levelM TP C j) vertices ≤
          48 * ((out.mem (base + j) : ℝ) + 1)) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (base + C.d + 1) ∧
      cost ≤ 60 * limbs + 50 * C.d + 179 := by
  dsimp only
  obtain ⟨mid, c, hr, h12, h120, hf, hz', hk, hc⟩ :=
    roundMultiwordRebuildGrowth_runs (ω := ω) hshift hround ha hL he hh hP
      hword heword hdvd heP hfrac hbelow hv hz hroom hvalue hfit hrounded
  obtain ⟨ready, ht, h4, h77, hm, hk'⟩ :=
    stageMultiwordRebuildTable_runs (w := w) (p := p) (ω := ω)
      ((hk 30 (by decide) (by decide)).trans h30) h120
  have hs : 0 < scale := hscale.symm ▸ Nat.two_pow_pos e
  have hdiv : 0 < 2 ^ (P - e) := Nat.two_pow_pos _
  have hscaleEq : ((scale * 2 ^ (P - e) : ℕ) : ℝ) = (2 : ℝ) ^ P := by
    rw [hscale, ← pow_add, Nat.add_sub_of_le heP]
    push_cast
    rfl
  obtain ⟨hlo, hu⟩ := Chain.roundLevelGrowthUpper_bounds upper scale (2 ^ (P - e)) hs hdiv
  rw [hscaleEq] at hlo hu
  have keep (r : ℕ) (hr₁ : r ≠ 4 := by decide) (hr₂ : r ≠ 77 := by decide)
      (hr₃ : r ≠ 12 := by decide) (hr₄ : r ≠ 120 := by decide) :=
    (hk' r hr₁ hr₂).trans (hk r hr₃ hr₄)
  obtain ⟨out, hwrite, h83, h98, htable, hf', hzero⟩ :=
    initIntegerThresholdTable_fromCoarse_runs (ω := ω) TP C hwordTwo hbase (hm.symm ▸ hz')
      ((hk' 12 (by decide) (by decide)).trans h12) h4 hs hTP hγM hγk
      (hlow.trans hlo) (hu.trans hhigh) ((keep 22).trans h22) ((keep 14).trans h14)
      h77 ((keep 76).trans h76) ((keep 75).trans h75) hden hcapacity
  refine ⟨out, c + 5 + (50 * C.d + 75) + 2, ?_, h83, h98, htable, ?_, hzero, by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, c, _, hr,
      runs_seq_iff.mpr (Or.inr ⟨ready, 5, _, ht, hwrite, rfl⟩), by omega⟩)
  · intro x hx
    exact (hf' x (by omega)).trans ((congrFun hm x).trans (hf x hx))

/-- The two growth terms can be rounded separately and compared as
words. This avoids aligning their multiword numerators for a comparison. -/
theorem rebuildGrowth_round_max
    {a b divisor : ℕ} :
    (max a b + divisor - 1) / divisor =
      max ((a + divisor - 1) / divisor) ((b + divisor - 1) / divisor) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right]
    exact Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h _) _)
  · rw [max_eq_left h, max_eq_left]
    exact Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h _) _)

/-- For the integer machine path factors the fine endpoint is exact.
Rounding its encoding simply multiplies the integer factor by the coarse scale. -/
theorem rebuildGrowth_round_exact {value precision coarse : ℕ}
    (he : coarse ≤ precision) :
    (value * 2 ^ precision + 2 ^ (precision - coarse) - 1) /
      2 ^ (precision - coarse) = value * 2 ^ coarse := by
  have hpow : 2 ^ precision = 2 ^ coarse * 2 ^ (precision - coarse) := by
    rw [← pow_add, Nat.add_sub_of_le he]
  let divisor := 2 ^ (precision - coarse)
  have hpos : 0 < divisor := Nat.two_pow_pos _
  rw [hpow, ← Nat.mul_assoc]
  change (value * 2 ^ coarse * divisor + divisor - 1) / divisor = _
  apply Nat.div_eq_of_lt_le
  · omega
  · rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Raising the fine precision by a power of two leaves the rounded
coarse numerator unchanged. -/
theorem rebuildGrowth_round_extend_precision {upper precision coarse extra : ℕ}
    (he : coarse ≤ precision) :
    (upper * 2 ^ extra + 2 ^ (precision + extra - coarse) - 1) /
      2 ^ (precision + extra - coarse) =
      (upper + 2 ^ (precision - coarse) - 1) / 2 ^ (precision - coarse) := by
  have hsub : precision + extra - coarse = precision - coarse + extra := by omega
  rw [hsub]
  exact rebuildGrowth_round_shift (upper := upper) (precision := precision - coarse + extra)
    (coarse := extra) (by omega) |>.trans (by rw [Nat.add_sub_cancel])

/-- Separate ceiling divisions retain the larger growth bound and incur
at most one coarse unit of rounding error in total. -/
theorem roundedRebuildGrowth_max_bounds
    (a b scale da db : ℕ) (hs : 0 < scale) (ha : 0 < da) (hb : 0 < db) :
    let upper := max ((a : ℝ) / ↑(scale * da)) ((b : ℝ) / ↑(scale * db))
    let rounded := max ((a + da - 1) / da) ((b + db - 1) / db)
    upper ≤ (rounded : ℝ) / scale ∧
      (rounded : ℝ) / scale ≤ upper + 1 / scale := by
  dsimp only
  obtain ⟨hal, hau⟩ := Chain.roundLevelGrowthUpper_bounds a scale da hs ha
  obtain ⟨hbl, hbu⟩ := Chain.roundLevelGrowthUpper_bounds b scale db hs hb
  have hs' : (0 : ℝ) ≤ scale := by exact_mod_cast hs.le
  constructor
  · apply max_le
    · exact hal.trans (div_le_div_of_nonneg_right (by exact_mod_cast le_max_left _ _) hs')
    · exact hbl.trans (div_le_div_of_nonneg_right (by exact_mod_cast le_max_right _ _) hs')
  · rcases le_total ((a + da - 1) / da) ((b + db - 1) / db) with h | h
    · rw [max_eq_right h]
      exact hbu.trans (add_le_add_left (le_max_right _ _) _)
    · rw [max_eq_left h]
      exact hau.trans (add_le_add_left (le_max_left _ _) _)

/-- A common error budget for both upper endpoints also bounds their
maximum. Reserve one coarse unit of that budget for the final rounding. -/
theorem rebuildGrowth_max_budget {a b upperA upperB scale budget : ℝ}
    (ha : a ≤ upperA) (hb : b ≤ upperB)
    (ha' : upperA + 1 / scale ≤ a + budget)
    (hb' : upperB + 1 / scale ≤ b + budget) :
    max a b ≤ max upperA upperB ∧
      max upperA upperB + 1 / scale ≤ max a b + budget := by
  constructor
  · exact max_le (ha.trans (le_max_left _ _)) (hb.trans (le_max_right _ _))
  · rcases le_total upperA upperB with h | h
    · rw [max_eq_right h]
      exact hb'.trans (add_le_add_left (le_max_right _ _) _)
    · rw [max_eq_left h]
      exact ha'.trans (add_le_add_left (le_max_left _ _) _)

/-- The length growth cap is the maximum of the squared path factors
for the two graph sizes used by the sparsifier. -/
theorem capGammaL_eq_max_path_squares
    {cDeg phiConst phiMin : ℝ} {paths : Spanner.PathDSTool} {M : ℕ}
    (ha : 0 ≤ paths.γ_ExpPath phiMin M)
    (hb : 0 ≤ paths.γ_ExpPath phiConst (Spanner.capM_W cDeg phiMin M)) :
    Spanner.capGammaL cDeg phiConst paths phiMin M =
      max (paths.γ_ExpPath phiMin M ^ 2)
        (paths.γ_ExpPath phiConst (Spanner.capM_W cDeg phiMin M) ^ 2) := by
  rw [Spanner.capGammaL, Spanner.capGammaExpPath]
  rcases le_total (paths.γ_ExpPath phiMin M)
      (paths.γ_ExpPath phiConst (Spanner.capM_W cDeg phiMin M)) with h | h
  · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ ha h 2)]
  · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ hb h 2)]

/-- Translate bounds stated at each term's fine precision into the
denominators used by the integer table writer. -/
theorem rebuildGrowth_dyadic_max_budget
    {a b target budget : ℝ} {upper upper' P P' e scale : ℕ}
    (hscale : scale = 2 ^ e) (heP : e ≤ P) (heP' : e ≤ P')
    (htarget : target = max a b)
    (ha : a ≤ (upper : ℝ) / (2 : ℝ) ^ P)
    (hb : b ≤ (upper' : ℝ) / (2 : ℝ) ^ P')
    (ha' : (upper : ℝ) / (2 : ℝ) ^ P + 1 / scale ≤ a + budget)
    (hb' : (upper' : ℝ) / (2 : ℝ) ^ P' + 1 / scale ≤ b + budget) :
    let combined := max ((upper : ℝ) / ↑(scale * 2 ^ (P - e)))
      ((upper' : ℝ) / ↑(scale * 2 ^ (P' - e)))
    target ≤ combined ∧ combined + 1 / scale ≤ target + budget := by
  have castScale (precision : ℕ) (he : e ≤ precision) :
      ((scale * 2 ^ (precision - e) : ℕ) : ℝ) = (2 : ℝ) ^ precision := by
    rw [hscale, ← pow_add, Nat.add_sub_of_le he]
    push_cast
    rfl
  dsimp only
  rw [castScale P heP, castScale P' heP', htarget]
  exact rebuildGrowth_max_budget ha hb ha' hb'

/-- Save the first rounded word and stage the second numerator, width,
precision, and fresh allocation cursor for the same rounding routine. -/
@[expose] def stageSecondRebuildGrowth : Stmt :=
  .assign 122 (.reg 12) ;;
  .assign 117 (.reg 123) ;;
  .assign 118 (.reg 124) ;;
  .assign 121 (.reg 125) ;;
  .assign 115 (.reg 120)

/-- The handoff leaves the common coarse scale and allocated memory intact. -/
theorem stageSecondRebuildGrowth_runs
    {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State} :
    ∃ out, Runs w p ω stageSecondRebuildGrowth st .normal out 14 ∧
      out.regs 122 = st.regs 12 ∧ out.regs 117 = st.regs 123 ∧
      out.regs 118 = st.regs 124 ∧ out.regs 121 = st.regs 125 ∧
      out.regs 115 = st.regs 120 ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 122 → r ≠ 117 → r ≠ 118 → r ≠ 121 → r ≠ 115 →
        out.regs r = st.regs r) := by
  let s₁ := {st with regs := Function.update st.regs 122 (st.regs 12)}
  let s₂ := {s₁ with regs := Function.update s₁.regs 117 (st.regs 123)}
  let s₃ := {s₂ with regs := Function.update s₂.regs 118 (st.regs 124)}
  let s₄ := {s₃ with regs := Function.update s₃.regs 121 (st.regs 125)}
  let out := {s₄ with regs := Function.update s₄.regs 115 (st.regs 120)}
  have h₁ : Runs w p ω (.assign 122 (.reg 12)) st .normal s₁ 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  have h₂ : Runs w p ω (.assign 117 (.reg 123)) s₁ .normal s₂ 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s₁], rfl, rfl, rfl⟩
  have h₃ : Runs w p ω (.assign 118 (.reg 124)) s₂ .normal s₃ 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s₂, s₁], rfl, rfl, rfl⟩
  have h₄ : Runs w p ω (.assign 121 (.reg 125)) s₃ .normal s₄ 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s₃, s₂, s₁], rfl, rfl, rfl⟩
  have h₅ : Runs w p ω (.assign 115 (.reg 120)) s₄ .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s₄, s₃, s₂, s₁], rfl, rfl, rfl⟩
  refine ⟨out, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s₁, 2, 11, h₁,
      runs_seq_iff.mpr (Or.inr ⟨s₂, 2, 8, h₂,
        runs_seq_iff.mpr (Or.inr ⟨s₃, 2, 5, h₃,
          runs_seq_iff.mpr (Or.inr ⟨s₄, 2, 2, h₄, h₅, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  all_goals simp [out, s₄, s₃, s₂, s₁, Function.update_of_ne, *]
  intro r h122 h117 h118 h121 h115
  simp [h122, h117, h118, h121, h115]

/-- Select the larger of the two rounded growth numerators. The first
numerator is saved in register 122 while the second is rounded. -/
@[expose] def selectRoundedRebuildGrowth : Stmt :=
  .cond (.bin .lt (.reg 12) (.reg 122)) (.assign 12 (.reg 122)) .nop

/-- Selecting the larger rounded word does not touch the table inputs. -/
theorem selectRoundedRebuildGrowth_runs
    {w a b : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (ha : st.regs 122 = a) (hb : st.regs 12 = b) (hw : 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω selectRoundedRebuildGrowth st .normal out cost ∧
      out.regs 12 = max a b ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 12 → out.regs r = st.regs r) ∧ cost ≤ 6 := by
  by_cases h : b < a
  · let out := {st with regs := Function.update st.regs 12 a}
    have hr : Runs w p ω (.assign 12 (.reg 122)) st .normal out 2 :=
      runs_assign_iff.mpr ⟨_, congrArg some ha, rfl, rfl, rfl⟩
    refine ⟨out, 6, runs_cond_iff.mpr ⟨1, 2, ?_, hr, rfl⟩,
      by simp [out, max_eq_left h.le], rfl, ?_, le_rfl⟩
    · simp [Expr.eval, BinOp.eval, ha, hb, h, show w ≠ 0 by intro he; simp [he] at hw]
    · intro r hr
      simp [out, hr]
  · exact ⟨st, 5, runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, BinOp.eval, ha, hb, h],
      runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩, hb.trans (max_eq_right (Nat.le_of_not_gt h)).symm,
      rfl, fun _ _ => rfl, by decide⟩

/-- Round the two growth factors at their own fine precisions and
select the larger coarse numerator. -/
@[expose] def roundTwoRebuildGrowthTerms (shift round h : ℕ) : Stmt :=
  roundMultiwordRebuildGrowth shift round h ;;
  stageSecondRebuildGrowth ;;
  roundMultiwordRebuildGrowth shift round h ;;
  selectRoundedRebuildGrowth

/-- Both growth inputs remain intact, with the fresh cursor advanced
past the two rounding buffers. -/
theorem roundTwoRebuildGrowthTerms_runs
    {w h shift round addr limbs e heap P upper addr' limbs' P' upper' : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w h))
    (hround : MeetsContract w p round (initDepthEndpointContract w h))
    (ha : st.regs 117 = addr) (hL : st.regs 118 = limbs)
    (he : st.regs 119 = e) (hh : st.regs 115 = heap) (hP : st.regs 121 = P)
    (ha' : st.regs 123 = addr') (hL' : st.regs 124 = limbs') (hP' : st.regs 125 = P')
    (hw : 1 < 2 ^ w) (hword : h < 2 ^ w) (heword : e < 2 ^ w)
    (hdvd : h ∣ P) (heP : e ≤ P) (hfrac : P / h ≤ limbs)
    (hdvd' : h ∣ P') (heP' : e ≤ P') (hfrac' : P' / h ≤ limbs')
    (hbelow : addr + limbs ≤ heap) (hbelow' : addr' + limbs' ≤ heap)
    (hv : Num.Valid st.mem addr h limbs) (hv' : Num.Valid st.mem addr' h limbs')
    (hz : ZeroFrom st.mem heap) (hroom : heap + limbs + limbs' < 2 ^ w)
    (hvalue : Num.intVal st.mem addr h limbs = (upper : ℤ))
    (hvalue' : Num.intVal st.mem addr' h limbs' = (upper' : ℤ))
    (hfit : Num.Fits h limbs ((upper : ℤ) * (2 : ℤ) ^ e))
    (hfit' : Num.Fits h limbs' ((upper' : ℤ) * (2 : ℤ) ^ e))
    (hrounded : upper * 2 ^ e / 2 ^ P + 1 < 2 ^ w)
    (hrounded' : upper' * 2 ^ e / 2 ^ P' + 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω (roundTwoRebuildGrowthTerms shift round h) st .normal out cost ∧
      out.regs 12 = max ((upper + 2 ^ (P - e) - 1) / 2 ^ (P - e))
        ((upper' + 2 ^ (P' - e) - 1) / 2 ^ (P' - e)) ∧
      out.regs 120 = heap + limbs + limbs' ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem (heap + limbs + limbs') ∧
      (∀ r, r ≠ 12 → r ≠ 115 → r ≠ 117 → r ≠ 118 → r ≠ 120 →
        r ≠ 121 → r ≠ 122 → out.regs r = st.regs r) ∧
      cost ≤ 60 * (limbs + limbs') + 217 := by
  obtain ⟨mid, c, hr, h12, h120, hf, hz₁, hk, hc⟩ :=
    roundMultiwordRebuildGrowth_runs (ω := ω) hshift hround ha hL he hh hP
      hword heword hdvd heP hfrac hbelow hv hz (by omega) hvalue hfit hrounded
  obtain ⟨ready, hs, h122, h117, h118, h121, h115, hm, hk₁⟩ :=
    stageSecondRebuildGrowth_runs (w := w) (p := p) (ω := ω) (st := mid)
  have hmem (a : ℕ) (ha : a < heap) : ready.mem a = st.mem a :=
    (congrFun hm a).trans (hf a ha)
  have hblock (i : ℕ) (hi : i < limbs') : ready.mem (addr' + i) = st.mem (addr' + i) :=
    hmem _ (by omega)
  have hvalid : Num.Valid ready.mem addr' h limbs' := by
    intro i hi
    rw [hblock i hi]
    exact hv' i hi
  have hval : Num.intVal ready.mem addr' h limbs' = (upper' : ℤ) :=
    (Num.intVal_congr hblock).trans hvalue'
  obtain ⟨done, d, ht, h12', h120', hf', hz₂, hk₂, hd⟩ :=
    roundMultiwordRebuildGrowth_runs (ω := ω) hshift hround
      (h117.trans ((hk 123 (by decide) (by decide)).trans ha'))
      (h118.trans ((hk 124 (by decide) (by decide)).trans hL'))
      ((hk₁ 119 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hk 119 (by decide) (by decide)).trans he))
      (h115.trans h120) (h121.trans ((hk 125 (by decide) (by decide)).trans hP'))
      hword heword hdvd' heP' hfrac' (by omega) hvalid (hm.symm ▸ hz₁) hroom hval hfit' hrounded'
  obtain ⟨out, f, hu, hmax, hm', hk₃, hfCost⟩ :=
    selectRoundedRebuildGrowth_runs (ω := ω)
      ((hk₂ 122 (by decide) (by decide)).trans (h122.trans h12)) h12' hw
  refine ⟨out, c + 14 + d + f + 3, ?_, hmax, (hk₃ 120 (by decide)).trans h120', ?_,
    hm'.symm ▸ hz₂, ?_, by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, c, _, hr,
      runs_seq_iff.mpr (Or.inr ⟨ready, 14, _, hs,
        runs_seq_iff.mpr (Or.inr ⟨done, d, f, ht, hu, rfl⟩), rfl⟩), by omega⟩)
  · intro a ha
    exact (congrFun hm' a).trans ((hf' a (by omega)).trans (hmem a ha))

  · intro r h12r h115r h117r h118r h120r h121r h122r
    exact (hk₃ r h12r).trans ((hk₂ r h12r h120r).trans
      ((hk₁ r h122r h117r h118r h121r h115r).trans (hk r h12r h120r)))

/-- Write the integer rebuild table from the larger of two growth terms. -/
@[expose] def initTwoGrowthIntegerThresholdTable (shift round h : ℕ) : Stmt :=
  roundTwoRebuildGrowthTerms shift round h ;;
  stageMultiwordRebuildTable ;;
  reserveAndInitIntegerThresholdTable

/-- The table has the certified lower and upper bounds at each level. -/
theorem initTwoGrowthIntegerThresholdTable_runs
    (TP : Chain.SparseCoreParams) (C : Chain.ChainParams)
    {w h shift round addr limbs e heap P upper addr' limbs' P' upper' vertices scale : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w h))
    (hround : MeetsContract w p round (initDepthEndpointContract w h))
    (ha : st.regs 117 = addr) (hL : st.regs 118 = limbs)
    (he : st.regs 119 = e) (hh : st.regs 115 = heap) (hP : st.regs 121 = P)
    (ha' : st.regs 123 = addr') (hL' : st.regs 124 = limbs') (hP' : st.regs 125 = P')
    (hw : 1 < 2 ^ w) (hword : h < 2 ^ w) (heword : e < 2 ^ w)
    (hdvd : h ∣ P) (heP : e ≤ P) (hfrac : P / h ≤ limbs)
    (hdvd' : h ∣ P') (heP' : e ≤ P') (hfrac' : P' / h ≤ limbs')
    (hbelow : addr + limbs ≤ heap) (hbelow' : addr' + limbs' ≤ heap)
    (hv : Num.Valid st.mem addr h limbs) (hv' : Num.Valid st.mem addr' h limbs')
    (hz : ZeroFrom st.mem heap) (hroom : heap + limbs + limbs' < 2 ^ w)
    (hvalue : Num.intVal st.mem addr h limbs = (upper : ℤ))
    (hvalue' : Num.intVal st.mem addr' h limbs' = (upper' : ℤ))
    (hfit : Num.Fits h limbs ((upper : ℤ) * (2 : ℤ) ^ e))
    (hfit' : Num.Fits h limbs' ((upper' : ℤ) * (2 : ℤ) ^ e))
    (hrounded : upper * 2 ^ e / 2 ^ P + 1 < 2 ^ w)
    (hrounded' : upper' * 2 ^ e / 2 ^ P' + 1 < 2 ^ w)
    (h30 : st.regs 30 = scale) (hscale : scale = 2 ^ e)
    (hTP : TP.Valid) (hγM : TP.γ_ℓ (C.M₀ ^ 2) ≤ C.M₀)
    (hγk : TP.γ_ℓ (C.M₀ ^ 2) ≤ C.k)
    (hbase : heap + limbs + limbs' + C.d + 1 < 2 ^ w)
    (hlow : TP.γ_ℓ (C.M₀ ^ 2) ≤ max ((upper : ℝ) / ↑(scale * 2 ^ (P - e)))
        ((upper' : ℝ) / ↑(scale * 2 ^ (P' - e))))
    (hhigh : max ((upper : ℝ) / ↑(scale * 2 ^ (P - e)))
        ((upper' : ℝ) / ↑(scale * 2 ^ (P' - e))) + 1 / scale ≤
      TP.γ_ℓ (C.M₀ ^ 2) + 1 / ((C.d : ℝ) + 1))
    (h22 : st.regs 22 = C.M₀) (h14 : st.regs 14 = Nat.clog 2 (vertices + 2))
    (h76 : st.regs 76 = C.k) (h75 : st.regs 75 = C.d)
    (hden : 3 * C.k * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w)
    (hcapacity : (3 * C.M₀ ^ 2 + 1) * (C.M₀ * (2 * scale) ^ (C.d + 1)) < 2 ^ w) :
    let a := (upper + 2 ^ (P - e) - 1) / 2 ^ (P - e)
      |> fun x => max x ((upper' + 2 ^ (P' - e) - 1) / 2 ^ (P' - e))
    let base := heap + limbs + limbs'
    ∃ out cost, Runs w p ω (initTwoGrowthIntegerThresholdTable shift round h) st .normal out cost ∧
      out.regs 83 = base ∧ out.regs 98 = base + C.d + 1 ∧
      (∀ j ≤ C.d, out.mem (base + j) = Chain.concreteLevelRebuildCount C.M₀ C.k a scale j vertices ∧
        (out.mem (base + j) : ℝ) ≤ Chain.SparseCoreTool.updateThreshold C.k (Chain.levelM TP C j) vertices ∧
        Chain.SparseCoreTool.updateThreshold C.k (Chain.levelM TP C j) vertices ≤
          48 * ((out.mem (base + j) : ℝ) + 1)) ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem (base + C.d + 1) ∧
      cost ≤ 60 * (limbs + limbs') + 50 * C.d + 299 := by
  dsimp only
  obtain ⟨mid, c, hr, h12, h120, hf, hz', hk, hc⟩ :=
    roundTwoRebuildGrowthTerms_runs (ω := ω) hshift hround ha hL he hh hP ha' hL' hP'
      hw hword heword hdvd heP hfrac hdvd' heP' hfrac' hbelow hbelow' hv hv' hz hroom
      hvalue hvalue' hfit hfit' hrounded hrounded'
  obtain ⟨ready, ht, h4, h77, hm, hk'⟩ :=
    stageMultiwordRebuildTable_runs (w := w) (p := p) (ω := ω)
      ((hk 30 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans h30) h120
  have hs : 0 < scale := hscale.symm ▸ Nat.two_pow_pos e
  obtain ⟨hlo, hu⟩ := roundedRebuildGrowth_max_bounds upper upper' scale
    (2 ^ (P - e)) (2 ^ (P' - e)) hs (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  have keep (r : ℕ) (hr₁ : r ≠ 4 := by decide) (hr₂ : r ≠ 77 := by decide)
      (hr₃ : r ≠ 12 := by decide) (hr₄ : r ≠ 120 := by decide)
      (hr₅ : r ≠ 115 := by decide) (hr₆ : r ≠ 117 := by decide)
      (hr₇ : r ≠ 118 := by decide) (hr₈ : r ≠ 121 := by decide)
      (hr₉ : r ≠ 122 := by decide) :=
    (hk' r hr₁ hr₂).trans (hk r hr₃ hr₅ hr₆ hr₇ hr₄ hr₈ hr₉)
  obtain ⟨out, hwrite, h83, h98, htable, hf', hzero⟩ :=
    initIntegerThresholdTable_fromCoarse_runs (ω := ω) TP C hw hbase (hm.symm ▸ hz')
      ((hk' 12 (by decide) (by decide)).trans h12) h4 hs hTP hγM hγk
      (hlow.trans hlo) (hu.trans hhigh) ((keep 22).trans h22) ((keep 14).trans h14)
      h77 ((keep 76).trans h76) ((keep 75).trans h75) hden hcapacity
  refine ⟨out, c + 5 + (50 * C.d + 75) + 2, ?_, h83, h98, htable, ?_, hzero, by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, c, _, hr,
      runs_seq_iff.mpr (Or.inr ⟨ready, 5, _, ht, hwrite, rfl⟩), by omega⟩)
  · intro x hx
    exact (hf' x (by omega)).trans ((congrFun hm x).trans (hf x hx))

/-- Scale the exact integer length factor for the threshold recurrence. -/
@[expose] def stageExactRebuildGrowth : Stmt :=
  .assign 12 (.bin .mul (.reg 17) (.reg 30))

/-- The exact length factor needs a single word multiplication when
its scaled value fits. Earlier allocations and other registers are preserved. -/
theorem stageExactRebuildGrowth_runs
    {w growth scale : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hg : st.regs 17 = growth) (hs : st.regs 30 = scale)
    (hfit : growth * scale < 2 ^ w) :
    ∃ out, Runs w p ω stageExactRebuildGrowth st .normal out 4 ∧
      out.regs 12 = growth * scale ∧ out.mem = st.mem ∧
      (∀ r ≠ 12, out.regs r = st.regs r) := by
  let out := {st with regs := Function.update st.regs 12 (growth * scale)}
  exact ⟨out, runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hg, hs, hfit],
    rfl, rfl, rfl⟩, by simp [out], rfl, fun r hr => by simp [out, hr]⟩

/-- Write the integer table directly from a word encoding the exact
length growth factor. -/
@[expose] def initExactGrowthThresholdTable : Stmt :=
  stageExactRebuildGrowth ;;
  .assign 4 (.reg 30) ;;
  reserveAndInitIntegerThresholdTable

/-- The exact growth path has the same threshold bounds and allocates
only the table itself. -/
theorem initExactGrowthThresholdTable_runs
    (TP : Chain.SparseCoreParams) (C : Chain.ChainParams)
    {w growth scale vertices base : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hw : 1 < 2 ^ w) (hbase : base + C.d + 1 < 2 ^ w) (hz : ZeroFrom st.mem base)
    (hg : st.regs 17 = growth) (hs : st.regs 30 = scale)
    (hfit : growth * scale < 2 ^ w) (hscale : 0 < scale)
    (hTP : TP.Valid) (hγM : TP.γ_ℓ (C.M₀ ^ 2) ≤ C.M₀)
    (hγk : TP.γ_ℓ (C.M₀ ^ 2) ≤ C.k) (hγ : TP.γ_ℓ (C.M₀ ^ 2) = growth)
    (h22 : st.regs 22 = C.M₀) (h14 : st.regs 14 = Nat.clog 2 (vertices + 2))
    (h77 : st.regs 77 = base) (h76 : st.regs 76 = C.k) (h75 : st.regs 75 = C.d)
    (hden : 3 * C.k * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w)
    (hcapacity : (3 * C.M₀ ^ 2 + 1) * (C.M₀ * (2 * scale) ^ (C.d + 1)) < 2 ^ w) :
    ∃ out, Runs w p ω initExactGrowthThresholdTable st .normal out (50 * C.d + 83) ∧
      out.regs 83 = base ∧ out.regs 98 = base + C.d + 1 ∧
      (∀ j ≤ C.d, out.mem (base + j) =
        Chain.concreteLevelRebuildCount C.M₀ C.k (growth * scale) scale j vertices ∧
        (out.mem (base + j) : ℝ) ≤ Chain.SparseCoreTool.updateThreshold C.k
          (Chain.levelM TP C j) vertices ∧
        Chain.SparseCoreTool.updateThreshold C.k (Chain.levelM TP C j) vertices ≤
          48 * ((out.mem (base + j) : ℝ) + 1)) ∧
      (∀ x < base, out.mem x = st.mem x) ∧ ZeroFrom out.mem (base + C.d + 1) := by
  obtain ⟨mid, hr, h12, hm, hk⟩ := stageExactRebuildGrowth_runs (p := p) (ω := ω) hg hs hfit
  let ready := {mid with regs := Function.update mid.regs 4 scale}
  have ht : Runs w p ω (.assign 4 (.reg 30)) mid .normal ready 2 :=
    runs_assign_iff.mpr ⟨_, congrArg some ((hk 30 (by decide)).trans hs), rfl, rfl, rfl⟩
  have keep (r : ℕ) (hr₁ : r ≠ 4 := by decide) (hr₂ : r ≠ 12 := by decide) :
      ready.regs r = st.regs r := by simpa [ready, hr₁] using hk r hr₂
  have heq : ((growth * scale : ℕ) : ℝ) / scale = TP.γ_ℓ (C.M₀ ^ 2) := by
    rw [hγ, Nat.cast_mul, mul_div_cancel_right₀]
    exact_mod_cast hscale.ne'
  obtain ⟨out, hrun, h83, h98, htable, hf, hzero⟩ :=
    initIntegerThresholdTable_fromCoarse_runs (ω := ω) TP C hw hbase (hm.symm ▸ hz)
      (by simpa [ready] using h12) (by simp [ready]) hscale hTP hγM hγk
      heq.symm.le (by rw [heq]; exact le_add_of_nonneg_right (by positivity)) ((keep 22).trans h22) ((keep 14).trans h14)
      ((keep 77).trans h77) ((keep 76).trans h76) ((keep 75).trans h75) hden hcapacity
  refine ⟨out, ?_, h83, h98, htable, fun x hx => (hf x hx).trans (congrFun hm x), hzero⟩
  exact runs_seq_iff.mpr (Or.inr ⟨mid, 4, _, hr,
    runs_seq_iff.mpr (Or.inr ⟨ready, 2, _, ht, hrun, rfl⟩), by omega⟩)

/-- Write the integer table directly from the scaled length factor
returned by the machine sparsifier. -/
@[expose] def initScaledGrowthThresholdTable : Stmt :=
  .assign 12 (.reg 50) ;;
  .assign 77 (.reg 98) ;;
  reserveAndInitIntegerThresholdTable

/-- The exact growth path has the same threshold bounds and allocates
only the table itself. -/
theorem initScaledGrowthThresholdTable_runs
    (TP : Chain.SparseCoreParams) (C : Chain.ChainParams)
    {w numerator scale vertices base : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hw : 1 < 2 ^ w) (hbase : base + C.d + 1 < 2 ^ w) (hz : ZeroFrom st.mem base)
    (hg : st.regs 50 = numerator) (hs : st.regs 4 = scale)
    (hscale : 0 < scale)
    (hTP : TP.Valid) (hγM : TP.γ_ℓ (C.M₀ ^ 2) ≤ C.M₀)
    (hγk : TP.γ_ℓ (C.M₀ ^ 2) ≤ C.k) (hγ : (numerator : ℝ) / scale = TP.γ_ℓ (C.M₀ ^ 2))
    (h22 : st.regs 22 = C.M₀) (h14 : st.regs 14 = Nat.clog 2 (vertices + 2))
    (h98 : st.regs 98 = base) (h76 : st.regs 76 = C.k) (h75 : st.regs 75 = C.d)
    (hden : 3 * C.k * Nat.clog 2 (vertices + 2) ^ 2 < 2 ^ w)
    (hcapacity : (3 * C.M₀ ^ 2 + 1) * (C.M₀ * (2 * scale) ^ (C.d + 1)) < 2 ^ w) :
    ∃ out, Runs w p ω initScaledGrowthThresholdTable st .normal out (50 * C.d + 81) ∧
      out.regs 83 = base ∧ out.regs 98 = base + C.d + 1 ∧
      (∀ j ≤ C.d, out.mem (base + j) =
        Chain.concreteLevelRebuildCount C.M₀ C.k numerator scale j vertices ∧
        (out.mem (base + j) : ℝ) ≤ Chain.SparseCoreTool.updateThreshold C.k
          (Chain.levelM TP C j) vertices ∧
        Chain.SparseCoreTool.updateThreshold C.k (Chain.levelM TP C j) vertices ≤
          48 * ((out.mem (base + j) : ℝ) + 1)) ∧
      (∀ x < base, out.mem x = st.mem x) ∧ ZeroFrom out.mem (base + C.d + 1) := by
  let mid := {st with regs := Function.update st.regs 12 numerator}
  have hr : Runs w p ω (.assign 12 (.reg 50)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨_, congrArg some hg, rfl, rfl, rfl⟩
  let ready := {mid with regs := Function.update mid.regs 77 base}
  have ht : Runs w p ω (.assign 77 (.reg 98)) mid .normal ready 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, mid, h98], rfl, rfl, rfl⟩
  have keep (r : ℕ) (hr₁ : r ≠ 77 := by decide) (hr₂ : r ≠ 12 := by decide) :
      ready.regs r = st.regs r := by simp [ready, mid, hr₁, hr₂]
  obtain ⟨out, hrun, h83, h98, htable, hf, hzero⟩ :=
    initIntegerThresholdTable_fromCoarse_runs (ω := ω) (st := ready) TP C hw hbase hz
      (by simp [ready, mid]) ((keep 4).trans hs) hscale hTP hγM hγk
      hγ.symm.le (by rw [hγ]; exact le_add_of_nonneg_right (by positivity)) ((keep 22).trans h22) ((keep 14).trans h14)
      (by simp [ready]) ((keep 76).trans h76) ((keep 75).trans h75) hden hcapacity
  refine ⟨out, ?_, h83, h98, htable, hf, hzero⟩
  exact runs_seq_iff.mpr (Or.inr ⟨mid, 2, _, hr,
    runs_seq_iff.mpr (Or.inr ⟨ready, 2, _, ht, hrun, rfl⟩), by omega⟩)

end MinCostFlow.MinRatio
