module

public import MinCostFlow.MinRatio.InitThresholdLogLink

/-!
# Rebuild precision from input widths

Compute the dimensions of the rebuild workspace from runtime inputs.
The fixed-point scale stays implicit so it can exceed a single word.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Even the first factor alone requires the input bit width times
the sparsifier depth in the current common-scale representation. -/
theorem rebuildWorkingBits_ge_mul_log
    {L cap coarse err bound : ℕ} (hc : 0 < coarse) (he : 0 < err) (hb : 0 < bound) :
    L * Nat.log 2 bound ≤ growthWorkingBits L cap coarse err bound := by
  have hbase : 2 ^ Nat.log 2 bound ≤ bound := Nat.pow_log_le_self 2 (by omega)
  have hpow : 2 ^ (L * Nat.log 2 bound) ≤ bound ^ L := by
    rw [Nat.mul_comm L, pow_mul]
    exact Nat.pow_le_pow_left hbase L
  have hscale := (growthWorkingBits_bounds L cap coarse err bound).2.1
  have hfactor : bound ^ L ≤ 3 ^ L * (err * (L + 1) * bound ^ L) * coarse := by
    have h₁ := Nat.le_mul_of_pos_left (bound ^ L) (Nat.mul_pos he (Nat.succ_pos L))
    have h₂ := Nat.le_mul_of_pos_left (err * (L + 1) * bound ^ L)
      (show 0 < 3 ^ L by positivity)
    have h₃ := Nat.le_mul_of_pos_right (3 ^ L * (err * (L + 1) * bound ^ L)) hc
    exact h₁.trans (h₂.trans h₃)
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
    (hpow.trans (hfactor.trans hscale))

/-- Once the depth exceeds the word-size multiplier, a factor bound
at least as large as the encoded input scale can exhaust the word. -/
theorem rebuildWorkingBits_wordSize_le
    {L cap coarse err bound c : ℕ} (input : List ℕ)
    (hc : 0 < coarse) (he : 0 < err)
    (hbound : input.length + input.foldr max 0 + 2 ≤ bound)
    (hlog : c ≤ Nat.log 2 (input.length + input.foldr max 0 + 2))
    (hdepth : c < L) :
    wordSize c input ≤ growthWorkingBits L cap coarse err bound := by
  let n := Nat.log 2 (input.length + input.foldr max 0 + 2)
  have hn : n ≤ Nat.log 2 bound := Nat.log_mono_right hbound
  have hprod : (c + 1) * n ≤ L * Nat.log 2 bound := Nat.mul_le_mul hdepth hn
  apply le_trans _ ((rebuildWorkingBits_ge_mul_log (L := L) (cap := cap) hc he
    (show 0 < bound by omega)).trans' hprod)
  change c * (n + 1) ≤ (c + 1) * n
  rw [Nat.mul_succ, Nat.succ_mul]
  exact Nat.add_le_add_left hlog _

/-- With these input bounds, the current aligned scale is too large
for the initializer's single-word scale register. -/
theorem rebuildAlignedScale_not_word
    {L cap coarse err bound c h : ℕ} (input : List ℕ)
    (hh : 0 < h) (hc : 0 < coarse) (he : 0 < err)
    (hbound : input.length + input.foldr max 0 + 2 ≤ bound)
    (hlog : c ≤ Nat.log 2 (input.length + input.foldr max 0 + 2))
    (hdepth : c < L) :
    let bits := growthWorkingBits L cap coarse err bound
    let precision := (bits + (h - 1)) / h * h
    ¬ 2 ^ precision < (2 : ℕ) ^ wordSize c input := by
  dsimp only
  let bits := growthWorkingBits L cap coarse err bound
  let top := bits + (h - 1)
  let precision := top / h * h
  have hmod := Nat.mod_lt top hh
  have hdiv := Nat.mod_add_div top h
  rw [Nat.mul_comm h] at hdiv
  change top % h + precision = bits + (h - 1) at hdiv
  have hbits : bits ≤ precision := by omega
  have hword : wordSize c input ≤ bits :=
    rebuildWorkingBits_wordSize_le input hc he hbound hlog hdepth
  exact not_lt_of_ge (Nat.pow_le_pow_right (by decide) (hword.trans hbits))

/-- A common bound on the input widths and the sparsifier depth
gives a quadratic bound on the unaligned rebuild precision. -/
theorem rebuildWorkingBits_le_of_width_bound
    {L cap coarse err bound width : ℕ}
    (hL : L ≤ width) (hcap : Nat.clog 2 cap ≤ width)
    (hcoarse : Nat.clog 2 coarse ≤ width) (herr : Nat.clog 2 err ≤ width)
    (hbound : Nat.clog 2 bound ≤ width) :
    growthWorkingBits L cap coarse err bound ≤ width ^ 2 + 5 * width + 7 := by
  have hlog : Nat.clog 2 (L + 1) ≤ width + 1 :=
    Nat.clog_le_of_le_pow ((Nat.succ_le_succ hL).trans (Nat.le_of_lt Nat.lt_two_pow_self))
  have hp := Nat.mul_le_mul hL hbound
  have hfirst : 2 * L + Nat.clog 2 (L + 1) + L * Nat.clog 2 bound ≤
      width ^ 2 + 3 * width + 7 := by
    rw [pow_two]
    omega
  have hsecond : 6 + Nat.clog 2 cap + 2 * Nat.clog 2 bound ≤
      width ^ 2 + 3 * width + 7 := by omega
  have hmax := max_le hfirst hsecond
  have hbits := growthWorkingBits_le L cap coarse err bound
  omega

/-- A word budget for the aligned precision also covers the power
exponent and the additional bits used by the threshold writer. -/
theorem rebuildThreshold_precision_fits
    {L cap coarse err bound width h w : ℕ}
    (hh : 0 < h) (hL : L ≤ width) (hcap : Nat.clog 2 cap ≤ width)
    (hcoarse : Nat.clog 2 coarse ≤ width) (herr : Nat.clog 2 err ≤ width)
    (hbound : Nat.clog 2 bound ≤ width)
    (hw : (width ^ 2 + 5 * width + 7 + h) * (width + 3) +
      12 + width + (width + 2) * (width + 3) < w) :
    let bits := growthWorkingBits L cap coarse err bound
    let precision := (bits + (h - 1)) / h * h
    precision < w ∧
      precision * max (L + 1) 3 + (12 + Nat.clog 2 cap +
        (Nat.clog 2 bound + 2) * (L + 3)) < w := by
  dsimp only
  let bits := growthWorkingBits L cap coarse err bound
  let precision := (bits + (h - 1)) / h * h
  have halign : precision ≤ bits + (h - 1) := by
    dsimp [precision]
    exact Nat.div_mul_le_self _ _
  have hp : precision ≤ width ^ 2 + 5 * width + 7 + h := by
    have hbits := rebuildWorkingBits_le_of_width_bound hL hcap hcoarse herr hbound
    change bits ≤ _ at hbits
    omega
  have hpow := Nat.mul_le_mul hp (show max (L + 1) 3 ≤ width + 3 by omega)
  have hextra := Nat.mul_le_mul (show Nat.clog 2 bound + 2 ≤ width + 2 by omega)
    (show L + 3 ≤ width + 3 by omega)
  have hprec : precision ≤ precision * max (L + 1) 3 :=
    Nat.le_mul_of_pos_right _ (by omega)
  change precision < w ∧ precision * max (L + 1) 3 + _ < w
  omega

/-- One bit-length call on the sum of the coefficient inputs gives a
common bound on their ceiling logarithms. Add depth and range for the
workspace requirements that are measured directly in bits. -/
theorem rebuildWorkspaceWidth_bounds (L cap coarse err bound range : ℕ) :
    let width := (cap + coarse + err + bound).size + L + range + 16
    L ≤ width ∧ Nat.clog 2 cap ≤ width ∧ Nat.clog 2 coarse ≤ width ∧
      Nat.clog 2 err ≤ width ∧ Nat.clog 2 bound ≤ width ∧ max 16 (range + 11) ≤ width := by
  dsimp only
  let sum := cap + coarse + err + bound
  have hs : sum < 2 ^ sum.size := Nat.lt_size_self _
  have hlog {value : ℕ} (hv : value ≤ sum) : Nat.clog 2 value ≤ sum.size :=
    Nat.clog_le_of_le_pow (hv.trans hs.le)
  have hcap := hlog (value := cap) (by dsimp [sum]; omega)
  have hcoarse := hlog (value := coarse) (by dsimp [sum]; omega)
  have herr := hlog (value := err) (by dsimp [sum]; omega)
  have hbound := hlog (value := bound) (by dsimp [sum]; omega)
  dsimp only [sum] at hcap hcoarse herr hbound
  exact ⟨by omega, by omega, by omega, by omega, by omega, max_le (by omega) (by omega)⟩

/-- Measure the coefficient inputs together, then include the depth
and logarithm range in the common width. -/
@[expose] def stageRebuildCommonWidth (bits : ℕ) : Stmt :=
  .call 37 bits [.bin .add (.bin .add (.bin .add (.reg 34) (.reg 30)) (.reg 35)) (.reg 36)] ;;
  .assign 37 (.bin .add (.bin .add (.bin .add (.reg 37) (.reg 44)) (.reg 127)) (.const 16))

/-- The common width uses one bit-length call and preserves all other registers. -/
theorem stageRebuildCommonWidth_runs
    {w bits L cap coarse err bound range : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : MeetsContract w p bits Num.IPM.bitLengthContract)
    (h34 : st.regs 34 = cap) (h30 : st.regs 30 = coarse)
    (h35 : st.regs 35 = err) (h36 : st.regs 36 = bound)
    (h44 : st.regs 44 = L) (h127 : st.regs 127 = range) :
    let total := cap + coarse + err + bound
    let width := total.size + L + range + 16
    total < 2 ^ w → width < 2 ^ w →
    ∃ out cost, Runs w p ω (stageRebuildCommonWidth bits) st .normal out cost ∧
      out.regs 37 = width ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 37 → out.regs r = st.regs r) ∧ cost ≤ 14 * total.size + 23 := by
  dsimp only
  intro htotal hwidth
  let total := cap + coarse + err + bound
  let width := total.size + L + range + 16
  have ha : evalArgs w st
      [.bin .add (.bin .add (.bin .add (.reg 34) (.reg 30)) (.reg 35)) (.reg 36)] = some [total] := by
    simp [evalArgs, Expr.eval, h34, h30, h35, h36, total, htotal,
      show cap + coarse < 2 ^ w by omega, show cap + coarse + err < 2 ^ w by omega]
  obtain ⟨mid, c, ret, hr, ⟨hm, hval⟩, hret, hf, hc⟩ :=
    runs_call_of_meetsContract (r := 37) hp ha (by simpa [total] using htotal) ⟨_, rfl⟩ ω
  change ret = total.size at hval
  change c ≤ 7 + (14 * total.size + 6) + 1 at hc
  have hw' : width < 2 ^ w := hwidth
  have hpart : total.size + L + range < 2 ^ w := by dsimp [width] at hw'; omega
  let out := {mid with regs := Function.update mid.regs 37 width}
  have hs : Runs w p ω
      (.assign 37 (.bin .add (.bin .add (.bin .add (.reg 37) (.reg 44)) (.reg 127)) (.const 16)))
      mid .normal out 8 := by
    apply runs_assign_iff.mpr
    refine ⟨width, ?_, rfl, rfl, rfl⟩
    simp [Expr.eval, hret.trans hval, (hf 44 (by decide)).trans h44,
      (hf 127 (by decide)).trans h127, show 16 < 2 ^ w by omega,
      show total.size + L < 2 ^ w by omega, hpart, width, hw']
  refine ⟨out, c + 9, runs_seq_iff.mpr (Or.inr ⟨mid, c, 8, hr, hs, by omega⟩),
    ?_, hm, ?_, ?_⟩
  · simp [out, width, total]
  · intro r hne
    simpa [out, hne] using hf r hne
  · dsimp [total] at hc
    omega

/-- Compute a conservative bit budget directly from a common input
width in register 37. This keeps the intermediate values in words. -/
@[expose] def stageRebuildPrecisionBound : Stmt :=
  .assign 37 (.bin .add
    (.bin .mul (.reg 37) (.bin .add (.reg 37) (.const 5))) (.const 7))

/-- The conservative bit budget dominates the exact working precision
once the input widths and sparse-core depth are bounded. -/
theorem stageRebuildPrecisionBound_runs
    {w width L cap coarse err bound : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (h37 : st.regs 37 = width)
    (hL : L ≤ width) (hcap : Nat.clog 2 cap ≤ width) (hcoarse : Nat.clog 2 coarse ≤ width)
    (herr : Nat.clog 2 err ≤ width) (hbound : Nat.clog 2 bound ≤ width)
    (hwidth : width + 5 < 2 ^ w) (hfit : width * (width + 5) + 7 < 2 ^ w) :
    ∃ out, Runs w p ω stageRebuildPrecisionBound st .normal out 8 ∧
      out.regs 37 = width * (width + 5) + 7 ∧
      growthWorkingBits L cap coarse err bound ≤ out.regs 37 ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 37 → out.regs r = st.regs r) := by
  let bits := width * (width + 5) + 7
  let out := {st with regs := Function.update st.regs 37 bits}
  have he : width ^ 2 + 5 * width + 7 = bits := by dsimp [bits]; ring
  have hb := (rebuildWorkingBits_le_of_width_bound hL hcap hcoarse herr hbound).trans_eq he
  refine ⟨out, ?_, by simp [out, bits], by simpa [out] using hb, rfl,
    fun r hr => by simp [out, hr]⟩
  apply runs_assign_iff.mpr
  refine ⟨bits, ?_, rfl, rfl, rfl⟩
  simp [Expr.eval, h37, bits, hfit, hwidth, show 5 < 2 ^ w by omega,
    show 7 < 2 ^ w by omega, show width * (width + 5) < 2 ^ w by omega]

/-- Store the aligned precision and workspace limb count without
materializing the power of two in a word. -/
@[expose] def stageRebuildLogDimensions (radixBits : ℕ) : Stmt :=
  .assign 68 (.bin .mul
    (.bin .div (.bin .add (.reg 37) (.const (radixBits - 1))) (.const radixBits))
    (.const radixBits)) ;;
  .assign 67 (.bin .add (.bin .add (.reg 68) (.reg 127)) (.const 4))

/-- Alignment increases the requested precision by fewer than one limb.
The workspace leaves room for the integer part and the logarithm guard bits. -/
theorem stageRebuildLogDimensions_runs
    {w radixBits bits range : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hr : 0 < radixBits) (hrw : radixBits < 2 ^ w)
    (h37 : st.regs 37 = bits) (h127 : st.regs 127 = range)
    (htop : bits + (radixBits - 1) < 2 ^ w) :
    let precision := (bits + (radixBits - 1)) / radixBits * radixBits
    let limbs := precision + range + 4
    limbs < 2 ^ w →
    ∃ out, Runs w p ω (stageRebuildLogDimensions radixBits) st .normal out 15 ∧
      out.regs 68 = precision ∧ out.regs 67 = limbs ∧
      bits ≤ precision ∧ precision < bits + radixBits ∧ radixBits ∣ precision ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 67 → r ≠ 68 → out.regs r = st.regs r) := by
  dsimp only
  intro hlimbs
  let top := bits + (radixBits - 1)
  let q := top / radixBits
  let prec := q * radixBits
  let limbs := prec + range + 4
  have hp : prec ≤ top := Nat.div_mul_le_self _ _
  have hm := Nat.mod_lt top hr
  have he := Nat.mod_add_div top radixBits
  rw [Nat.mul_comm radixBits] at he
  have he' : top % radixBits + prec = top := he
  have hlow : bits ≤ prec := by change top % radixBits + prec = bits + (radixBits - 1) at he'; omega
  have hhigh : prec < bits + radixBits := by dsimp [top] at hp; omega
  have hq : q < 2 ^ w := (Nat.div_le_self _ _).trans_lt htop
  have hprec : prec < 2 ^ w := hp.trans_lt htop
  have hlimbs' : limbs < 2 ^ w := hlimbs
  have hword : 4 < 2 ^ w := by omega
  have hpart : prec + range < 2 ^ w := by omega
  have hsub : radixBits - 1 < 2 ^ w := (Nat.sub_le _ _).trans_lt hrw
  let s₁ := {st with regs := Function.update st.regs 68 prec}
  let s₂ := {s₁ with regs := Function.update s₁.regs 67 limbs}
  have hr₁ : Runs w p ω
      (.assign 68 (.bin .mul (.bin .div (.bin .add (.reg 37) (.const (radixBits - 1)))
        (.const radixBits)) (.const radixBits))) st .normal s₁ 8 :=
    runs_assign_iff.mpr ⟨prec, by simp [Expr.eval, BinOp.eval, h37, hsub, hrw, htop,
      show top / radixBits < 2 ^ w from hq, show q * radixBits < 2 ^ w from hprec,
      prec, q, top], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω
      (.assign 67 (.bin .add (.bin .add (.reg 68) (.reg 127)) (.const 4))) s₁ .normal s₂ 6 :=
    runs_assign_iff.mpr ⟨limbs, by simp [Expr.eval, BinOp.eval, s₁, h127, hword, hpart,
      show prec + range + 4 < 2 ^ w from hlimbs', limbs], rfl, rfl, rfl⟩
  refine ⟨s₂, runs_seq_iff.mpr (Or.inr ⟨s₁, 8, 6, hr₁, hr₂, rfl⟩),
    by simp [s₂, s₁, prec, q, top], by simp [s₂, limbs, prec, q, top],
    hlow, hhigh, dvd_mul_left _ _, rfl, ?_⟩
  intro r h67 h68
  simp [s₂, s₁, h67, h68]

/-- Convert a common input width to aligned rebuild dimensions. -/
@[expose] def stageRebuildDimensionsFromWidth (h : ℕ) : Stmt :=
  stageRebuildPrecisionBound ;; stageRebuildLogDimensions h

/-- The width-based selector keeps the working scale implicit while
rounding its precision up to a whole number of limbs. -/
theorem stageRebuildDimensionsFromWidth_runs
    {w h width L cap coarse err bound range : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hh : 0 < h) (hhw : h < 2 ^ w)
    (h37 : st.regs 37 = width) (h127 : st.regs 127 = range)
    (hL : L ≤ width) (hcap : Nat.clog 2 cap ≤ width)
    (hcoarse : Nat.clog 2 coarse ≤ width) (herr : Nat.clog 2 err ≤ width)
    (hbound : Nat.clog 2 bound ≤ width)
    (hwidth : width + 5 < 2 ^ w) :
    let bits := width * (width + 5) + 7
    let precision := (bits + (h - 1)) / h * h
    bits + (h - 1) < 2 ^ w → precision + range + 4 < 2 ^ w →
    ∃ out, Runs w p ω (stageRebuildDimensionsFromWidth h) st .normal out 24 ∧
      out.regs 68 = precision ∧ out.regs 67 = precision + range + 4 ∧
      growthWorkingBits L cap coarse err bound ≤ precision ∧ width ≤ precision ∧ h ∣ precision ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 37 → r ≠ 67 → r ≠ 68 → out.regs r = st.regs r) := by
  dsimp only
  intro htop hlimbs
  obtain ⟨mid, hrun, hbits, hbudget, hm, hf⟩ :=
    stageRebuildPrecisionBound_runs (p := p) (ω := ω) h37 hL hcap hcoarse herr hbound
      hwidth ((Nat.le_add_right _ _).trans_lt htop)
  obtain ⟨out, hr, hp, hl, hlo, _, hd, hm', hf'⟩ :=
    stageRebuildLogDimensions_runs (p := p) (ω := ω) hh hhw hbits
      ((hf 127 (by decide)).trans h127) htop hlimbs
  have hwidthBudget := Nat.le_mul_of_pos_right width (show 0 < width + 5 by omega)
  have hwidthPrecision : width ≤ _ := hwidthBudget.trans ((Nat.le_add_right _ 7).trans hlo)
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 8, 15, hrun, hr, rfl⟩),
    hp, hl, (hbits ▸ hbudget).trans hlo, hwidthPrecision, hd, hm'.trans hm,
    fun r h37' h67 h68 => (hf' r h67 h68).trans (hf r h37')⟩

/-- Select aligned rebuild dimensions directly from the coefficient inputs. -/
@[expose] def stageRebuildDimensionsFromCoefficients (bits h : ℕ) : Stmt :=
  stageRebuildCommonWidth bits ;; stageRebuildDimensionsFromWidth h

/-- The selector leaves the scale implicit and changes only the three
registers for the budget, precision, and limb count. -/
theorem stageRebuildDimensionsFromCoefficients_runs
    {w bits h L cap coarse err bound range : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hh : 0 < h) (hhw : h < 2 ^ w)
    (h34 : st.regs 34 = cap) (h30 : st.regs 30 = coarse)
    (h35 : st.regs 35 = err) (h36 : st.regs 36 = bound)
    (h44 : st.regs 44 = L) (h127 : st.regs 127 = range) :
    let total := cap + coarse + err + bound
    let width := total.size + L + range + 16
    let budget := width * (width + 5) + 7
    let precision := (budget + (h - 1)) / h * h
    total < 2 ^ w → width + 5 < 2 ^ w →
    budget + (h - 1) < 2 ^ w → precision + range + 4 < 2 ^ w →
    ∃ out cost, Runs w p ω (stageRebuildDimensionsFromCoefficients bits h) st .normal out cost ∧
      out.regs 68 = precision ∧ out.regs 67 = precision + range + 4 ∧
      growthWorkingBits L cap coarse err bound ≤ precision ∧
      max 16 (range + 11) ≤ precision ∧ h ∣ precision ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 37 → r ≠ 67 → r ≠ 68 → out.regs r = st.regs r) ∧
      cost ≤ 14 * total.size + 48 := by
  dsimp only
  intro htotal hwidth htop hlimbs
  obtain ⟨mid, cost, hr, h37, hm, hf, hc⟩ :=
    stageRebuildCommonWidth_runs (ω := ω) hp h34 h30 h35 h36 h44 h127 htotal
      ((Nat.le_add_right _ _).trans_lt hwidth)
  obtain ⟨hL, hcap, hcoarse, herr, hbound, haccuracy⟩ :=
    rebuildWorkspaceWidth_bounds L cap coarse err bound range
  obtain ⟨out, hr', hprecision, hlimbs', hbudget, hwidthPrecision, hd, hm', hf'⟩ :=
    stageRebuildDimensionsFromWidth_runs (ω := ω) hh hhw h37 ((hf 127 (by decide)).trans h127)
      hL hcap hcoarse herr hbound hwidth htop hlimbs
  exact ⟨out, cost + 25, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 24, hr, hr', by omega⟩),
    hprecision, hlimbs', hbudget, haccuracy.trans hwidthPrecision, hd, hm'.trans hm,
    fun r h37' h67 h68 => (hf' r h37' h67 h68).trans (hf r h37'), by omega⟩

/-- Prepare the rebuild dimensions from the padded graph bound and the
runtime capacities, without storing a scaled real value. -/
@[expose] def initRebuildDimensions (clog bits h : ℕ) : Stmt :=
  prepareRebuildLogAllowance ;;
  stageRebuildLogRange bits ;;
  prepareGrowthCoarseScale clog ;;
  prepareRebuildScaleCapacity ;;
  stageRebuildDimensionsFromCoefficients bits h

/-- The graph range and the two capacity factors are computed before
the width-based selector. The dimension calculation leaves memory intact. -/
theorem initRebuildDimensions_runs
    {w clog bits h M N depth L buckets degree err bound : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hb : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hh : 0 < h) (hhw : h < 2 ^ w)
    (hM : st.regs 22 = M) (hN : st.regs 92 = N) (hMpos : 0 < M)
    (hd : st.regs 75 = depth) (hL : st.regs 44 = L)
    (hB : st.regs 47 = buckets) (hD : st.regs 48 = degree) (hBpos : 0 < buckets)
    (he : st.regs 35 = err) (hbound : st.regs 36 = bound) :
    let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
    let range := (input + 2).size
    let coarse := Chain.concreteThresholdScale depth
    let cap := (L + 1) * buckets * (2 * degree + 190)
    let allowance := max err (4096 * (input + 2))
    let total := cap + coarse + allowance + bound
    let width := total.size + L + range + 16
    let budget := width * (width + 5) + 7
    let precision := (budget + (h - 1)) / h * h
    input + 2 < 2 ^ w → 2 * (depth + 1) + 1 < 2 ^ w →
    total < 2 ^ w → width + 5 < 2 ^ w →
    budget + (h - 1) < 2 ^ w → precision + range + 4 < 2 ^ w →
    ∃ out cost, Runs w p ω (initRebuildDimensions clog bits h) st .normal out cost ∧
      out.regs 68 = precision ∧ out.regs 67 = precision + range + 4 ∧
      out.regs 124 = input + 2 ∧ out.regs 126 = 1 ∧ out.regs 127 = range ∧
      growthWorkingBits L cap coarse allowance bound ≤ precision ∧
      max 16 (range + 11) ≤ precision ∧ h ∣ precision ∧ out.mem = st.mem ∧
      (∀ r, r ∉ [24, 30, 33, 34, 35, 37, 38, 57, 67, 68, 124, 126, 127] →
        out.regs r = st.regs r) ∧
      cost ≤ 14 * range + 40 * Nat.clog 2 (2 * (depth + 1)) + 14 * total.size + 170 := by
  dsimp only
  intro hinput hdepth htotal hwidth hbudget hlimbs
  let m := M ^ 2
  let input := SparseCore.coreNMax m + m
  have heq : m * (2 * m + 60) = input := by
    dsimp [input, SparseCore.coreNMax, SparseCore.coreSplitMax]
    ring
  have hprod : m * (2 * m + 60) < 2 ^ w := heq.symm ▸ (Nat.le_add_right input 2).trans_lt hinput
  have hlinear := (Nat.le_mul_of_pos_left _ (Nat.pow_pos hMpos)).trans_lt hprod
  have hmword := (Nat.le_mul_of_pos_right m (by omega : 0 < 2 * m + 60)).trans_lt hprod
  obtain ⟨start, hstart, h35, hm₀, hf₀⟩ :=
    prepareRebuildLogAllowance_runs (p := p) (ω := ω) hM hN he hmword
      (by omega) hlinear hprod (by omega)
  obtain ⟨s₁, c₁, hr₁, h127, h124, h126, _, hm₁, hf₁, hc₁⟩ :=
    stageRebuildLogRange_runs (ω := ω) hb ((hf₀ 22 (by decide) (by decide) (by decide) (by decide)).trans hM)
      ((hf₀ 92 (by decide) (by decide) (by decide) (by decide)).trans hN) hMpos hinput
  have keep₁ (r : ℕ) (h24 : r ≠ 24 := by decide) (h57 : r ≠ 57 := by decide)
      (h124 : r ≠ 124 := by decide) (h126 : r ≠ 126 := by decide)
      (h127' : r ≠ 127 := by decide) (h35' : r ≠ 35 := by decide) (h38 : r ≠ 38 := by decide) :=
    (hf₁ r h24 h57 h124 h126 h127').trans (hf₀ r h24 h35' h38 h57)
  obtain ⟨s₂, c₂, hr₂, h30, hm₂, hf₂, hc₂⟩ :=
    prepareGrowthCoarseScale_runs (ω := ω) hp ((keep₁ 75).trans hd) hdepth
      (lt_of_le_of_lt (Nat.le_add_left _ _) (lt_of_le_of_lt (Nat.le_add_right _ _)
        (lt_of_le_of_lt (Nat.le_add_right _ _) htotal)))
  have keep₂ (r : ℕ) (h30' : r ≠ 30 := by decide) (h24 : r ≠ 24 := by decide)
      (h57 : r ≠ 57 := by decide) (h124 : r ≠ 124 := by decide)
      (h126 : r ≠ 126 := by decide) (h127' : r ≠ 127 := by decide)
      (h35' : r ≠ 35 := by decide) (h38 : r ≠ 38 := by decide) :=
    (hf₂ r h30').trans (keep₁ r h24 h57 h124 h126 h127' h35' h38)
  obtain ⟨s₃, hr₃, h34, hm₃, hf₃⟩ :=
    prepareRebuildScaleCapacity_runs (w := w) (p := p) (ω := ω) ((keep₂ 44).trans hL)
      ((keep₂ 47).trans hB) ((keep₂ 48).trans hD) hBpos (by omega)
  have keep₃ (r : ℕ) (h33 : r ≠ 33 := by decide) (h34' : r ≠ 34 := by decide)
      (h38 : r ≠ 38 := by decide) := hf₃ r h33 h34' h38
  obtain ⟨out, c₄, hr₄, hp', hl, hprec, haccuracy, hdiv, hm₄, hf₄, hc₄⟩ :=
    stageRebuildDimensionsFromCoefficients_runs (ω := ω) hb hh hhw h34 ((keep₃ 30).trans h30)
      ((keep₃ 35).trans ((hf₂ 35 (by decide)).trans
        ((hf₁ 35 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h35))) ((keep₃ 36).trans ((keep₂ 36).trans hbound))
      ((keep₃ 44).trans ((keep₂ 44).trans hL))
      ((keep₃ 127).trans ((hf₂ 127 (by decide)).trans h127)) htotal hwidth hbudget hlimbs
  refine ⟨out, 33 + (c₁ + c₂ + 18 + c₄ + 3) + 1, ?_, hp', hl, ?_, ?_, ?_, hprec, haccuracy, hdiv,
    hm₄.trans (hm₃.trans (hm₂.trans (hm₁.trans hm₀))), ?_, by omega⟩
  · refine runs_seq_iff.mpr (Or.inr ⟨start, 33, _, hstart, ?_, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨s₁, c₁, c₂ + (18 + c₄ + 1) + 1, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨s₂, c₂, 18 + c₄ + 1, hr₂,
        runs_seq_iff.mpr (Or.inr ⟨s₃, 18, c₄, hr₃, hr₄, rfl⟩), rfl⟩), by omega⟩)
  · exact (hf₄ 124 (by decide) (by decide) (by decide)).trans
      ((keep₃ 124).trans ((hf₂ 124 (by decide)).trans h124))
  · exact (hf₄ 126 (by decide) (by decide) (by decide)).trans
      ((keep₃ 126).trans ((hf₂ 126 (by decide)).trans h126))
  · exact (hf₄ 127 (by decide) (by decide) (by decide)).trans
      ((keep₃ 127).trans ((hf₂ 127 (by decide)).trans h127))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h24, h30, h33, h34, h35', h37, h38, h57, h67, h68, h124, h126, h127⟩ := hr
    exact (hf₄ r h37 h67 h68).trans
      ((hf₃ r h33 h34 h38).trans (keep₂ r h30 h24 h57 h124 h126 h127 h35' h38))

/-- The aligned workspace has room for the integer logarithm input and
its shifted representation. -/
theorem rebuildDimension_log_input_fits {h precision input : ℕ} (hh : 0 < h) :
    let range := (input + 2).size
    let limbs := precision + range + 4
    precision / h ≤ limbs ∧ input + 2 < Num.capacity h (limbs - precision / h) ∧
      2 * ((input + 2) * Num.capacity h (precision / h)) < Num.capacity h limbs := by
  dsimp only
  let range := (input + 2).size
  let limbs := precision + range + 4
  have hdiv := Nat.div_le_self precision h
  have hroom : range ≤ limbs - precision / h := by dsimp [limbs]; omega
  have hmul {n : ℕ} : n ≤ h * n := Nat.le_mul_of_pos_left _ hh
  have hf : input + 2 < Num.capacity h (limbs - precision / h) := by
    rw [Num.capacity_eq_two_pow]
    exact (Nat.lt_size_self (input + 2)).trans_le
      (Nat.pow_le_pow_right (by decide) (hroom.trans hmul))
  have hscale : h * (precision / h) ≤ precision := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self _ _
  have hcap := rebuildLogInput_capacity (h := h) (limbs := limbs) (input := input)
    (bits := precision) (show precision + (input + 2).size + 4 ≤ h * limbs from hmul)
  refine ⟨hdiv.trans (by omega), hf, ?_⟩
  rw [Num.capacity_eq_two_pow]
  exact lt_of_le_of_lt
    (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hscale))) hcap

/-- Evaluate the sparse-core logarithm directly in the selected multiword
workspace. The input and its bit length come from the dimension stage. -/
theorem rebuildDimension_log_runs
    {w h load log heap precision input : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hh : 0 < h) (hhw : h < 2 ^ w)
    (hload : MeetsContract w p load (Num.loadSmallContract w h)) :
    let range := (input + 2).size
    let limbs := precision + range + 4
    let accuracy := precision - range - 10
    MeetsContract w p log (Num.logarithmContract w h accuracy) →
    st.regs 67 = limbs → st.regs 68 = precision → st.regs 127 = range →
    st.regs 98 = heap → st.regs 124 = input + 2 → st.regs 126 = 1 →
    input + 2 < 2 ^ w → 2 * precision + 9 < 2 ^ w →
    max 16 (range + 11) ≤ precision → h ∣ precision →
    heap + limbs + limbs + Num.logarithmSpace limbs precision range < 2 ^ w →
    ZeroFrom st.mem heap →
    ∃ out cost ret, Runs w p ω (computeInitDepthLogBlock load log h) st .normal out cost ∧
      out.regs 99 = ret ∧ heap + limbs + limbs ≤ ret ∧ ret < 2 ^ w ∧
      ret ≤ heap + limbs + limbs + Num.logarithmSpace limbs precision range ∧
      Num.Valid out.mem (ret - limbs) h limbs ∧
      |Num.fixVal out.mem (ret - limbs) h limbs precision - Real.log ((input + 2 : ℕ) : ℝ)| ≤
        1 / (2 : ℝ) ^ accuracy ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
      (∀ r, r ≠ 99 → r ≠ 123 → r ≠ 125 → out.regs r = st.regs r) ∧
      cost ≤ 46 * limbs + Num.logarithmCost limbs precision range + 45 := by
  dsimp only
  intro hlog hL hP hE ha hv hone hvword hprec hacc hdvd hroom hz
  obtain ⟨hfrac, hvalue, hfit⟩ := rebuildDimension_log_input_fits (precision := precision)
    (input := input) hh
  have hrange : input + 2 ≤ 2 ^ (input + 2).size := (Nat.lt_size_self _).le
  have hcap : precision + (input + 2).size + 4 ≤ h * (precision + (input + 2).size + 4) :=
    Nat.le_mul_of_pos_left _ hh
  have hEword : (input + 2).size < 2 ^ w := by omega
  exact computeInitDepthLogBlock_runs (ω := ω) hload hlog hhw hL hP hE ha hv hone
    (by omega) hvword (by omega) hEword hroom hfrac hdvd hz hvalue hfit (by omega)
    hcap hprec hrange

/-- The logarithm error at the selected precision fits in one word,
even when the center and scale require several limbs. -/
@[expose] def stageRebuildMultiwordLogError : Stmt :=
  .assign 100 (.bin .shiftLeft (.const 1) (.bin .add (.reg 127) (.const 10)))

/-- Form the scaled logarithm error from its range, preserving the
center block and the selected precision. -/
theorem stageRebuildMultiwordLogError_runs
    {w input precision : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h127 : st.regs 127 = (input + 2).size)
    (hprec : (input + 2).size + 11 ≤ precision)
    (hallowance : 4096 * (input + 2) < 2 ^ w) :
    let accuracy := precision - (input + 2).size - 10
    ∃ out, Runs w p ω stageRebuildMultiwordLogError st .normal out 6 ∧
      out.regs 100 = 2 ^ (precision - accuracy) ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 100 → out.regs r = st.regs r) := by
  dsimp only
  let e := (input + 2).size + 10
  have he : precision - (precision - (input + 2).size - 10) = e := by dsimp [e]; omega
  have hg := sparseCoreLog_error_le input precision hprec
  rw [he] at hg
  have hpow : 2 ^ e < 2 ^ w := by omega
  have heword : e < 2 ^ w := (Nat.lt_two_pow_self (n := e)).trans hpow
  let out := {st with regs := Function.update st.regs 100 (2 ^ e)}
  refine ⟨out, ?_, by simp [out, he], rfl, fun r hr => by simp [out, hr]⟩
  apply runs_assign_iff.mpr
  refine ⟨_, ?_, rfl, rfl, rfl⟩
  simp [Expr.eval, BinOp.eval, Nat.shiftLeft_eq, h127, e, heword, hpow,
    show 10 < 2 ^ w by dsimp [e] at heword; omega, show 1 < 2 ^ w by omega]

/-- Select the multiword dimensions and evaluate the sparse-core logarithm. -/
@[expose] def initRebuildMultiwordLog (clog bits h load log : ℕ) : Stmt :=
  initRebuildDimensions clog bits h ;;
  computeInitDepthLogBlock load log h ;; stageRebuildMultiwordLogError

/-- The logarithm is returned as a fixed-point block at the aligned
precision. Both stages preserve memory below the incoming heap. -/
theorem initRebuildMultiwordLog_runs
    {w clog bits h load log heap M N depth L buckets degree err bound : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hp : p.HasAt clog (Scaling.Machine.clogTwoModule clog))
    (hb : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hheap : st.regs 98 = heap) (hz : ZeroFrom st.mem heap)
    (hh : 0 < h) (hhw : h < 2 ^ w)
    (hM : st.regs 22 = M) (hN : st.regs 92 = N) (hMpos : 0 < M)
    (hd : st.regs 75 = depth) (hL : st.regs 44 = L)
    (hB : st.regs 47 = buckets) (hD : st.regs 48 = degree) (hBpos : 0 < buckets)
    (he : st.regs 35 = err) (hbound : st.regs 36 = bound) :
    let input := SparseCore.coreNMax (M ^ 2) + M ^ 2
    let range := (input + 2).size
    let coarse := Chain.concreteThresholdScale depth
    let cap := (L + 1) * buckets * (2 * degree + 190)
    let allowance := max err (4096 * (input + 2))
    let total := cap + coarse + allowance + bound
    let width := total.size + L + range + 16
    let budget := width * (width + 5) + 7
    let precision := (budget + (h - 1)) / h * h
    input + 2 < 2 ^ w → 2 * (depth + 1) + 1 < 2 ^ w →
    total < 2 ^ w → width + 5 < 2 ^ w →
    budget + (h - 1) < 2 ^ w → precision + range + 4 < 2 ^ w →
    let limbs := precision + range + 4
    let accuracy := precision - range - 10
    MeetsContract w p log (Num.logarithmContract w h accuracy) →
    2 * precision + 9 < 2 ^ w →
    heap + limbs + limbs + Num.logarithmSpace limbs precision range < 2 ^ w →
    ∃ out cost ret, Runs w p ω (initRebuildMultiwordLog clog bits h load log) st .normal out cost ∧
      out.regs 99 = ret ∧ out.regs 100 = 2 ^ (precision - accuracy) ∧ heap + limbs + limbs ≤ ret ∧ ret < 2 ^ w ∧
      ret ≤ heap + limbs + limbs + Num.logarithmSpace limbs precision range ∧
      out.regs 67 = limbs ∧ out.regs 68 = precision ∧ range + 11 ≤ precision ∧ Num.Valid out.mem (ret - limbs) h limbs ∧
      |Num.fixVal out.mem (ret - limbs) h limbs precision - Real.log ((input + 2 : ℕ) : ℝ)| ≤
        1 / (2 : ℝ) ^ accuracy ∧
      (∀ x < heap, out.mem x = st.mem x) ∧ ZeroFrom out.mem ret ∧
      cost ≤ 14 * range + 40 * Nat.clog 2 (2 * (depth + 1)) + 14 * total.size + 170 +
        (46 * limbs + Num.logarithmCost limbs precision range + 45) + 8 := by
  dsimp only
  intro hinput hdepth htotal hwidth hbudget hlimbs hlog hprecision hroom
  obtain ⟨mid, c, hr, h68, h67, hv, hone, hE, _, hacc, hdvd, hm, hf, hc⟩ :=
    initRebuildDimensions_runs (ω := ω) hp hb hh hhw hM hN hMpos hd hL hB hD hBpos he hbound
      hinput hdepth htotal hwidth hbudget hlimbs
  obtain ⟨out, d, ret, hs, hret, hlo, hhi, hretBound, hvalid, herr, hframe, hzero, hregs, hcost⟩ :=
    rebuildDimension_log_runs (ω := ω) hh hhw hload hlog h67 h68 hE
      ((hf 98 (by decide)).trans hheap) hv hone hinput hprecision hacc hdvd hroom (hm.symm ▸ hz)
  obtain ⟨ready, ht, herror, hmem, hkeep⟩ :=
    stageRebuildMultiwordLogError_runs (w := w) (p := p) (ω := ω)
      ((hregs 127 (by decide) (by decide) (by decide)).trans hE)
      ((le_max_right _ _).trans hacc) (by omega)
  refine ⟨ready, c + (d + 7) + 1, ret, ?_, (hkeep 99 (by decide)).trans hret,
    herror, hlo, hhi, hretBound,
    (hkeep 67 (by decide)).trans ((hregs 67 (by decide) (by decide) (by decide)).trans h67),
    (hkeep 68 (by decide)).trans ((hregs 68 (by decide) (by decide) (by decide)).trans h68),
    (le_max_right _ _).trans hacc, hmem.symm ▸ hvalid, hmem.symm ▸ herr, ?_, hmem.symm ▸ hzero, by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, c, d + 7, hr,
      runs_seq_iff.mpr (Or.inr ⟨out, d, 6, hs, ht, by omega⟩), rfl⟩)
  · intro x hx
    exact (congrFun hmem x).trans ((hframe x hx).trans (congrFun hm x))

end MinCostFlow.MinRatio
