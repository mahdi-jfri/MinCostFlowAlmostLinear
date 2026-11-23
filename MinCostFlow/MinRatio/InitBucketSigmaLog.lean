module

public import MinCostFlow.MinRatio.InitBucketCap
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith

/-!
# Logarithms at bucket schedule endpoints

Use a fixed-point format that represents the endpoint numerators exactly.
Allocate the logarithm inputs and combine the errors of the two calls.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain SparseCore

/-- The bucket schedule numerators have denominator `(2^P)^7`.
Save the original precision and use `7P` for the logarithm call. -/
@[expose] def prepareInitBucketSigmaLogScale : Stmt :=
  .assign 30 (.reg 68) ;;
  .assign 68 (.bin .mul (.const 7) (.reg 68)) ;;
  .assign 4 (.reg 43)

/-- The schedule denominator is a power of two in the new format. -/
theorem prepareInitBucketSigmaLogScale_runs {w precision : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hP : st.regs 68 = precision) (hden : st.regs 43 = (2 ^ precision) ^ 7)
    (hw : 7 < 2 ^ w) (hfit : 7 * precision < 2 ^ w) :
    ∃ out, Runs w p ω prepareInitBucketSigmaLogScale st .normal out 10 ∧
      out.regs 30 = precision ∧ out.regs 68 = 7 * precision ∧
      out.regs 4 = 2 ^ (7 * precision) ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 30 → r ≠ 68 → r ≠ 4 → out.regs r = st.regs r) := by
  let s₁ := {st with regs := Function.update st.regs 30 precision}
  let s₂ := {s₁ with regs := Function.update s₁.regs 68 (7 * precision)}
  let out := {s₂ with regs := Function.update s₂.regs 4 ((2 ^ precision) ^ 7)}
  have hr₁ : Runs w p ω (.assign 30 (.reg 68)) st .normal s₁ 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hP], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 68 (.bin .mul (.const 7) (.reg 68))) s₁ .normal s₂ 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, s₁, hP, hw, hfit], rfl, rfl, rfl⟩
  have hr₃ : Runs w p ω (.assign 4 (.reg 43)) s₂ .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s₂, s₁, hden], rfl, rfl, rfl⟩
  refine ⟨out, ?_, by simp [out, s₂, s₁], by simp [out, s₂], ?_, rfl, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s₁, 2, 7, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨s₂, 4, 2, hr₂, hr₃, rfl⟩), rfl⟩)
  · simp [out, ← pow_mul, Nat.mul_comm]
  · intro r h30 h68 h4
    simp [out, s₂, s₁, h30, h68, h4]

/-- Compute the logarithm range from the upper schedule numerator and
its fixed-point precision. -/
@[expose] def setInitBucketSigmaLogRange (bits : ℕ) : Stmt :=
  .call 97 bits [.reg 46] ;;
  .assign 97 (.bin .sub (.reg 97) (.reg 68))

/-- Removing the fractional bits gives an exponent bounding the real
schedule endpoint. -/
theorem setInitBucketSigmaLogRange_runs
    {w bits numerator precision : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hn : st.regs 46 = numerator) (hP : st.regs 68 = precision)
    (hw : numerator < 2 ^ w) :
    ∃ out c, Runs w p ω (setInitBucketSigmaLogRange bits) st .normal out c ∧
      out.regs 97 = numerator.size - precision ∧
      (numerator : ℝ) / (2 : ℝ) ^ precision ≤ (2 : ℝ) ^ (numerator.size - precision) ∧
      out.mem = st.mem ∧ (∀ r ≠ 97, out.regs r = st.regs r) ∧ c ≤ 14 * numerator.size + 13 := by
  have hargs : evalArgs w st [.reg 46] = some [numerator] := by
    simp [evalArgs, Expr.eval, hn]
  obtain ⟨mid, c, ret, hr, hp, hret, hk, hc⟩ :=
    runs_call_of_meetsContract (r := 97) hbits hargs (by simpa using hw) ⟨_, rfl⟩ ω
  obtain ⟨hm, he⟩ := hp
  change ret = numerator.size at he
  have hsize : numerator.size < 2 ^ w := by
    have : numerator.size ≤ w := Nat.size_le.mpr hw
    exact this.trans_lt Nat.lt_two_pow_self
  have hsub : numerator.size - precision < 2 ^ w := (Nat.sub_le _ _).trans_lt hsize
  let out := {mid with regs := Function.update mid.regs 97 (numerator.size - precision)}
  have hr' : Runs w p ω (.assign 97 (.bin .sub (.reg 97) (.reg 68))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hret, he, (hk 68 (by decide)).trans hP,
      hsub], rfl, rfl, rfl⟩
  have hpow : (numerator : ℝ) ≤ (2 : ℝ) ^ numerator.size := by
    exact_mod_cast (Nat.lt_size_self numerator).le
  have hrange : (numerator : ℝ) / (2 : ℝ) ^ precision ≤ (2 : ℝ) ^ (numerator.size - precision) := by
    apply (div_le_iff₀ (by positivity)).mpr
    rw [← pow_add]
    exact hpow.trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega))
  change c ≤ 1 + (14 * numerator.size + 6) + 1 at hc
  refine ⟨out, c + 5, runs_seq_iff.mpr (Or.inr ⟨mid, c, 4, hr, hr', rfl⟩),
    by simp [out], hrange, hm, ?_, by omega⟩
  intro r h97
  simpa [out, h97] using hk r h97

/-- Set the schedule logarithm format, range, and accuracy from the
runtime precision and upper numerator. -/
@[expose] def prepareInitBucketSigmaLog (bits : ℕ) : Stmt :=
  prepareInitBucketSigmaLogScale ;; setInitBucketSigmaLogRange bits ;; setInitLogAccuracy

/-- The resulting register values satisfy the logarithm's precision
inequality when the scaled format has at least one bit of accuracy. -/
theorem prepareInitBucketSigmaLog_runs {w bits basePrecision numerator : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hP : st.regs 68 = basePrecision) (hn : st.regs 46 = numerator)
    (hden : st.regs 43 = (2 ^ basePrecision) ^ 7)
    (hw : 10 < 2 ^ w) (hwidth : 7 * basePrecision < w) (hword : numerator < 2 ^ w) :
    let precision := 7 * basePrecision
    let range := numerator.size - precision
    let accuracy := precision - range - 10
    range + 11 ≤ precision →
    ∃ out c, Runs w p ω (prepareInitBucketSigmaLog bits) st .normal out c ∧
      out.regs 30 = basePrecision ∧ out.regs 68 = precision ∧ out.regs 4 = 2 ^ precision ∧
      out.regs 97 = range ∧ out.regs 100 = accuracy ∧
      (numerator : ℝ) / (2 : ℝ) ^ precision ≤ (2 : ℝ) ^ range ∧
      1 ≤ accuracy ∧ accuracy + range + 10 ≤ precision ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 30 → r ≠ 68 → r ≠ 4 → r ≠ 97 → r ≠ 100 → out.regs r = st.regs r) ∧
      c ≤ 14 * numerator.size + 31 := by
  dsimp only
  intro hacc
  have hfit : 7 * basePrecision < 2 ^ w := hwidth.trans Nat.lt_two_pow_self
  obtain ⟨s₁, hr₁, h30, hp, hs, hm₁, hk₁⟩ :=
    prepareInitBucketSigmaLogScale_runs (p := p) (ω := ω) hP hden (by omega) hfit
  obtain ⟨s₂, c, hr₂, hE, hbound, hm₂, hk₂, hc⟩ :=
    setInitBucketSigmaLogRange_runs (ω := ω) hbits
      ((hk₁ 46 (by decide) (by decide) (by decide)).trans hn) hp hword
  obtain ⟨out, hr₃, hq, hk₃, hm₃, _⟩ :=
    setInitLogAccuracy_runs (p := p) (ω := ω) ((hk₂ 68 (by decide)).trans hp) hE hw hfit
  have keep (r : ℕ) (h97 : r ≠ 97) (h100 : r ≠ 100) :
      out.regs r = s₁.regs r := (hk₃ r h100).trans (hk₂ r h97)
  refine ⟨out, c + 18, ?_, (keep 30 (by decide) (by decide)).trans h30,
    (keep 68 (by decide) (by decide)).trans hp, (keep 4 (by decide) (by decide)).trans hs,
    (hk₃ 97 (by decide)).trans hE, hq, hbound, by omega, by omega, hm₃.trans (hm₂.trans hm₁),
    ?_, by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s₁, 10, c + 7, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨s₂, c, 6, hr₂, hr₃, rfl⟩), by omega⟩)
  · intro r h30 h68 h4 h97 h100
    exact (keep r h97 h100).trans (hk₁ r h30 h68 h4)

/-- Allocate a fixed-point block for one schedule-base endpoint using
its exact numerator. -/
@[expose] def encodeInitBucketSigmaEndpoint (load endpoint : ℕ) : Stmt :=
  .call 98 load [.reg endpoint, .reg 67, .reg 98]

/-- The new block denotes the scaled endpoint exactly, with the scratch
heap advanced by one block. -/
theorem encodeInitBucketSigmaEndpoint_runs
    {w h load endpoint numerator precision limbs heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hn : st.regs endpoint = numerator) (hL : st.regs 67 = limbs) (hh : st.regs 98 = heap)
    (hw : numerator < 2 ^ w) (hfit : 2 * numerator < Num.capacity h limbs)
    (hroom : heap + limbs < 2 ^ w) (hz : ZeroFrom st.mem heap) :
    ∃ out c, Runs w p ω (encodeInitBucketSigmaEndpoint load endpoint) st .normal out c ∧
      out.regs 98 = heap + limbs ∧ Num.Valid out.mem heap h limbs ∧
      Num.fixVal out.mem heap h limbs precision = (numerator : ℝ) / (2 : ℝ) ^ precision ∧
      (∀ r ≠ 98, out.regs r = st.regs r) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem (heap + limbs) ∧
      c ≤ 23 * limbs + 10 := by
  have hargs : evalArgs w st [.reg endpoint, .reg 67, .reg 98] =
      some [numerator, limbs, heap] := by simp [evalArgs, Expr.eval, hn, hL, hh]
  have hwords : ∀ v ∈ [numerator, limbs, heap], v < 2 ^ w := by
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl
    · exact hw
    · omega
    · omega
  have hpre : (Num.loadSmallContract w h).pre [numerator, limbs, heap] st.mem :=
    ⟨⟨numerator, limbs, heap, rfl⟩, hz, hroom⟩
  obtain ⟨out, c, ret, hr, hp, hret, hk, hc⟩ :=
    runs_call_of_meetsContract (r := 98) hload hargs hwords hpre ω
  obtain ⟨hval, _, _, hframe, hzero, hblock⟩ := hp
  change ret = heap + limbs at hval
  change ListAt out.mem heap (Num.digits h limbs numerator) at hblock
  obtain ⟨hv, _, hi⟩ := Num.loadSmall_value hblock
  have hm : numerator < Num.capacity h limbs := by omega
  rw [Nat.mod_eq_of_lt hm, Num.signedVal, ite_eq_right (Nat.not_le.mpr hfit), sub_zero] at hi
  have he : Num.fixVal out.mem heap h limbs precision =
      (numerator : ℝ) / (2 : ℝ) ^ precision := by rw [Num.fixVal, hi]; push_cast; rfl
  change c ≤ 3 + (23 * limbs + 6) + 1 at hc
  exact ⟨out, c, hr, hret.trans hval, hv, he, hk, hframe, hval ▸ hzero, by omega⟩

/-- Allocate the schedule endpoint and the constant one consecutively. -/
@[expose] def encodeInitBucketSigmaLogInputs (load endpoint : ℕ) : Stmt :=
  encodeInitBucketSigmaEndpoint load endpoint ;; encodeInitLogOne load

/-- Both input blocks satisfy the shared fixed-point format and the second
allocation preserves the exact value of the first. -/
theorem encodeInitBucketSigmaLogInputs_runs
    {w h load endpoint numerator precision limbs heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hn : st.regs endpoint = numerator) (hs : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hh : st.regs 98 = heap)
    (hw : numerator < 2 ^ w) (hsw : 2 ^ precision < 2 ^ w)
    (hfit : 2 * numerator < Num.capacity h limbs)
    (hsfit : 2 * 2 ^ precision < Num.capacity h limbs)
    (hroom : heap + limbs + limbs < 2 ^ w) (hz : ZeroFrom st.mem heap) :
    ∃ out c, Runs w p ω (encodeInitBucketSigmaLogInputs load endpoint) st .normal out c ∧
      out.regs 98 = heap + limbs + limbs ∧
      Num.Valid out.mem heap h limbs ∧
      Num.fixVal out.mem heap h limbs precision = (numerator : ℝ) / (2 : ℝ) ^ precision ∧
      Num.Valid out.mem (heap + limbs) h limbs ∧
      Num.intVal out.mem (heap + limbs) h limbs = (2 : ℤ) ^ precision ∧
      (∀ r ≠ 98, out.regs r = st.regs r) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem (heap + limbs + limbs) ∧
      c ≤ 46 * limbs + 21 := by
  obtain ⟨mid, c₁, hr₁, hh₁, hv, hval, hk₁, hf₁, hz₁, hc₁⟩ :=
    encodeInitBucketSigmaEndpoint_runs (ω := ω) (precision := precision) hload hn hL hh hw hfit
      (by omega) hz
  obtain ⟨out, c₂, hr₂, hh₂, hk₂, hv₂, hone, hf₂, hz₂, hc₂⟩ :=
    encodeInitLogOne_runs (ω := ω) hload ((hk₁ 4 (by decide)).trans hs)
      ((hk₁ 67 (by decide)).trans hL) hh₁ hsw hsfit hroom hz₁
  have hf (i : ℕ) (hi : i < limbs) : out.mem (heap + i) = mid.mem (heap + i) :=
    hf₂ _ (by omega)
  refine ⟨out, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩),
    hh₂, fun i hi => hf i hi ▸ hv i hi, ?_, hv₂, hone,
    fun r hr => (hk₂ r hr).trans (hk₁ r hr),
    fun a ha => (hf₂ a (by omega)).trans (hf₁ a ha), hz₂, by omega⟩
  rw [Num.fixVal, Num.intVal_congr hf]
  exact hval

/-- Allocate the fixed-point inputs and call the logarithm at a schedule
endpoint. The caller supplies the runtime range in register 97. -/
@[expose] def approximateInitBucketSigmaLog (load log endpoint : ℕ) : Stmt :=
  setInitLogInputPointers ;;
  encodeInitBucketSigmaLogInputs load endpoint ;;
  approximateInitVertexLog log

/-- The result block encloses the logarithm of the represented schedule
endpoint, with cost and allocation charged to its runtime format. -/
theorem approximateInitBucketSigmaLog_runs
    {w h load log endpoint numerator precision limbs heap range accuracy : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h accuracy))
    (hn : st.regs endpoint = numerator) (hs : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision)
    (hh : st.regs 98 = heap) (hE : st.regs 97 = range)
    (h95 : endpoint ≠ 95) (h96 : endpoint ≠ 96)
    (hw : numerator < 2 ^ w) (hsw : 2 ^ precision < 2 ^ w)
    (hfit : 2 * numerator < Num.capacity h limbs)
    (hsfit : 2 * 2 ^ precision < Num.capacity h limbs)
    (hroom : heap + limbs + limbs + Num.logarithmSpace limbs precision range < 2 ^ w)
    (hz : ZeroFrom st.mem heap)
    (hdiv : h ∣ precision) (hacc : accuracy + range + 10 ≤ precision)
    (hcap : precision + range + 4 ≤ h * limbs) (hprec : 2 * precision + 9 < 2 ^ w)
    (hlo : 1 / (2 : ℝ) ^ range ≤ (numerator : ℝ) / (2 : ℝ) ^ precision)
    (hhi : (numerator : ℝ) / (2 : ℝ) ^ precision ≤ (2 : ℝ) ^ range) :
    ∃ out c ret, Runs w p ω (approximateInitBucketSigmaLog load log endpoint) st .normal out c ∧
      out.regs 99 = ret ∧ heap + limbs + limbs ≤ ret ∧
      ret ≤ heap + limbs + limbs + Num.logarithmSpace limbs precision range ∧
      Num.Valid out.mem (ret - limbs) h limbs ∧
      |Num.fixVal out.mem (ret - limbs) h limbs precision -
        Real.log ((numerator : ℝ) / (2 : ℝ) ^ precision)| ≤ 1 / (2 : ℝ) ^ accuracy ∧
      (∀ r, r ≠ 95 → r ≠ 96 → r ≠ 98 → r ≠ 99 → out.regs r = st.regs r) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      c ≤ 46 * limbs + Num.logarithmCost limbs precision range + 37 := by
  obtain ⟨s₁, hr₁, ha, hone, hk₁, hm₁, _⟩ :=
    setInitLogInputPointers_runs (w := w) (p := p) (ω := ω) hh hL (by omega)
  obtain ⟨s₂, c₂, hr₂, hh₂, hv, hval, hvOne, hOne, hk₂, hf₂, hz₂, hc₂⟩ :=
    encodeInitBucketSigmaLogInputs_runs (ω := ω) hload ((hk₁ endpoint h95 h96).trans hn)
      ((hk₁ 4 (by decide) (by decide)).trans hs) ((hk₁ 67 (by decide) (by decide)).trans hL)
      ((hk₁ 98 (by decide) (by decide)).trans hh) hw hsw hfit hsfit (by omega) (hm₁.symm ▸ hz)
  have hk (r : ℕ) (h98 : r ≠ 98) (h95 : r ≠ 95) (h96 : r ≠ 96) :
      s₂.regs r = st.regs r := (hk₂ r h98).trans (hk₁ r h95 h96)
  let scratch := heap + limbs + limbs
  have hpre : (Num.logarithmContract w h accuracy).pre
      [heap, heap + limbs, limbs, precision, range, scratch] s₂.mem := by
    refine ⟨⟨heap, heap + limbs, limbs, precision, range, scratch, rfl, hdiv, hacc,
      hcap, hprec, by omega, le_rfl, hv, hvOne, hOne, hval.symm ▸ hlo, hval.symm ▸ hhi⟩, hz₂, hroom⟩
  have hwords : ∀ v ∈ [heap, heap + limbs, limbs, precision, range, scratch], v < 2 ^ w := by
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp [scratch] at * <;> omega
  obtain ⟨out, c₃, ret, hr₃, hret, hk₃, hretLo, hretHi, hf₃, hz₃, hvout, herr, hc₃⟩ :=
    approximateInitLogValue_runs (ω := ω) hlog
      ((hk₂ 95 (by decide)).trans ha) ((hk₂ 96 (by decide)).trans hone)
      ((hk 67 (by decide) (by decide) (by decide)).trans hL)
      ((hk 68 (by decide) (by decide) (by decide)).trans hP)
      ((hk 97 (by decide) (by decide) (by decide)).trans hE) hh₂ hwords hpre hval
  refine ⟨out, 7 + (c₂ + c₃ + 1) + 1, ret, ?_, hret, hretLo, hretHi, hvout, herr,
    fun r h95 h96 h98 h99 => (hk₃ r h99).trans (hk r h98 h95 h96),
    fun a ha => (hf₃ a (by omega)).trans ((hf₂ a ha).trans (congrFun hm₁ a)), hz₃, by omega⟩
  exact runs_seq_iff.mpr (Or.inr ⟨s₁, 7, _, hr₁,
    runs_seq_iff.mpr (Or.inr ⟨s₂, c₂, c₃, hr₂, hr₃, rfl⟩), rfl⟩)

/-- Run and unpack the logarithm of one schedule endpoint. -/
@[expose] def computeInitBucketSigmaEndpointLog (load log pack endpoint lower upper : ℕ) : Stmt :=
  approximateInitBucketSigmaLog load log endpoint ;; unpackInitBucketLogBounds pack lower upper

/-- When the schedule endpoint is at least two, the logarithm's
numerator and error can be unpacked as unsigned words. -/
theorem computeInitBucketSigmaEndpointLog_runs
    {w h load log pack endpoint lower upper numerator precision limbs heap range accuracy : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h accuracy))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hn : st.regs endpoint = numerator) (hs : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision)
    (hh : st.regs 98 = heap) (hE : st.regs 97 = range) (hq : st.regs 100 = accuracy)
    (h95 : endpoint ≠ 95) (h96 : endpoint ≠ 96)
    (hw : numerator < 2 ^ w) (hwidth : precision < w)
    (hfit : 2 * numerator < Num.capacity h limbs)
    (hsfit : 2 * 2 ^ precision < Num.capacity h limbs)
    (hroom : heap + limbs + limbs + Num.logarithmSpace limbs precision range < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : accuracy + range + 10 ≤ precision) (hqPos : 1 ≤ accuracy)
    (hcap : precision + range + 4 ≤ h * limbs) (hprec : 2 * precision + 9 < 2 ^ w)
    (h₂ : lower ≠ 2) (h₃ : lower ≠ 3) (hd : lower ≠ upper)
    (h₄ : lower ≠ 4) (hu₄ : upper ≠ 4) (h₉₉ : lower ≠ 99) (hu₉₉ : upper ≠ 99)
    (hbound : (range + 1) * 2 ^ precision < 2 ^ w) :
    let value := (numerator : ℝ) / (2 : ℝ) ^ precision
    2 ≤ value → value ≤ (2 : ℝ) ^ range →
    ∃ out c ret, Runs w p ω (computeInitBucketSigmaEndpointLog load log pack endpoint lower upper)
        st .normal out c ∧
      (out.regs lower : ℝ) / (2 : ℝ) ^ precision ≤ Real.log value ∧
      Real.log value ≤ (out.regs upper : ℝ) / (2 : ℝ) ^ precision ∧
      out.regs upper ≤ (range + 1) * 2 ^ precision ∧ out.regs 4 = 2 ^ precision ∧
      out.regs 99 = ret ∧ heap ≤ ret ∧
      ret ≤ heap + limbs + limbs + Num.logarithmSpace limbs precision range ∧
      (∀ r, r ≠ 95 → r ≠ 96 → r ≠ 98 → r ≠ 99 → r ≠ 2 → r ≠ 3 →
        r ≠ 4 → r ≠ lower → r ≠ upper → out.regs r = st.regs r) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      c ≤ 71 * limbs + Num.logarithmCost limbs precision range + 71 := by
  dsimp only
  intro htwo hupper
  have hones : 1 / (2 : ℝ) ^ range ≤ (numerator : ℝ) / (2 : ℝ) ^ precision :=
    (one_div_le_one_div_of_le (by norm_num) (one_le_pow₀ (by norm_num) : 1 ≤ (2 : ℝ) ^ range)).trans
      (by simpa using (show (1 : ℝ) ≤ 2 by norm_num).trans htwo)
  obtain ⟨mid, c₁, ret, hr, hret, hLo, hHi, hv, herr, hk, hframe, hzero, hc₁⟩ :=
    approximateInitBucketSigmaLog_runs (ω := ω) hload hlog hn hs hL hP hh hE h95 h96 hw
      (Nat.pow_lt_pow_right (by decide) hwidth) hfit hsfit hroom hz hdiv hacc hcap hprec hones hupper
  have hlogLo : (1 / 2 : ℝ) ≤ Real.log ((numerator : ℝ) / (2 : ℝ) ^ precision) :=
    (by linarith only [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) htwo)
  have hlogHi : Real.log ((numerator : ℝ) / (2 : ℝ) ^ precision) ≤ range := by
    have ht := Real.log_le_log (by linarith only [htwo]) hupper
    rw [Real.log_pow] at ht
    have hlogTwo : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
    simpa only [mul_one] using ht.trans (mul_le_mul_of_nonneg_left hlogTwo (Nat.cast_nonneg range))
  have hqp : accuracy ≤ precision := by omega
  have hscaled := (initLogValue_scaledError hqPos hqp hlogLo herr).2
  let approx := (Num.intVal mid.mem (ret - limbs) h limbs).toNat
  let error := 2 ^ (precision - accuracy)
  have he : 2 * error ≤ 2 ^ precision := by
    dsimp [error]
    rw [← pow_succ']
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hb : approx + error ≤ (range + 1) * 2 ^ precision := by
    have hsReal : (0 : ℝ) < (2 : ℝ) ^ precision := by positivity
    have hx := (abs_le.mp hscaled).2
    have hx' : (approx : ℝ) - (range : ℝ) * 2 ^ precision ≤ error := by
      have ht := (le_div_iff₀ hsReal).mp (show (approx : ℝ) / 2 ^ precision -
          Real.log ((numerator : ℝ) / (2 : ℝ) ^ precision) ≤ (error : ℝ) / 2 ^ precision from by
            simpa only [approx, error, Nat.cast_pow, Nat.cast_ofNat] using hx)
      rw [sub_mul, div_mul_cancel₀ _ hsReal.ne'] at ht
      linarith only [ht, mul_le_mul_of_nonneg_right hlogHi hsReal.le]
    have he' : 2 * (error : ℝ) ≤ (2 : ℝ) ^ precision := by exact_mod_cast he
    exact_mod_cast (show (approx : ℝ) + error ≤ ((range : ℝ) + 1) * 2 ^ precision by
      rw [add_mul, one_mul]
      linarith only [hx', he'])
  obtain ⟨out, c₂, hr', hlo, hhi, _, hu, hscale, hm, hk', hc₂⟩ :=
    unpackInitBucketLogValueBounds_runs (ω := ω) hpack hret
      ((hk 67 (by decide) (by decide) (by decide) (by decide)).trans hL) ((hk 68 (by decide) (by decide) (by decide) (by decide)).trans hP)
      ((hk 100 (by decide) (by decide) (by decide) (by decide)).trans hq)
      (by omega) (hHi.trans_lt hroom) hwidth hv hqPos hqp hlogLo herr h₂ h₃ hd h₄ hu₄
      (hb.trans_lt hbound)
  exact ⟨out, c₁ + c₂ + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr, hr', rfl⟩),
    by simpa using hlo, by simpa using hhi, hu ▸ hb, hscale,
    (hk' 99 (by decide) (by decide) (by decide) h₉₉.symm hu₉₉.symm).trans hret,
    by omega, hHi, fun r h95 h96 h98 h99 h2 h3 h4 hl hu =>
      (hk' r h2 h3 h4 hl hu).trans (hk r h95 h96 h98 h99),
    fun a ha => (congrFun hm a).trans (hframe a ha), hm.symm ▸ hzero, by omega⟩

/-- Evaluate the two schedule endpoints with the same range and accuracy. -/
@[expose] def computeInitBucketSigmaLogs (load log pack : ℕ) : Stmt :=
  computeInitBucketSigmaEndpointLog load log pack 45 31 36 ;;
  .assign 98 (.reg 99) ;;
  computeInitBucketSigmaEndpointLog load log pack 46 36 32

/-- The first call gives a lower logarithm bound and the second gives an
upper bound, with both runs charged to the available heap. -/
theorem computeInitBucketSigmaLogs_runs
    {w h load log pack lo hi precision limbs heap range accuracy : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {σ : ℝ}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h accuracy))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (h45 : st.regs 45 = lo) (h46 : st.regs 46 = hi) (hs : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision)
    (hh : st.regs 98 = heap) (hE : st.regs 97 = range) (hq : st.regs 100 = accuracy)
    (hwlo : lo < 2 ^ w) (hwhi : hi < 2 ^ w) (hwidth : precision < w)
    (hflo : 2 * lo < Num.capacity h limbs) (hfhi : 2 * hi < Num.capacity h limbs)
    (hsfit : 2 * 2 ^ precision < Num.capacity h limbs)
    (hroom : heap + 2 * (limbs + limbs + Num.logarithmSpace limbs precision range) < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : accuracy + range + 10 ≤ precision) (hqPos : 1 ≤ accuracy)
    (hcap : precision + range + 4 ≤ h * limbs) (hprec : 2 * precision + 9 < 2 ^ w)
    (hbound : (range + 1) * 2 ^ precision < 2 ^ w)
    (htwo : 2 ≤ (lo : ℝ) / (2 : ℝ) ^ precision)
    (hlo : (lo : ℝ) / (2 : ℝ) ^ precision ≤ σ)
    (hhi : σ ≤ (hi : ℝ) / (2 : ℝ) ^ precision)
    (hmax : (hi : ℝ) / (2 : ℝ) ^ precision ≤ (2 : ℝ) ^ range) :
    ∃ out c ret, Runs w p ω (computeInitBucketSigmaLogs load log pack) st .normal out c ∧
      (out.regs 31 : ℝ) / (2 : ℝ) ^ precision ≤ Real.log σ ∧
      Real.log σ ≤ (out.regs 32 : ℝ) / (2 : ℝ) ^ precision ∧
      out.regs 32 ≤ (range + 1) * 2 ^ precision ∧
      out.regs 99 = ret ∧ heap ≤ ret ∧
      ret ≤ heap + 2 * (limbs + limbs + Num.logarithmSpace limbs precision range) ∧
      (∀ r, r ∉ ([2, 3, 4, 31, 32, 36, 95, 96, 98, 99] : List ℕ) →
        out.regs r = st.regs r) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      c ≤ 142 * limbs + 2 * Num.logarithmCost limbs precision range + 146 := by
  obtain ⟨mid, c₁, next, hr₁, h31, _, _, hsMid, hn, hnlo, hnhi, hk, hm, hz₁, hc₁⟩ :=
    computeInitBucketSigmaEndpointLog_runs (ω := ω) (lower := 31) (upper := 36)
      hload hlog hpack h45 hs hL hP hh hE hq (by decide) (by decide)
      hwlo hwidth hflo hsfit (by omega) hz hdiv hacc hqPos hcap hprec
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hbound htwo (hlo.trans (hhi.trans hmax))
  let ready := {mid with regs := Function.update mid.regs 98 next}
  have hr₂ : Runs w p ω (.assign 98 (.reg 99)) mid .normal ready 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hn], rfl, rfl, rfl⟩
  have keep (r : ℕ) (hne : r ∉ ([2, 3, 4, 31, 36, 95, 96, 98, 99] : List ℕ)) :
      ready.regs r = st.regs r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hne
    rcases hne with ⟨h2, h3, h4, h31, h36, h95, h96, h98, h99⟩
    exact (Function.update_of_ne h98 ..).trans (hk r h95 h96 h98 h99 h2 h3 h4 h31 h36)
  have hsReady : ready.regs 4 = 2 ^ precision := by
    simpa [ready] using hsMid
  obtain ⟨out, c₂, ret, hr₃, _, h32, hu, _, hret, hretLo, hretHi, hk₂, hm₂, hz₂, hc₂⟩ :=
    computeInitBucketSigmaEndpointLog_runs (ω := ω) (lower := 36) (upper := 32)
      hload hlog hpack ((keep 46 (by decide)).trans h46) hsReady
      ((keep 67 (by decide)).trans hL) ((keep 68 (by decide)).trans hP)
      (by simp [ready]) ((keep 97 (by decide)).trans hE) ((keep 100 (by decide)).trans hq)
      (by decide) (by decide) hwhi hwidth hfhi hsfit (by omega) hz₁ hdiv hacc hqPos hcap hprec
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hbound (htwo.trans (hlo.trans hhi)) hmax
  have h31' : out.regs 31 = mid.regs 31 :=
    (hk₂ 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans (by simp [ready])
  refine ⟨out, c₁ + c₂ + 4, ret, ?_, ?_, ?_, hu, hret, by omega, by omega, ?_,
    fun a ha => (hm₂ a (by omega)).trans (hm a ha), hz₂, by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, c₁, 2 + c₂ + 1, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨ready, 2, c₂, hr₂, hr₃, rfl⟩), by omega⟩)
  · rw [h31']
    exact h31.trans (Real.log_le_log (by linarith only [htwo]) hlo)
  · exact (Real.log_le_log (by linarith only [htwo, hlo]) hhi).trans h32
  · intro r hne
    have hne' := hne
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hne'
    rcases hne' with ⟨h2, h3, h4, h31, h32, h36, h95, h96, h98, h99⟩
    exact (hk₂ r h95 h96 h98 h99 h2 h3 h4 h36 h32).trans
      (keep r (by simp [h2, h3, h4, h31, h36, h95, h96, h98, h99]))

/-- To enclose the logarithm of the schedule base, evaluate the logarithm
at each positive endpoint and include the error of each call. -/
theorem initBucketSigmaLog_bounds
    {σ approxLo approxHi errorLo errorHi : ℝ} {lo hi den scale : ℕ}
    (hloPos : 0 < lo) (hdenPos : 0 < den) (hscalePos : 0 < scale)
    (hlo : (lo : ℝ) / den ≤ σ) (hhi : σ ≤ (hi : ℝ) / den)
    (happroxLo : |approxLo - Real.log ((lo : ℝ) / den)| ≤ errorLo)
    (happroxHi : |approxHi - Real.log ((hi : ℝ) / den)| ≤ errorHi) :
    (lo : ℝ) / den ≥ 2 →
    (Nat.floor ((approxLo - errorLo) * scale) : ℝ) / scale ≤ Real.log σ ∧
      Real.log σ ≤ ((Nat.ceil ((approxHi + errorHi) * scale) : ℕ) : ℝ) / scale := by
  intro htwo
  have hs : (0 : ℝ) < scale := by exact_mod_cast hscalePos
  have hpos : 0 < (lo : ℝ) / den := div_pos (by exact_mod_cast hloPos) (by exact_mod_cast hdenPos)
  have hσ : 0 < σ := hpos.trans_le hlo
  have hl := (abs_le.mp happroxLo).2
  have hu := (abs_le.mp happroxHi).1
  have hl' : approxLo - errorLo ≤ Real.log σ := by
    have := Real.log_le_log hpos hlo
    linarith
  have hu' : Real.log σ ≤ approxHi + errorHi := by
    have := Real.log_le_log hσ hhi
    linarith
  constructor
  · apply (div_le_iff₀ hs).mpr
    by_cases hn : 0 ≤ (approxLo - errorLo) * (scale : ℝ)
    · exact (Nat.floor_le hn).trans (mul_le_mul_of_nonneg_right hl' hs.le)
    · rw [Nat.floor_of_nonpos (le_of_not_ge hn), Nat.cast_zero]
      exact mul_nonneg (Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ 2).trans (htwo.trans hlo))) hs.le
  · exact (le_div_iff₀ hs).mpr
      ((mul_le_mul_of_nonneg_right hu' hs.le).trans (Nat.le_ceil _))

/-- Restore the caller's precision and compute the factor that converts
the schedule logarithms to its scale. -/
@[expose] def restoreInitBucketSigmaLogScale : Stmt :=
  .assign 68 (.reg 30) ;;
  .assign 4 (.bin .shiftLeft (.const 1) (.reg 30)) ;;
  .assign 33 (.bin .div (.reg 43) (.reg 4))

/-- One division gives the exact scale ratio, since the schedule precision
is seven times the caller's precision. -/
theorem restoreInitBucketSigmaLogScale_runs {w precision : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hP : st.regs 30 = precision) (hden : st.regs 43 = 2 ^ (7 * precision))
     (hwidth : 7 * precision < w) :
    ∃ out, Runs w p ω restoreInitBucketSigmaLogScale st .normal out 12 ∧
      out.regs 68 = precision ∧ out.regs 4 = 2 ^ precision ∧
      out.regs 33 = 2 ^ (6 * precision) ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 68 → r ≠ 4 → r ≠ 33 → out.regs r = st.regs r) := by
  have hfit (n : ℕ) (hn : n ≤ 7 * precision) : 2 ^ n < 2 ^ w :=
    Nat.pow_lt_pow_right (by decide) (hn.trans_lt hwidth)
  have hscale := hfit precision (by omega)
  have hfac := hfit (6 * precision) (by omega)
  have hOne : 1 < 2 ^ w := by
    apply Nat.one_lt_two_pow
    omega
  have hquot : 2 ^ (7 * precision) / 2 ^ precision = 2 ^ (6 * precision) := by
    rw [show 7 * precision = 6 * precision + precision by omega, pow_add]
    exact Nat.mul_div_cancel _ (by positivity)
  let s₁ := {st with regs := Function.update st.regs 68 precision}
  let s₂ := {s₁ with regs := Function.update s₁.regs 4 (2 ^ precision)}
  let out := {s₂ with regs := Function.update s₂.regs 33 (2 ^ (6 * precision))}
  have hr₁ : Runs w p ω (.assign 68 (.reg 30)) st .normal s₁ 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hP], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 4 (.bin .shiftLeft (.const 1) (.reg 30))) s₁ .normal s₂ 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, s₁, hP, hOne,
      Nat.shiftLeft_eq, hscale], rfl, rfl, rfl⟩
  have hr₃ : Runs w p ω (.assign 33 (.bin .div (.reg 43) (.reg 4))) s₂ .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, s₂, s₁, hden, hquot, hfac],
      rfl, rfl, rfl⟩
  refine ⟨out, ?_, by simp [out, s₂, s₁], by simp [out, s₂], by simp [out], rfl, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s₁, 2, 9, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨s₂, 4, 4, hr₂, hr₃, rfl⟩), rfl⟩)
  · intro r h68 h4 h33
    simp [out, s₂, s₁, h68, h4, h33]

/-- Round a lower numerator down and an upper numerator up after
dividing by the change in scale. -/
@[expose] def rescaleInitBucketSigmaLogBounds (lower upper : ℕ) : Stmt :=
  .assign lower (.bin .div (.reg 31) (.reg 33)) ;;
  .assign upper (.bin .div (.bin .add (.reg 32) (.bin .sub (.reg 33) (.const 1))) (.reg 33))

/-- The rescaled integers bound the original endpoints in the appropriate
direction. -/
theorem rescaleInitBucketSigmaLogBounds_runs
    {w lo hi factor lower upper : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hl : st.regs 31 = lo) (hh : st.regs 32 = hi) (hf : st.regs 33 = factor)
    (h32 : lower ≠ 32) (h33 : lower ≠ 33) (hdu : lower ≠ upper)
    (hpos : 0 < factor) (hw : 1 < 2 ^ w) (hlo : lo < 2 ^ w)
    (hhi : hi + (factor - 1) < 2 ^ w) :
    ∃ out, Runs w p ω (rescaleInitBucketSigmaLogBounds lower upper) st .normal out 13 ∧
      out.regs lower * factor ≤ lo ∧ hi ≤ out.regs upper * factor ∧
      (∀ n, n * factor ≤ lo → n ≤ out.regs lower) ∧
      out.regs upper < 2 ^ w ∧ (∀ n, hi ≤ n * factor → out.regs upper ≤ n) ∧
      out.mem = st.mem ∧ (∀ r, r ≠ lower → r ≠ upper → out.regs r = st.regs r) := by
  let low := lo / factor
  let high := (hi + (factor - 1)) / factor
  have hlow : low < 2 ^ w := (Nat.div_le_self _ _).trans_lt hlo
  have hhigh : high < 2 ^ w := (Nat.div_le_self _ _).trans_lt hhi
  have hsub : factor - 1 < 2 ^ w := by omega
  let mid := {st with regs := Function.update st.regs lower low}
  let out := {mid with regs := Function.update mid.regs upper high}
  have hr₁ : Runs w p ω (.assign lower (.bin .div (.reg 31) (.reg 33))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨low, by simp [Expr.eval, BinOp.eval, hl, hf, low, hlow],
      rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω
      (.assign upper (.bin .div (.bin .add (.reg 32) (.bin .sub (.reg 33) (.const 1))) (.reg 33)))
      mid .normal out 8 :=
    runs_assign_iff.mpr ⟨high, by simp [Expr.eval, BinOp.eval, mid, h32.symm, h33.symm, hh, hf, hsub, hhi, hw,
      high, hhigh], rfl, rfl, rfl⟩
  have hbound : hi ≤ high * factor := by
    have hmod := Nat.mod_lt (hi + (factor - 1)) hpos
    have hsum := Nat.mod_add_div (hi + (factor - 1)) factor
    rw [Nat.mul_comm factor] at hsum
    change (hi + (factor - 1)) % factor + high * factor = hi + (factor - 1) at hsum
    omega
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 4, 8, hr₁, hr₂, rfl⟩),
    by simpa [out, mid, low, Function.update_of_ne hdu] using Nat.div_mul_le_self lo factor,
    by simpa [out] using hbound, ?_, by simpa [out] using hhigh, ?_, rfl, ?_⟩
  · intro n hn
    simpa [out, mid, low, Function.update_of_ne hdu] using (Nat.le_div_iff_mul_le hpos).mpr hn
  · intro n hn
    have ht : hi + (factor - 1) < (n + 1) * factor := by
      rw [Nat.add_mul, one_mul]
      omega
    exact Nat.le_of_lt_succ (by simpa [out, high] using (Nat.div_lt_iff_lt_mul hpos).mpr ht)
  · intro r h26 h27
    simp [out, mid, h26, h27]

/-- Return to the caller's precision and round the schedule logarithm
endpoints in opposite directions. -/
@[expose] def finishInitBucketSigmaLogBounds : Stmt :=
  restoreInitBucketSigmaLogScale ;; rescaleInitBucketSigmaLogBounds 26 27

/-- Outward rounding preserves the enclosure of the logarithm at the
original scale. -/
theorem finishInitBucketSigmaLogBounds_runs {w precision lo hi : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {value : ℝ}
    (hP : st.regs 30 = precision) (hden : st.regs 43 = 2 ^ (7 * precision))
    (h31 : st.regs 31 = lo) (h32 : st.regs 32 = hi) (hwidth : 7 * precision < w)
    (hw : 1 < 2 ^ w) (hlo : lo < 2 ^ w)
    (hhi : hi + (2 ^ (6 * precision) - 1) < 2 ^ w)
    (hlower : (lo : ℝ) / (2 : ℝ) ^ (7 * precision) ≤ value)
    (hupper : value ≤ (hi : ℝ) / (2 : ℝ) ^ (7 * precision)) :
    ∃ out, Runs w p ω finishInitBucketSigmaLogBounds st .normal out 26 ∧
      (out.regs 26 : ℝ) / (2 : ℝ) ^ precision ≤ value ∧
      value ≤ (out.regs 27 : ℝ) / (2 : ℝ) ^ precision ∧
      (∀ n, hi ≤ n * 2 ^ (6 * precision) → out.regs 27 ≤ n) ∧
      out.regs 68 = precision ∧ out.regs 4 = 2 ^ precision ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 68 → r ≠ 4 → r ≠ 33 → r ≠ 26 → r ≠ 27 → out.regs r = st.regs r) := by
  obtain ⟨mid, hr, hp, hs, hfactor, hm, hk⟩ :=
    restoreInitBucketSigmaLogScale_runs (p := p) (ω := ω) hP hden hwidth
  obtain ⟨out, hr', hlo', hhi', _, _, hround, hm', hk'⟩ :=
    rescaleInitBucketSigmaLogBounds_runs (p := p) (ω := ω) (lower := 26) (upper := 27)
      ((hk 31 (by decide) (by decide) (by decide)).trans h31)
      ((hk 32 (by decide) (by decide) (by decide)).trans h32)
      hfactor (by decide) (by decide) (by decide) (by positivity) hw hlo hhi
  have hscale (n : ℕ) :
      (n : ℝ) / (2 : ℝ) ^ precision =
        ((n * 2 ^ (6 * precision) : ℕ) : ℝ) / (2 : ℝ) ^ (7 * precision) := by
    push_cast
    rw [show 7 * precision = precision + 6 * precision by omega, pow_add,
      mul_div_mul_right _ _ (by positivity)]
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 12, 13, hr, hr', rfl⟩),
    ?_, ?_, hround, (hk' 68 (by decide) (by decide)).trans hp,
    (hk' 4 (by decide) (by decide)).trans hs, hm'.trans hm, ?_⟩
  · rw [hscale]
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hlo') (by positivity)).trans hlower
  · rw [hscale]
    exact hupper.trans (div_le_div_of_nonneg_right (by exact_mod_cast hhi') (by positivity))
  · intro r h68 h4 h33 h26 h27
    exact (hk' r h26 h27).trans (hk r h68 h4 h33)

/-- Compute both logarithms and return the enclosing words at the base scale. -/
@[expose] def computeInitBucketSigmaLogsAtBaseScale (load log pack : ℕ) : Stmt :=
  computeInitBucketSigmaLogs load log pack ;; finishInitBucketSigmaLogBounds

/-- The logarithm of the schedule base is enclosed at the restored
precision, and the heap is ready for the next initialization call. -/
theorem computeInitBucketSigmaLogsAtBaseScale_runs
    {w h load log pack lo hi basePrecision limbs heap range accuracy : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {σ : ℝ}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h accuracy))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (h45 : st.regs 45 = lo) (h46 : st.regs 46 = hi) (hs : st.regs 4 = 2 ^ (7 * basePrecision))
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = (7 * basePrecision))
    (hh : st.regs 98 = heap) (hE : st.regs 97 = range) (hq : st.regs 100 = accuracy)
    (hwlo : lo < 2 ^ w) (hwhi : hi < 2 ^ w) (hwidth : (7 * basePrecision) < w)
    (hflo : 2 * lo < Num.capacity h limbs) (hfhi : 2 * hi < Num.capacity h limbs)
    (hsfit : 2 * 2 ^ (7 * basePrecision) < Num.capacity h limbs)
    (hroom : heap + 2 * (limbs + limbs + Num.logarithmSpace limbs (7 * basePrecision) range) < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ (7 * basePrecision))
    (hacc : accuracy + range + 10 ≤ (7 * basePrecision)) (hqPos : 1 ≤ accuracy)
    (hcap : (7 * basePrecision) + range + 4 ≤ h * limbs) (hprec : 2 * (7 * basePrecision) + 9 < 2 ^ w)
    (h30 : st.regs 30 = basePrecision) (h43 : st.regs 43 = 2 ^ (7 * basePrecision))
    (hbound : (range + 1) * 2 ^ (7 * basePrecision) + (2 ^ (6 * basePrecision) - 1) < 2 ^ w)
    (htwo : 2 ≤ (lo : ℝ) / (2 : ℝ) ^ (7 * basePrecision))
    (hlo : (lo : ℝ) / (2 : ℝ) ^ (7 * basePrecision) ≤ σ)
    (hhi : σ ≤ (hi : ℝ) / (2 : ℝ) ^ (7 * basePrecision))
    (hmax : (hi : ℝ) / (2 : ℝ) ^ (7 * basePrecision) ≤ (2 : ℝ) ^ range) :
    ∃ out c ret, Runs w p ω (computeInitBucketSigmaLogsAtBaseScale load log pack) st .normal out c ∧
      (out.regs 26 : ℝ) / (2 : ℝ) ^ basePrecision ≤ Real.log σ ∧
      Real.log σ ≤ (out.regs 27 : ℝ) / (2 : ℝ) ^ basePrecision ∧
      out.regs 27 ≤ (range + 1) * 2 ^ basePrecision ∧
      out.regs 4 = 2 ^ basePrecision ∧ out.regs 68 = basePrecision ∧
      out.regs 99 = ret ∧ heap ≤ ret ∧
      ret ≤ heap + 2 * (limbs + limbs + Num.logarithmSpace limbs (7 * basePrecision) range) ∧
      (∀ r, r ∉ ([2, 3, 4, 26, 27, 31, 32, 33, 36, 68, 95, 96, 98, 99] : List ℕ) →
        out.regs r = st.regs r) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      c ≤ 142 * limbs + 2 * Num.logarithmCost limbs (7 * basePrecision) range + 173 := by
  obtain ⟨mid, c, ret, hr, hlo', hhi', hu, hret, hretLo, hretHi, hk, hf, hz', hc⟩ :=
    computeInitBucketSigmaLogs_runs (ω := ω) hload hlog hpack h45 h46 hs hL hP hh hE hq
      hwlo hwhi hwidth hflo hfhi hsfit hroom hz hdiv hacc hqPos hcap hprec
      ((Nat.le_add_right _ _).trans_lt hbound) htwo hlo hhi hmax
  have hp : (0 : ℝ) < (2 : ℝ) ^ (7 * basePrecision) := by positivity
  have hord : mid.regs 31 ≤ mid.regs 32 := by
    exact_mod_cast (div_le_div_iff_of_pos_right hp).mp (hlo'.trans hhi')
  obtain ⟨out, hr', hlo'', hhi'', hround, hP', hs', hm, hk'⟩ :=
    finishInitBucketSigmaLogBounds_runs (ω := ω)
      ((hk 30 (by decide)).trans h30) ((hk 43 (by decide)).trans h43) rfl rfl hwidth
      (by
        have : 1 ≤ (range + 1) * 2 ^ (7 * basePrecision) :=
          Nat.succ_le_of_lt (by positivity)
        omega)
      (hord.trans_lt (hu.trans_lt ((Nat.le_add_right _ _).trans_lt hbound)))
      ((Nat.add_le_add_right hu _).trans_lt hbound) hlo' hhi'
  refine ⟨out, c + 27, ret, runs_seq_iff.mpr (Or.inr ⟨mid, c, 26, hr, hr', rfl⟩),
    hlo'', hhi'', ?_, hs', hP', (hk' 99 (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hret, hretLo, hretHi, ?_,
    fun a ha => (congrFun hm a).trans (hf a ha), hm.symm ▸ hz', by omega⟩
  · apply hround
    rw [Nat.mul_assoc, ← pow_add, show basePrecision + 6 * basePrecision = 7 * basePrecision by omega]
    exact hu
  · intro r hn
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rcases hn with ⟨h2, h3, h4, h26, h27, h31, h32, h33, h36, h68, h95, h96, h98, h99⟩
    exact (hk' r h68 h4 h33 h26 h27).trans
      (hk r (by simp [h2, h3, h4, h31, h32, h36, h95, h96, h98, h99]))

/-- Prepare the runtime logarithm inputs and return both schedule bounds
at the original precision. -/
@[expose] def initBucketSigmaLogs (bits load log pack : ℕ) : Stmt :=
  prepareInitBucketSigmaLog bits ;; computeInitBucketSigmaLogsAtBaseScale load log pack

/-- The complete schedule logarithm fragment derives the internal range and
restores the original precision after rounding. -/
theorem initBucketSigmaLogs_runs
    {w h bits load log pack lo hi basePrecision limbs heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {σ : ℝ}
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (h45 : st.regs 45 = lo) (h46 : st.regs 46 = hi)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = basePrecision)
    (hh : st.regs 98 = heap)
    (hwlo : lo < 2 ^ w) (hwhi : hi < 2 ^ w) (hwidth : (7 * basePrecision) < w)
    (hflo : 2 * lo < Num.capacity h limbs) (hfhi : 2 * hi < Num.capacity h limbs)
    (hsfit : 2 * 2 ^ (7 * basePrecision) < Num.capacity h limbs)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ (7 * basePrecision))
    (hprec : 2 * (7 * basePrecision) + 9 < 2 ^ w)
    (h43 : st.regs 43 = (2 ^ basePrecision) ^ 7) (hw : 10 < 2 ^ w)
    (htwo : 2 ≤ (lo : ℝ) / (2 : ℝ) ^ (7 * basePrecision))
    (hlo : (lo : ℝ) / (2 : ℝ) ^ (7 * basePrecision) ≤ σ)
    (hhi : σ ≤ (hi : ℝ) / (2 : ℝ) ^ (7 * basePrecision)) :
    let range := hi.size - 7 * basePrecision
    let accuracy := 7 * basePrecision - range - 10
    MeetsContract w p log (Num.logarithmContract w h accuracy) →
    range + 11 ≤ 7 * basePrecision → 7 * basePrecision + range + 4 ≤ h * limbs →
    heap + 2 * (limbs + limbs + Num.logarithmSpace limbs (7 * basePrecision) range) < 2 ^ w →
    (range + 1) * 2 ^ (7 * basePrecision) + (2 ^ (6 * basePrecision) - 1) < 2 ^ w →
    ∃ out c ret, Runs w p ω (initBucketSigmaLogs bits load log pack) st .normal out c ∧
      (out.regs 26 : ℝ) / (2 : ℝ) ^ basePrecision ≤ Real.log σ ∧
      Real.log σ ≤ (out.regs 27 : ℝ) / (2 : ℝ) ^ basePrecision ∧
      out.regs 27 ≤ (range + 1) * 2 ^ basePrecision ∧
      out.regs 4 = 2 ^ basePrecision ∧ out.regs 68 = basePrecision ∧
      out.regs 99 = ret ∧ heap ≤ ret ∧
      ret ≤ heap + 2 * (limbs + limbs + Num.logarithmSpace limbs (7 * basePrecision) range) ∧
      (∀ r, r ∉ ([2, 3, 4, 26, 27, 30, 31, 32, 33, 36, 95, 96, 97, 98, 99, 100] : List ℕ) →
        out.regs r = st.regs r) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      c ≤ 142 * limbs + 2 * Num.logarithmCost limbs (7 * basePrecision) range + 14 * hi.size + 205 := by
  dsimp only
  intro hlog hacc hcap hroom hbound
  obtain ⟨mid, c₁, hr₁, h30, h68, hs, h97, h100, hmax, hqPos, hacc', hm, hk, hc₁⟩ :=
    prepareInitBucketSigmaLog_runs (ω := ω) hbits hP h46 h43 hw hwidth hwhi hacc
  have hden : mid.regs 43 = 2 ^ (7 * basePrecision) := by
    rw [(hk 43 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h43,
      ← pow_mul, Nat.mul_comm]
  obtain ⟨out, c₂, ret, hr₂, hlo', hhi', hu, hs', hp', hret, hretLo, hretHi, hk', hf, hz', hc₂⟩ :=
    computeInitBucketSigmaLogsAtBaseScale_runs (ω := ω) hload hlog hpack
      ((hk 45 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h45)
      ((hk 46 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h46) hs
      ((hk 67 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL) h68
      ((hk 98 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh)
      h97 h100 hwlo hwhi hwidth hflo hfhi hsfit hroom (hm.symm ▸ hz) hdiv
      hacc' hqPos hcap hprec h30 hden hbound htwo hlo hhi hmax
  refine ⟨out, c₁ + c₂ + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩),
    hlo', hhi', hu, hs', hp', hret, hretLo, hretHi, ?_,
    fun a ha => (hf a ha).trans (congrFun hm a), hz', by omega⟩
  intro r hn
  by_cases he : r = 68
  · subst r
    exact hp'.trans hP.symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rcases hn with ⟨h2, h3, h4, h26, h27, h30, h31, h32, h33, h36, h95, h96, h97, h98, h99, h100⟩
    exact (hk' r (by simp [h2, h3, h4, h26, h27, h31, h32, h33, h36, he, h95, h96, h98, h99])).trans
      (hk r h30 he h4 h97 h100)

end MinCostFlow.MinRatio
