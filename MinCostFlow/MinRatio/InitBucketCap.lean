module

public import MinCostFlow.Chain.ConcreteDefs
import MinCostFlow.MinRatio.InitBucketCeiling
public import MinCostFlow.MinRatio.InitStretch
public import MinCostFlow.MinRatio.InitThreshold
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Initialization of the sparse-core bucket bound

Compute the vertex bound used in the bucket count and certify the ceiling
in the bucket bound from scaled endpoints.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain SparseCore

/-- Compute the vertex bound used by the concrete configuration from the
base edge bound in register 22. -/
@[expose] def initBucketVertexBound : Stmt :=
  .assign 46 (.bin .mul (.const 4) (.reg 22))

/-- The bucket calculation uses the configuration's vertex bound, four
times the base edge bound. -/
theorem initBucketVertexBound_runs {w M : ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} (hM : st.regs 22 = M) (hw : 4 < 2 ^ w)
    (hfit : 4 * M < 2 ^ w) :
    ∃ out, Runs w p ω initBucketVertexBound st .normal out 4 ∧
      out.regs 46 = 4 * M ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 46 → out.regs r = st.regs r) := by
  let out := {st with regs := Function.update st.regs 46 (4 * M)}
  exact ⟨out, runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hM, hw, hfit],
    rfl, rfl, rfl⟩, by simp [out], rfl, fun r hr => by simp [out, hr]⟩

/-- Store the clipped lower and upper logarithm numerators from the
approximation and absolute error in registers 2 and 3. -/
@[expose] def storeInitBucketLogBounds (lower upper : ℕ) : Stmt :=
  .assign lower (.bin .sub (.reg 2) (.reg 3)) ;;
  .assign upper (.bin .add (.reg 2) (.reg 3))

/-- The two words bound any nonnegative logarithm within the given error. -/
theorem storeInitBucketLogBounds_runs
    {w lower upper approx error scale : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {value : ℝ} (hvalue : 0 ≤ value)
    (happrox : st.regs 2 = approx) (herr : st.regs 3 = error)
    (h₂ : lower ≠ 2) (h₃ : lower ≠ 3) (hd : lower ≠ upper)
    (hfit : approx + error < 2 ^ w)
    (hclose : |(approx : ℝ) / scale - value| ≤ (error : ℝ) / scale) :
    ∃ out, Runs w p ω (storeInitBucketLogBounds lower upper) st .normal out 9 ∧
      out.regs lower = approx - error ∧ out.regs upper = approx + error ∧
      (out.regs lower : ℝ) / scale ≤ value ∧ value ≤ (out.regs upper : ℝ) / scale ∧
      out.mem = st.mem ∧ (∀ r, r ≠ lower → r ≠ upper → out.regs r = st.regs r) := by
  let mid := {st with regs := Function.update st.regs lower (approx - error)}
  let out := {mid with regs := Function.update mid.regs upper (approx + error)}
  have hsub : approx - error < 2 ^ w := by omega
  have hr₁ : Runs w p ω (.assign lower (.bin .sub (.reg 2) (.reg 3))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, happrox, herr, hsub],
      rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign upper (.bin .add (.reg 2) (.reg 3))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, mid, Ne.symm h₂, Ne.symm h₃, happrox, herr, hfit],
      rfl, rfl, rfl⟩
  have hlo : out.regs lower = approx - error := by simp [out, mid, hd]
  have hhi : out.regs upper = approx + error := by simp [out]
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 4, 4, hr₁, hr₂, rfl⟩), hlo, hhi, ?_, ?_, rfl, ?_⟩
  · rw [hlo]
    by_cases he : error ≤ approx
    · rw [Nat.cast_sub he, sub_div]
      linarith only [(abs_le.mp hclose).2]
    · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero, zero_div]
      exact hvalue
  · rw [hhi, Nat.cast_add, add_div]
    linarith only [(abs_le.mp hclose).1]
  · intro r hl hu
    simp [out, mid, hl, hu]

/-- Read a cached logarithm and form its scaled lower and upper bounds. -/
@[expose] def unpackInitBucketLogBounds (pack lower upper : ℕ) : Stmt :=
  prepareInitLogEnclosure pack ;; storeInitBucketLogBounds lower upper

/-- A positive logarithm with a word-sized error interval can be unpacked
without changing its fixed-point scale. -/
theorem unpackInitBucketLogValueBounds_runs
    {w h pack lower upper ret limbs precision accuracy : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {value : ℝ}
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hret : st.regs 99 = ret) (hL : st.regs 67 = limbs)
    (hP : st.regs 68 = precision) (hq : st.regs 100 = accuracy)
    (hle : limbs ≤ ret) (hw : ret < 2 ^ w) (hwidth : precision < w)
    (hv : Num.Valid st.mem (ret - limbs) h limbs)
    (hqpos : 1 ≤ accuracy) (hqprec : accuracy ≤ precision)
    (hlog : (1 / 2 : ℝ) ≤ Real.log value)
    (herr : |Num.fixVal st.mem (ret - limbs) h limbs precision - Real.log value| ≤
      1 / (2 : ℝ) ^ accuracy)
    (h₂ : lower ≠ 2) (h₃ : lower ≠ 3) (hd : lower ≠ upper)
    (h₄ : lower ≠ 4) (hu₄ : upper ≠ 4) :
    let approx := (Num.intVal st.mem (ret - limbs) h limbs).toNat
    let error := 2 ^ (precision - accuracy)
    approx + error < 2 ^ w →
    ∃ out c, Runs w p ω (unpackInitBucketLogBounds pack lower upper) st .normal out c ∧
      (out.regs lower : ℝ) / (2 ^ precision : ℕ) ≤ Real.log value ∧
      Real.log value ≤ (out.regs upper : ℝ) / (2 ^ precision : ℕ) ∧
      out.regs lower = approx - error ∧ out.regs upper = approx + error ∧ out.regs 4 = 2 ^ precision ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ lower → r ≠ upper → out.regs r = st.regs r) ∧
      c ≤ 25 * limbs + 33 := by
  dsimp only
  intro hfit
  obtain ⟨mid, c, hr, ha, he, hs, hclose, hk, hm, hc⟩ :=
    prepareInitLogValueEnclosure_runs (ω := ω) hpack hret hL hP hq hle hw hwidth hv
      hqpos hqprec hlog herr ((Nat.le_add_right _ _).trans_lt hfit)
  obtain ⟨out, hr', hlow, hu, hlo, hhi, hm', hk'⟩ :=
    storeInitBucketLogBounds_runs (ω := ω) (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hlog)
      ha he h₂ h₃ hd hfit hclose
  exact ⟨out, c + 10, runs_seq_iff.mpr (Or.inr ⟨mid, c, 9, hr, hr', rfl⟩),
    hlo, hhi, hlow, hu, (hk' 4 h₄.symm hu₄.symm).trans hs, hm'.trans hm,
    fun r h2 h3 h4 hl hu => (hk' r hl hu).trans (hk r h2 h3 h4), by omega⟩

/-- Unpacking a cached logarithm adds a second copy of its error to
each side of the enclosure. The saturated lower word still meets the
same error bound. -/
theorem initDepthLogEndpointError {value : ℝ} {approx error scale : ℕ}
    (hs : 0 < scale)
    (hclose : |(approx : ℝ) / scale - value| ≤ (error : ℝ) / scale) :
    value - 2 * ((error : ℝ) / scale) ≤ ((approx - error : ℕ) : ℝ) / scale ∧
      ((approx + error : ℕ) : ℝ) / scale ≤ value + 2 * ((error : ℝ) / scale) := by
  have h := abs_le.mp hclose
  have hsub : (approx : ℝ) - error ≤ ((approx - error : ℕ) : ℝ) := by
    by_cases he : error ≤ approx
    · rw [Nat.cast_sub he]
    · have ht : (approx : ℝ) ≤ error := by exact_mod_cast (Nat.le_of_not_ge he)
      exact (sub_nonpos.mpr ht).trans (Nat.cast_nonneg _)
  have hreal : (0 : ℝ) ≤ scale := by exact_mod_cast hs.le
  have hlow := div_le_div_of_nonneg_right hsub hreal
  rw [sub_div] at hlow
  push_cast
  rw [add_div]
  exact ⟨by linarith only [h.1, hlow], by linarith only [h.2]⟩

/-- The two-sided endpoint error depends on the requested logarithm
accuracy once the working scale is canceled. -/
theorem initDepthLogEndpointError_scale {precision accuracy : ℕ} (hacc : accuracy ≤ precision) :
    2 * ((2 ^ (precision - accuracy) : ℕ) : ℝ) / ((2 ^ precision : ℕ) : ℝ) =
      2 / (2 : ℝ) ^ accuracy := by
  push_cast
  have hpow : (2 : ℝ) ^ precision = (2 : ℝ) ^ (precision - accuracy) * (2 : ℝ) ^ accuracy := by
    rw [← pow_add, Nat.sub_add_cancel hacc]
  rw [hpow]
  have hn : (2 : ℝ) ^ (precision - accuracy) ≠ 0 := by positivity
  field_simp

/-- The cached result gives word endpoints for the logarithm of `N + 2`. -/
theorem unpackInitBucketLogBounds_runs
    {w h pack lower upper ret limbs precision accuracy N : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hret : st.regs 99 = ret) (hL : st.regs 67 = limbs)
    (hP : st.regs 68 = precision) (hq : st.regs 100 = accuracy)
    (hle : limbs ≤ ret) (hw : ret < 2 ^ w) (hwidth : precision < w)
    (hv : Num.Valid st.mem (ret - limbs) h limbs)
    (hqpos : 1 ≤ accuracy) (hqprec : accuracy ≤ precision)
    (herr : |Num.fixVal st.mem (ret - limbs) h limbs precision - Real.log ((N : ℝ) + 2)| ≤
      1 / (2 : ℝ) ^ accuracy)
    (h₂ : lower ≠ 2) (h₃ : lower ≠ 3) (hd : lower ≠ upper)
    (h₄ : lower ≠ 4) (hu₄ : upper ≠ 4)
    (hfit : (N + 2) * 2 ^ precision < 2 ^ w) :
    ∃ out c, Runs w p ω (unpackInitBucketLogBounds pack lower upper) st .normal out c ∧
      (out.regs lower : ℝ) / (2 ^ precision : ℕ) ≤ Real.log ((N : ℝ) + 2) ∧
      Real.log ((N : ℝ) + 2) ≤ (out.regs upper : ℝ) / (2 ^ precision : ℕ) ∧
      (2 ≤ accuracy → 0 < out.regs lower) ∧
      out.regs upper ≤ (N + 2) * 2 ^ precision ∧ out.regs 4 = 2 ^ precision ∧
      out.mem = st.mem ∧
      (∀ r, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ lower → r ≠ upper → out.regs r = st.regs r) ∧
      c ≤ 25 * limbs + 33 ∧
      Real.log ((N : ℝ) + 2) - 2 * ((2 ^ (precision - accuracy) : ℕ) : ℝ) / (2 ^ precision : ℕ) ≤
        (out.regs lower : ℝ) / (2 ^ precision : ℕ) ∧
      (out.regs upper : ℝ) / (2 ^ precision : ℕ) ≤
        Real.log ((N : ℝ) + 2) + 2 * ((2 ^ (precision - accuracy) : ℕ) : ℝ) / (2 ^ precision : ℕ) := by
  let approx := (Num.intVal st.mem (ret - limbs) h limbs).toNat
  let error : ℕ := 2 ^ (precision - accuracy)
  have hscale : 2 * error ≤ 2 ^ precision := by
    dsimp [error]
    rw [← pow_succ']
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hscaled := (initVertexLog_scaledError hqpos hqprec herr).2
  have hbound : approx + error ≤ (N + 2) * 2 ^ precision :=
    initLogUpper_le_scaledInput (by positivity) hscale
      (by simpa only [approx, error, Nat.cast_pow, Nat.cast_ofNat] using hscaled)
  have hlog : (1 / 2 : ℝ) ≤ Real.log ((N : ℝ) + 2) := by
    have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
    exact htwo.trans (Real.log_le_log (by norm_num) (by
      linarith only [Nat.cast_nonneg (α := ℝ) N]))
  obtain ⟨out, c, hr, hlo, hhi, hlow, hu, hs, hm, hk, hc⟩ :=
    unpackInitBucketLogValueBounds_runs (ω := ω) hpack hret hL hP hq hle hw hwidth hv
      hqpos hqprec hlog herr h₂ h₃ hd h₄ hu₄ (hbound.trans_lt hfit)
  have hscaledClose : |(approx : ℝ) / (2 ^ precision : ℕ) - Real.log ((N : ℝ) + 2)| ≤
      (error : ℝ) / (2 ^ precision : ℕ) := by
    simpa only [approx, error, Nat.cast_pow, Nat.cast_ofNat] using hscaled
  obtain ⟨hel, heu⟩ := initDepthLogEndpointError (by positivity : 0 < (2 : ℕ)^precision) hscaledClose
  refine ⟨out, c, hr, hlo, hhi, ?_, hu ▸ hbound, hs, hm, hk, hc, ?_, ?_⟩
  rotate_left
  · simpa only [hlow, mul_div_assoc, error] using hel
  · simpa only [hu, mul_div_assoc, error] using heu
  intro hacc
  have he : (4 : ℝ) * (error : ℝ) ≤ 2 ^ precision := by
    exact_mod_cast (show 4 * error ≤ 2 ^ precision by
      dsimp [error]
      rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega))
  have hlogStrict : (1 / 2 : ℝ) < Real.log ((N : ℝ) + 2) :=
    (by linarith only [Real.log_two_gt_d9] : (1 / 2 : ℝ) < Real.log 2).trans_le
      (Real.log_le_log (by norm_num) (by linarith only [Nat.cast_nonneg (α := ℝ) N]))
  have hsPos : (0 : ℝ) < (2 : ℝ) ^ precision := by positivity
  have hstrict : (error : ℝ) < approx := by
    have hclose : Real.log ((N : ℝ) + 2) - (approx : ℝ) / (2 : ℝ) ^ precision ≤
        (error : ℝ) / (2 : ℝ) ^ precision := by
      have := (abs_le.mp hscaled).1
      simp only [approx, error, Nat.cast_pow, Nat.cast_ofNat]
      linarith only [this]
    have hquarter : (error : ℝ) / (2 : ℝ) ^ precision ≤ 1 / 4 :=
      (div_le_iff₀ hsPos).mpr (by linarith only [he])
    by_contra! hn
    have hsmall := div_le_div_of_nonneg_right hn hsPos.le
    linarith only [hsmall, hclose, hquarter, hlogStrict]
  rw [hlow]
  exact Nat.sub_pos_of_lt (by exact_mod_cast hstrict)

/-- Evaluate the logarithm at the runtime input and return word endpoints. -/
@[expose] def computeInitBucketLogBounds (bits load log pack lower upper : ℕ) : Stmt :=
  cacheInitVertexLog bits load log ;; unpackInitBucketLogBounds pack lower upper

/-- The endpoints enclose the logarithm of the runtime input plus two.
The fresh heap returned by the logarithm is available for later calls. -/
theorem computeInitBucketLogBounds_runs
    {w h bits load log pack lower upper N precision limbs heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (N + 2).size - 10)))
    (hN : st.regs 92 = N) (hs : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision) (hh : st.regs 98 = heap)
    (hw : N + 2 < 2 ^ w) (hword : (N + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((N + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hroom : heap + limbs + limbs + Num.logarithmSpace limbs precision (N + 2).size < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : (N + 2).size + 11 ≤ precision) (hcap : precision + (N + 2).size + 4 ≤ h * limbs)
    (hprec : 2 * precision + 9 < 2 ^ w) (hwidth : precision < w)
    (h₂ : lower ≠ 2) (h₃ : lower ≠ 3) (hd : lower ≠ upper)
    (h₄ : lower ≠ 4) (hu₄ : upper ≠ 4) (h₉₉ : lower ≠ 99) (hu₉₉ : upper ≠ 99) :
    ∃ out c ret, Runs w p ω (computeInitBucketLogBounds bits load log pack lower upper) st .normal out c ∧
      (out.regs lower : ℝ) / (2 ^ precision : ℕ) ≤ Real.log ((N : ℝ) + 2) ∧
      Real.log ((N : ℝ) + 2) ≤ (out.regs upper : ℝ) / (2 ^ precision : ℕ) ∧
      (2 ≤ precision - (N + 2).size - 10 → 0 < out.regs lower) ∧
      out.regs upper ≤ (N + 2) * 2 ^ precision ∧ out.regs 4 = 2 ^ precision ∧
      out.regs 99 = ret ∧ heap + limbs ≤ ret ∧
      ret ≤ heap + limbs + limbs + Num.logarithmSpace limbs precision (N + 2).size ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 95, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ lower → r ≠ upper → out.regs r = st.regs r) ∧
      c ≤ 71 * limbs + Num.logarithmCost limbs precision (N + 2).size + 14 * (N + 2).size + 93 ∧
      let error := 2 / (2 : ℝ) ^ (precision - (N + 2).size - 10)
      Real.log ((N : ℝ) + 2) - error ≤ (out.regs lower : ℝ) / (2 ^ precision : ℕ) ∧
      (out.regs upper : ℝ) / (2 ^ precision : ℕ) ≤ Real.log ((N : ℝ) + 2) + error := by
  obtain ⟨mid, c₁, ret, hr₁, hret, hq, hretLo, hretHi, hretSpace, hv, herr, hk, hframe, hzero, hc₁⟩ :=
    cacheInitVertexLog_runs (ω := ω) hbits hload hlog hN hs hL hP hh hw hword hfit
      hroom hz hdiv hacc hcap hprec
  obtain ⟨out, c₂, hr₂, hlo, hhi, hpos, hu, hscale, hm, hk', hc₂, hel, heu⟩ :=
    unpackInitBucketLogBounds_runs (ω := ω) hpack hret
      ((hk 67 (Or.inl (by decide))).trans hL) ((hk 68 (Or.inl (by decide))).trans hP)
      hq (by omega) hretHi hwidth hv (by omega) (by omega) herr h₂ h₃ hd h₄ hu₄ hword
  rw [initDepthLogEndpointError_scale (by omega :
    precision - (N + 2).size - 10 ≤ precision)] at hel heu
  exact ⟨out, c₁ + c₂ + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, c₁, c₂, hr₁, hr₂, rfl⟩),
    hlo, hhi, hpos, hu, hscale, (hk' 99 (by decide) (by decide) (by decide)
      h₉₉.symm hu₉₉.symm).trans hret, hretLo, hretSpace,
    fun a ha => (congrFun hm a).trans (hframe a ha), hm.symm ▸ hzero,
    fun r hr h2 h3 h4 hl hu => (hk' r h2 h3 h4 hl hu).trans (hk r (Or.inl hr)), by omega, hel, heu⟩

/-- Use the returned heap for the next logarithm and set its argument
to two, using the zero offset in the shared logarithm routine. -/
@[expose] def prepareInitBucketLogTwo : Stmt :=
  .assign 98 (.reg 99) ;; .assign 92 (.const 0)

/-- Preparing the second call preserves both endpoints from the first call. -/
theorem prepareInitBucketLogTwo_runs {w heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} (hh : st.regs 99 = heap) :
    ∃ out, Runs w p ω prepareInitBucketLogTwo st .normal out 5 ∧
      out.regs 98 = heap ∧ out.regs 92 = 0 ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 98 → r ≠ 92 → out.regs r = st.regs r) := by
  let mid := {st with regs := Function.update st.regs 98 heap}
  let out := {mid with regs := Function.update mid.regs 92 0}
  have hr₁ : Runs w p ω (.assign 98 (.reg 99)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hh], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 92 (.const 0)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, show 0 < 2 ^ w by positivity], rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, 2, hr₁, hr₂, rfl⟩),
    by simp [out, mid], by simp [out], rfl, ?_⟩
  intro r h98 h92
  simp [out, mid, h98, h92]

/-- Enclose the logarithms of the vertex bound plus two and of two. -/
@[expose] def computeInitBucketBaseLogs (bits load log pack : ℕ) : Stmt :=
  computeInitBucketLogBounds bits load log pack 26 27 ;;
  prepareInitBucketLogTwo ;;
  computeInitBucketLogBounds bits load log pack 28 29

/-- The two resulting intervals share the runtime scale and the second
logarithm allocates after the first. -/
theorem computeInitBucketBaseLogs_runs
    {w h bits load log pack N precision limbs heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hlogN : MeetsContract w p log (Num.logarithmContract w h (precision - (N + 2).size - 10)))
    (hlogTwo : MeetsContract w p log (Num.logarithmContract w h (precision - 2 - 10)))
    (hN : st.regs 92 = N) (hs : st.regs 4 = 2 ^ precision)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision) (hh : st.regs 98 = heap)
    (hw : N + 2 < 2 ^ w) (hword : (N + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((N + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision) (hwidth : precision < w)
    (hacc : (N + 2).size + 11 ≤ precision) (hcap : precision + (N + 2).size + 4 ≤ h * limbs)
    (hprec : 2 * precision + 9 < 2 ^ w) :
    let spaceN := limbs + limbs + Num.logarithmSpace limbs precision (N + 2).size
    let spaceTwo := limbs + limbs + Num.logarithmSpace limbs precision 2
    heap + spaceN + spaceTwo < 2 ^ w →
    ∃ out c ret, Runs w p ω (computeInitBucketBaseLogs bits load log pack) st .normal out c ∧
      (out.regs 26 : ℝ) / (2 ^ precision : ℕ) ≤ Real.log ((N : ℝ) + 2) ∧
      Real.log ((N : ℝ) + 2) ≤ (out.regs 27 : ℝ) / (2 ^ precision : ℕ) ∧
      (out.regs 28 : ℝ) / (2 ^ precision : ℕ) ≤ Real.log 2 ∧
      Real.log 2 ≤ (out.regs 29 : ℝ) / (2 ^ precision : ℕ) ∧
      (14 ≤ precision → 0 < out.regs 28) ∧
      out.regs 27 ≤ (N + 2) * 2 ^ precision ∧ out.regs 29 ≤ 2 * 2 ^ precision ∧
      out.regs 4 = 2 ^ precision ∧ out.regs 99 = ret ∧
      heap ≤ ret ∧ ret ≤ heap + spaceN + spaceTwo ∧ ZeroFrom out.mem ret ∧
      (∀ a < heap, out.mem a = st.mem a) ∧
      (∀ r < 95, r ∉ ([2, 3, 4, 26, 27, 28, 29, 92] : List ℕ) → out.regs r = st.regs r) ∧
      c ≤ 142 * limbs + Num.logarithmCost limbs precision (N + 2).size +
        Num.logarithmCost limbs precision 2 + 14 * (N + 2).size + 221 := by
  dsimp only
  intro hroom
  obtain ⟨mid, c₁, next, hr₁, h26, h27, _, huN, hs₁, hn, hnLo, hnHi, hm₁, hz₁, hk₁, hc₁, _, _⟩ :=
    computeInitBucketLogBounds_runs (ω := ω) (lower := 26) (upper := 27)
      hbits hload hpack hlogN hN hs hL hP hh hw hword hfit (by omega)
      hz hdiv hacc hcap hprec hwidth (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  obtain ⟨ready, hr₂, hh₂, hN₂, hm₂, hk₂⟩ := prepareInitBucketLogTwo_runs (ω := ω) hn
  have hsize : 2 ≤ (N + 2).size := by
    have hb : 1 < (N + 2).size := Nat.lt_size.mpr (show 2 ^ 1 ≤ N + 2 by omega)
    omega
  have hwordTwo : (0 + 2) * 2 ^ precision < 2 ^ w :=
    (Nat.mul_le_mul_right _ (by omega)).trans_lt hword
  have hfitTwo : 2 * ((0 + 2) * 2 ^ precision) < Num.capacity h limbs :=
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))).trans_lt hfit
  have roomTwo : next + limbs + limbs + Num.logarithmSpace limbs precision 2 < 2 ^ w := by
    omega
  have accTwo : 2 + 11 ≤ precision := by omega
  have capTwo : precision + 2 + 4 ≤ h * limbs := by omega
  obtain ⟨out, c₂, ret, hr₃, h28, h29, hTwoPos, huTwo, hs₂, hout, hretLo, hretHi, hm₃, hz₃, hk₃, hc₂, _, _⟩ :=
    computeInitBucketLogBounds_runs (ω := ω) (lower := 28) (upper := 29) (N := 0) (precision := precision)
      hbits hload hpack hlogTwo hN₂ ((hk₂ 4 (by decide) (by decide)).trans hs₁)
      ((hk₂ 67 (by decide) (by decide)).trans ((hk₁ 67 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans hL))
      ((hk₂ 68 (by decide) (by decide)).trans ((hk₁ 68 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans hP))
      hh₂ (by omega) hwordTwo hfitTwo roomTwo (hm₂.symm ▸ hz₁) hdiv accTwo capTwo
      hprec hwidth (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hk (r : ℕ) (hr : r < 95) (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r ≠ 4)
      (h28 : r ≠ 28) (h29 : r ≠ 29) (h92 : r ≠ 92) : out.regs r = mid.regs r :=
    (hk₃ r hr h2 h3 h4 h28 h29).trans (hk₂ r (by omega) h92)
  change ret ≤ next + limbs + limbs + Num.logarithmSpace limbs precision 2 at hretHi
  change c₂ ≤ 71 * limbs + Num.logarithmCost limbs precision 2 + 14 * 2 + 93 at hc₂
  refine ⟨out, c₁ + (5 + c₂ + 1) + 1, ret, ?_, ?_, ?_, ?_, ?_, ?_, ?_, huTwo,
    hs₂, hout, by omega, by omega, hz₃, ?_, ?_, by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, c₁, _, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨ready, 5, c₂, hr₂, hr₃, rfl⟩), rfl⟩)
  · simpa only [hk 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)] using h26
  · simpa only [hk 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)] using h27
  · simpa only [Nat.cast_zero, zero_add] using h28
  · simpa only [Nat.cast_zero, zero_add] using h29
  · intro hp
    apply hTwoPos
    change 2 ≤ precision - 2 - 10
    omega
  · exact (hk 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).le.trans huN
  · intro a ha
    exact (hm₃ a (by omega)).trans ((congrFun hm₂ a).trans (hm₁ a ha))
  · intro r hr hn
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rcases hn with ⟨h2, h3, h4, h26, h27, h28, h29, h92⟩
    exact (hk r hr h2 h3 h4 h28 h29 h92).trans (hk₁ r hr h2 h3 h4 h26 h27)

/-- Raise the scaled logarithm endpoints to the sixth power and multiply
by the coefficient and branch count to enclose the bucket schedule base. -/
theorem initBucketSigma_bounds (C : ℝ) (N k scale cLo cHi logLo logHi : ℕ)
    (hs : 0 < (scale : ℝ))
    (hcLo : (cLo : ℝ) / scale ≤ mwuK0 C)
    (hcHi : mwuK0 C ≤ (cHi : ℝ) / scale)
    (hlLo : (logLo : ℝ) / scale ≤ Real.log ((N : ℝ) + 2))
    (hlHi : Real.log ((N : ℝ) + 2) ≤ (logHi : ℝ) / scale) :
    let base := max (2 : ℝ) (max 1 (mwuK0 C * (k : ℝ) * Real.log ((N : ℝ) + 2) ^ 6))
    let den := (scale : ℝ) ^ 7
    (max (2 * scale ^ 7) (cLo * k * logLo ^ 6) : ℕ) / den ≤ base ∧
      base ≤ (max (2 * scale ^ 7) (cHi * k * logHi ^ 6) : ℕ) / den := by
  have hd : 0 < (scale : ℝ) ^ 7 := pow_pos hs _
  have hlog : 0 ≤ Real.log ((N : ℝ) + 2) := by
    apply Real.log_nonneg
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hlo := mul_le_mul
    (mul_le_mul_of_nonneg_right hcLo (Nat.cast_nonneg k))
    (pow_le_pow_left₀ (by positivity) hlLo 6)
    (by positivity) (by positivity [mwuK0_pos C])
  have hhi := mul_le_mul
    (mul_le_mul_of_nonneg_right hcHi (Nat.cast_nonneg k))
    (pow_le_pow_left₀ hlog hlHi 6) (pow_nonneg hlog 6) (by positivity)
  have hrepack (c l : ℕ) :
      (c : ℝ) / scale * (k : ℝ) * ((l : ℝ) / scale) ^ 6 =
        ((c * k * l ^ 6 : ℕ) : ℝ) / (scale : ℝ) ^ 7 := by
    push_cast
    field_simp
  rw [hrepack] at hlo hhi
  have hmax (c l : ℕ) :
      ((max (2 * scale ^ 7) (c * k * l ^ 6) : ℕ) : ℝ) / (scale : ℝ) ^ 7 =
        max 2 (((c * k * l ^ 6 : ℕ) : ℝ) / (scale : ℝ) ^ 7) := by
    push_cast
    rw [← max_div_div_right hd.le, mul_div_cancel_right₀ _ hd.ne']
  dsimp only
  rw [hmax, hmax, ← max_assoc, max_eq_left (by norm_num : (1 : ℝ) ≤ 2)]
  exact ⟨max_le_max le_rfl hlo, max_le_max le_rfl hhi⟩

/-- Set the bucket schedule denominator and its doubled numerator. -/
@[expose] def initBucketSigmaScale (power : ℕ) : Stmt :=
  .call 43 power [.reg 4, .const 7] ;;
  .assign 42 (.bin .mul (.const 2) (.reg 43))

/-- Both scaled outputs use the runtime fixed-point denominator in register 4. -/
theorem initBucketSigmaScale_runs {w power scale : ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} (hpower : MeetsContract w p power (initStretchPowerContract w))
    (hs : st.regs 4 = scale) (hpos : 0 < scale)
    (hw : 7 < 2 ^ w) (hfit : 2 * scale ^ 7 < 2 ^ w) :
    ∃ out c, Runs w p ω (initBucketSigmaScale power) st .normal out c ∧
      out.regs 43 = scale ^ 7 ∧ out.regs 42 = 2 * scale ^ 7 ∧
      (∀ r, r ≠ 42 → r ≠ 43 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ c ≤ 154 := by
  have hpow : scale ^ 7 < 2 ^ w := by omega
  have hscale : scale < 2 ^ w :=
    (by simpa using Nat.pow_le_pow_right hpos (show 1 ≤ 7 by decide) :
      scale ≤ scale ^ 7).trans_lt hpow
  have hargs : evalArgs w st [.reg 4, .const 7] = some [scale, 7] := by
    simp [evalArgs, Expr.eval, hs, hw]
  have hwords : ∀ a ∈ [scale, 7], a < 2 ^ w := by
    intro a ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hscale
    · exact hw
  obtain ⟨mid, c, ret, hr, hp, hret, hkeep, hcost⟩ :=
    runs_call_of_meetsContract (r := 43) hpower hargs hwords
      ⟨scale, 7, rfl, hpos, hpow⟩ ω
  obtain ⟨hm, hretVal⟩ := hp
  change ret = scale ^ 7 at hretVal
  change c ≤ 2 + (20 * 7 + 6) + 1 at hcost
  let out := {mid with regs := Function.update mid.regs 42 (2 * scale ^ 7)}
  have hr' : Runs w p ω (.assign 42 (.bin .mul (.const 2) (.reg 43))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, hret, hretVal, hfit, show 2 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  refine ⟨out, c + 5, runs_seq_iff.mpr (Or.inr ⟨mid, c, 4, hr, hr', rfl⟩),
    by simp [out, hret, hretVal], by simp [out], ?_, hm, ?_⟩
  · intro r h₄₂ h₄₃
    simpa [out, h₄₂] using hkeep r h₄₃
  · omega

/-- Form one scaled bucket schedule endpoint. Register 40 holds the cube
of the logarithm numerator. -/
@[expose] def computeInitBucketSigmaEndpoint (coefficientReg logReg dest : ℕ) : Stmt :=
  .assign 40 (.bin .mul (.bin .mul (.reg logReg) (.reg logReg)) (.reg logReg)) ;;
  .assign dest (.bin .mul (.bin .mul (.reg coefficientReg) (.reg 38)) (.bin .mul (.reg 40) (.reg 40))) ;;
  .assign dest (.bin .add (.reg 42) (.bin .sub (.reg dest) (.reg 42)))

/-- The endpoint equals the larger of twice the common denominator and
the product of the scaled coefficient, branch count, and logarithm power. -/
theorem computeInitBucketSigmaEndpoint_runs
    {w coefficient k logNumerator twiceDen coefficientReg logReg dest : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hcoeff : coefficientReg ≠ 40) (hdenReg : (42 : ℕ) ≠ dest)
    (hc : st.regs coefficientReg = coefficient) (hk : st.regs 38 = k)
    (hl : st.regs logReg = logNumerator) (hd : st.regs 42 = twiceDen)
    (hsq : logNumerator ^ 2 < 2 ^ w) (hcu : logNumerator ^ 3 < 2 ^ w)
    (hsix : logNumerator ^ 6 < 2 ^ w) (hck : coefficient * k < 2 ^ w)
    (hprod : coefficient * k * logNumerator ^ 6 < 2 ^ w) (hden : twiceDen < 2 ^ w) :
    ∃ out, Runs w p ω (computeInitBucketSigmaEndpoint coefficientReg logReg dest) st .normal out 22 ∧
      out.regs dest = max twiceDen (coefficient * k * logNumerator ^ 6) ∧
      (∀ r, r ≠ 40 → r ≠ dest → out.regs r = st.regs r) ∧ out.mem = st.mem := by
  let cube := logNumerator ^ 3
  let product := coefficient * k * logNumerator ^ 6
  let s₁ := {st with regs := Function.update st.regs 40 cube}
  let s₂ := {s₁ with regs := Function.update s₁.regs dest product}
  let out := {s₂ with regs := Function.update s₂.regs dest (max twiceDen product)}
  have hpow : cube * cube = logNumerator ^ 6 := by
    dsimp [cube]
    rw [← pow_add]
  have hsub : product - twiceDen < 2 ^ w := (Nat.sub_le ..).trans_lt hprod
  have hm : max twiceDen product < 2 ^ w := max_lt hden hprod
  have hmax : twiceDen + (product - twiceDen) = max twiceDen product := by omega
  have hr₁ : Runs w p ω
      (.assign 40 (.bin .mul (.bin .mul (.reg logReg) (.reg logReg)) (.reg logReg))) st .normal s₁ 6 :=
    runs_assign_iff.mpr ⟨cube, by
      simp [Expr.eval, BinOp.eval, hl, ← pow_two, ← pow_succ, hsq, hcu, cube],
      rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω
      (.assign dest (.bin .mul (.bin .mul (.reg coefficientReg) (.reg 38)) (.bin .mul (.reg 40) (.reg 40))))
      s₁ .normal s₂ 8 :=
    runs_assign_iff.mpr ⟨product, by simp [Expr.eval, BinOp.eval, s₁, hc, hk, hcoeff, hpow, hck, hsix,
      hprod, product], rfl, rfl, rfl⟩
  have hr₃ : Runs w p ω
      (.assign dest (.bin .add (.reg 42) (.bin .sub (.reg dest) (.reg 42)))) s₂ .normal out 6 :=
    runs_assign_iff.mpr ⟨max twiceDen product, by
      simp [Expr.eval, BinOp.eval, s₂, s₁, hdenReg, show (42 : ℕ) ≠ 40 by decide, hd, hsub, hmax, hm], rfl, rfl, rfl⟩
  refine ⟨out, ?_, by simp [out, product], ?_, rfl⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s₁, 6, 15, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨s₂, 8, 6, hr₂, hr₃, rfl⟩), by decide⟩)
  · intro r h40 hdest
    simp [out, s₂, s₁, h40, hdest]

/-- Compute both endpoints with one common denominator. Registers 45 and
46 receive the lower and upper numerators. -/
@[expose] def computeInitBucketSigma (power : ℕ) : Stmt :=
  initBucketSigmaScale power ;;
  computeInitBucketSigmaEndpoint 34 26 45 ;;
  computeInitBucketSigmaEndpoint 35 27 46

/-- The two calls enclose the same bucket schedule base at runtime. -/
theorem computeInitBucketSigma_runs
    (C : ℝ) (N k scale cLo cHi logLo logHi : ℕ)
    {w power : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hpower : MeetsContract w p power (initStretchPowerContract w))
    (hs : st.regs 4 = scale) (hsPos : 0 < scale)
    (h34 : st.regs 34 = cLo) (h35 : st.regs 35 = cHi)
    (h26 : st.regs 26 = logLo) (h27 : st.regs 27 = logHi) (h38 : st.regs 38 = k)
    (hcLo : (cLo : ℝ) / scale ≤ mwuK0 C) (hcHi : mwuK0 C ≤ (cHi : ℝ) / scale)
    (hlLo : (logLo : ℝ) / scale ≤ Real.log ((N : ℝ) + 2))
    (hlHi : Real.log ((N : ℝ) + 2) ≤ (logHi : ℝ) / scale)
    (hw : 7 < 2 ^ w) (hden : 2 * scale ^ 7 < 2 ^ w)
    (hlo : logLo ^ 2 < 2 ^ w ∧ logLo ^ 3 < 2 ^ w ∧ logLo ^ 6 < 2 ^ w ∧
      cLo * k < 2 ^ w ∧ cLo * k * logLo ^ 6 < 2 ^ w)
    (hhi : logHi ^ 2 < 2 ^ w ∧ logHi ^ 3 < 2 ^ w ∧ logHi ^ 6 < 2 ^ w ∧
      cHi * k < 2 ^ w ∧ cHi * k * logHi ^ 6 < 2 ^ w) :
    let base := max (2 : ℝ) (max 1 (mwuK0 C * (k : ℝ) * Real.log ((N : ℝ) + 2) ^ 6))
    ∃ out c, Runs w p ω (computeInitBucketSigma power) st .normal out c ∧
      (out.regs 45 : ℝ) / out.regs 43 ≤ base ∧ base ≤ (out.regs 46 : ℝ) / out.regs 43 ∧
      out.regs 45 = max (2 * scale ^ 7) (cLo * k * logLo ^ 6) ∧
      out.regs 46 = max (2 * scale ^ 7) (cHi * k * logHi ^ 6) ∧
      out.regs 43 = scale ^ 7 ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 40 → r ≠ 42 → r ≠ 43 → r ≠ 45 → r ≠ 46 → out.regs r = st.regs r) ∧
      c ≤ 200 := by
  obtain ⟨s₁, c, hr₁, hd, h42, hk₁, hm₁, hcost⟩ :=
    initBucketSigmaScale_runs (ω := ω) hpower hs hsPos hw hden
  obtain ⟨s₂, hr₂, h45, hk₂, hm₂⟩ :=
    computeInitBucketSigmaEndpoint_runs (ω := ω) (dest := 45) (by decide) (by decide)
      ((hk₁ 34 (by decide) (by decide)).trans h34)
      ((hk₁ 38 (by decide) (by decide)).trans h38)
      ((hk₁ 26 (by decide) (by decide)).trans h26) h42
      hlo.1 hlo.2.1 hlo.2.2.1 hlo.2.2.2.1 hlo.2.2.2.2 hden
  have hk₁₂ (r : ℕ) (h40 : r ≠ 40) (h42 : r ≠ 42) (h43 : r ≠ 43) (h45 : r ≠ 45) :
      s₂.regs r = st.regs r := (hk₂ r h40 h45).trans (hk₁ r h42 h43)
  obtain ⟨out, hr₃, h46, hk₃, hm₃⟩ :=
    computeInitBucketSigmaEndpoint_runs (ω := ω) (dest := 46) (by decide) (by decide)
      ((hk₁₂ 35 (by decide) (by decide) (by decide) (by decide)).trans h35)
      ((hk₁₂ 38 (by decide) (by decide) (by decide) (by decide)).trans h38)
      ((hk₁₂ 27 (by decide) (by decide) (by decide) (by decide)).trans h27)
      ((hk₂ 42 (by decide) (by decide)).trans h42)
      hhi.1 hhi.2.1 hhi.2.2.1 hhi.2.2.2.1 hhi.2.2.2.2 hden
  have h43 := (hk₃ 43 (by decide) (by decide)).trans ((hk₂ 43 (by decide) (by decide)).trans hd)
  have h45' := (hk₃ 45 (by decide) (by decide)).trans h45
  have hb := initBucketSigma_bounds C N k scale cLo cHi logLo logHi
    (by exact_mod_cast hsPos) hcLo hcHi hlLo hlHi
  refine ⟨out, c + 46, ?_, ?_, ?_, h45', h46, h43, hm₃.trans (hm₂.trans hm₁), ?_, by omega⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s₁, c, 45, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨s₂, 22, 22, hr₂, hr₃, rfl⟩), rfl⟩)
  · simpa only [h43, h45', Nat.cast_pow] using hb.1
  · simpa only [h43, h46, Nat.cast_pow] using hb.2
  · intro r h40 h42 h43 h45 h46
    exact (hk₃ r h40 h46).trans (hk₁₂ r h40 h42 h43 h45)

/-- Bound the argument of the bucket ceiling using scaled bounds on the
two logarithms. The lower endpoint uses the larger denominator. -/
theorem initBucketRatio_bounds (σ : ℝ) (psi depth scale sigLo sigHi twoLo twoHi : ℕ)
    (hs : 0 < (scale : ℝ)) (hTwoPos : 0 < twoLo)
    (hSigLo : (sigLo : ℝ) / scale ≤ Real.log σ)
    (hSigHi : Real.log σ ≤ (sigHi : ℝ) / scale)
    (hTwoLo : (twoLo : ℝ) / scale ≤ Real.log 2)
    (hTwoHi : Real.log 2 ≤ (twoHi : ℝ) / scale) :
    let nLo := 2 * psi * scale + depth * sigLo
    let nHi := 2 * psi * scale + depth * sigHi
    let value := (2 * max 0 (psi : ℝ) + (depth : ℝ) * Real.log σ) / Real.log 2
    (nLo : ℝ) / twoHi ≤ value ∧ value ≤ (nHi : ℝ) / twoLo := by
  dsimp only
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hTwoLoPos : 0 < (twoLo : ℝ) / scale := div_pos (by exact_mod_cast hTwoPos) hs
  have hTwoHiPos : 0 < (twoHi : ℝ) / scale := hlog.trans_le hTwoHi
  have hnum (n : ℕ) :
      ((2 * psi * scale + depth * n : ℕ) : ℝ) / scale =
        2 * (psi : ℝ) + (depth : ℝ) * ((n : ℝ) / scale) := by
    push_cast
    rw [add_div, mul_div_cancel_right₀ _ hs.ne', mul_div_assoc]
  have hlo : ((2 * psi * scale + depth * sigLo : ℕ) : ℝ) / scale ≤
      2 * max 0 (psi : ℝ) + (depth : ℝ) * Real.log σ := by
    rw [hnum, max_eq_right (Nat.cast_nonneg psi)]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hSigLo (Nat.cast_nonneg depth)) _
  have hhi : 2 * max 0 (psi : ℝ) + (depth : ℝ) * Real.log σ ≤
      ((2 * psi * scale + depth * sigHi : ℕ) : ℝ) / scale := by
    rw [hnum, max_eq_right (Nat.cast_nonneg psi)]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hSigHi (Nat.cast_nonneg depth)) _
  constructor
  · rw [← div_div_div_cancel_right₀ hs.ne' _ _]
    exact div_le_div_of_nonneg_left (by positivity) hlog hTwoHi |>.trans
      (div_le_div_of_nonneg_right hlo hlog.le)
  · rw [← div_div_div_cancel_right₀ hs.ne' ((2 * psi * scale + depth * sigHi : ℕ) : ℝ)
      (twoLo : ℝ)]
    exact (div_le_div_of_nonneg_right hhi hlog.le).trans
      (div_le_div_of_nonneg_left (by positivity) hTwoLoPos hTwoLo)

/-- Use the product of the two bounds on `log 2` as the common denominator
for the ceiling check. -/
theorem initBucketRatio_commonDen_bounds (σ : ℝ)
    (psi depth scale sigLo sigHi twoLo twoHi : ℕ)
    (hs : 0 < (scale : ℝ)) (hTwoPos : 0 < twoLo)
    (hSigLo : (sigLo : ℝ) / scale ≤ Real.log σ)
    (hSigHi : Real.log σ ≤ (sigHi : ℝ) / scale)
    (hTwoLo : (twoLo : ℝ) / scale ≤ Real.log 2)
    (hTwoHi : Real.log 2 ≤ (twoHi : ℝ) / scale) :
    let nLo := (2 * psi * scale + depth * sigLo) * twoLo
    let nHi := (2 * psi * scale + depth * sigHi) * twoHi
    let den := twoLo * twoHi
    let value := (2 * max 0 (psi : ℝ) + (depth : ℝ) * Real.log σ) / Real.log 2
    (nLo : ℝ) / den ≤ value ∧ value ≤ (nHi : ℝ) / den := by
  dsimp only
  have hlo : (twoLo : ℝ) ≠ 0 := by positivity
  have hhi : (twoHi : ℝ) ≠ 0 := by
    have hp := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hTwoHi
    intro he
    rw [he, zero_div] at hp
    exact (lt_irrefl 0) hp
  have leftCancel (a : ℝ) : a * twoLo / ((twoLo : ℝ) * twoHi) = a / twoHi := by
    rw [mul_comm (twoLo : ℝ) (twoHi : ℝ), mul_div_mul_right _ _ hlo]
  have rightCancel (a : ℝ) : a * twoHi / ((twoLo : ℝ) * twoHi) = a / twoLo :=
    mul_div_mul_right _ _ hhi
  push_cast
  rw [leftCancel, rightCancel]
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using initBucketRatio_bounds σ psi depth scale sigLo sigHi twoLo twoHi
    hs hTwoPos hSigLo hSigHi hTwoLo hTwoHi

/-- Put the two bucket ceiling numerators and their common denominator
in the registers read by the ceiling check. -/
@[expose] def prepareInitBucketRatio : Stmt :=
  .assign 19 (.bin .mul (.bin .mul (.const 2) (.reg 20)) (.reg 4)) ;;
  .assign 14 (.bin .mul (.bin .add (.reg 19) (.bin .mul (.reg 75) (.reg 26))) (.reg 28)) ;;
  .assign 15 (.bin .mul (.bin .add (.reg 19) (.bin .mul (.reg 75) (.reg 27))) (.reg 29)) ;;
  .assign 16 (.bin .mul (.reg 28) (.reg 29))

/-- The fragment computes the common-denominator bounds with exact word
arithmetic when the intermediate products fit. -/
theorem prepareInitBucketRatio_runs
    {w psi depth scale sigLo sigHi twoLo twoHi : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hpsi : st.regs 20 = psi) (hd : st.regs 75 = depth) (hs : st.regs 4 = scale)
    (h26 : st.regs 26 = sigLo) (h27 : st.regs 27 = sigHi)
    (h28 : st.regs 28 = twoLo) (h29 : st.regs 29 = twoHi)
    (hw : 2 < 2 ^ w) (hPsiWord : 2 * psi < 2 ^ w)
    (hloPos : 0 < twoLo) (hhiPos : 0 < twoHi)
    (hloWord : (2 * psi * scale + depth * sigLo) * twoLo < 2 ^ w)
    (hhiWord : (2 * psi * scale + depth * sigHi) * twoHi < 2 ^ w)
    (hden : twoLo * twoHi < 2 ^ w) :
    ∃ out, Runs w p ω prepareInitBucketRatio st .normal out 29 ∧
      out.regs 14 = (2 * psi * scale + depth * sigLo) * twoLo ∧
      out.regs 15 = (2 * psi * scale + depth * sigHi) * twoHi ∧
      out.regs 16 = twoLo * twoHi ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 19 → out.regs r = st.regs r) := by
  let common := 2 * psi * scale
  let lo := common + depth * sigLo
  let hi := common + depth * sigHi
  have hlo : lo < 2 ^ w := (Nat.le_mul_of_pos_right _ hloPos).trans_lt hloWord
  have hhi : hi < 2 ^ w := (Nat.le_mul_of_pos_right _ hhiPos).trans_lt hhiWord
  have hc : common < 2 ^ w := (Nat.le_add_right ..).trans_lt hlo
  have hls : depth * sigLo < 2 ^ w := (Nat.le_add_left ..).trans_lt hlo
  have hhs : depth * sigHi < 2 ^ w := (Nat.le_add_left ..).trans_lt hhi
  let s₁ := {st with regs := Function.update st.regs 19 common}
  let s₂ := {s₁ with regs := Function.update s₁.regs 14 (lo * twoLo)}
  let s₃ := {s₂ with regs := Function.update s₂.regs 15 (hi * twoHi)}
  let out := {s₃ with regs := Function.update s₃.regs 16 (twoLo * twoHi)}
  have hr₁ : Runs w p ω (.assign 19 (.bin .mul (.bin .mul (.const 2) (.reg 20)) (.reg 4)))
      st .normal s₁ 6 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hpsi, hs, hw, hPsiWord, hc, common],
      rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω
      (.assign 14 (.bin .mul (.bin .add (.reg 19) (.bin .mul (.reg 75) (.reg 26))) (.reg 28)))
      s₁ .normal s₂ 8 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, s₁, hd, h26, h28, hls, show common + depth * sigLo = lo from rfl,
      hlo, show lo * twoLo < 2 ^ w from hloWord],
      rfl, rfl, rfl⟩
  have hr₃ : Runs w p ω
      (.assign 15 (.bin .mul (.bin .add (.reg 19) (.bin .mul (.reg 75) (.reg 27))) (.reg 29)))
      s₂ .normal s₃ 8 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, s₂, s₁, hd, h27, h29, hhs, show common + depth * sigHi = hi from rfl,
      hhi, show hi * twoHi < 2 ^ w from hhiWord],
      rfl, rfl, rfl⟩
  have hr₄ : Runs w p ω (.assign 16 (.bin .mul (.reg 28) (.reg 29))) s₃ .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, s₃, s₂, s₁, h28, h29, hden],
      rfl, rfl, rfl⟩
  refine ⟨out, ?_, by simp [out, s₃, s₂, lo, common], by simp [out, s₃, hi, common],
    by simp [out], rfl, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s₁, 6, 22, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨s₂, 8, 13, hr₂,
        runs_seq_iff.mpr (Or.inr ⟨s₃, 8, 4, hr₃, hr₄, rfl⟩), rfl⟩), rfl⟩)
  · intro r h14 h15 h16 h19
    simp [out, s₃, s₂, s₁, h14, h15, h16, h19]

/-- Check the bucket ceiling from the scaled endpoints in registers 14 and 15
and their common denominator in register 16. The cap is written to register 47. -/
@[expose] def selectInitBucketCap : Stmt :=
  .assign 17 (.bin .div (.bin .sub (.reg 15) (.const 1)) (.reg 16)) ;;
  .assign 18 (.bin .lt (.bin .mul (.reg 17) (.reg 16)) (.reg 14)) ;;
  .assign 47 (.bin .add (.reg 17) (.const 3))

/-- A set flag certifies that the selected bucket cap agrees with the model. -/
theorem selectInitBucketCap_runs
    (C Ψ : ℝ) (M N lo hi scale : ℕ) (hM : 1 ≤ M)
    {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hs : 0 < scale) (hhiPos : 0 < hi)
    (hl : st.regs 14 = lo) (hh : st.regs 15 = hi) (hd : st.regs 16 = scale)
    (hw : 3 < 2 ^ w) (hword : hi + 2 < 2 ^ w) :
    let P := concreteChainParams M hM
    let σ := max (2 : ℝ) (max 1 (mwuK0 C * (P.k : ℝ) * (Real.log ((N : ℝ) + 2)) ^ 6))
    let b := (2 * max 0 Ψ + (P.d : ℝ) * Real.log σ) / Real.log 2
    (lo : ℝ) / scale ≤ b → b ≤ (hi : ℝ) / scale →
    ∃ out, Runs w p ω selectInitBucketCap st .normal out 18 ∧
      (out.regs 18 = 1 → out.regs 47 = concreteBCap C Ψ M N hM) ∧
      (out.regs 18 = 1 ↔ (hi - 1) / scale * scale < lo) ∧
      (∀ r, r ≠ 17 → r ≠ 18 → r ≠ 47 → out.regs r = st.regs r) ∧
      out.mem = st.mem := by
  dsimp only
  intro hlo hhi
  let q := (hi - 1) / scale
  let flag := if q * scale < lo then 1 else 0
  have hq : q ≤ hi - 1 := Nat.div_le_self _ _
  have hcut : q * scale ≤ hi - 1 := Nat.div_mul_le_self _ _
  have hsub : hi - 1 < 2 ^ w := by omega
  have hqw : q < 2 ^ w := by omega
  have hcap : q + 3 < 2 ^ w := by omega
  have hcutw : q * scale < 2 ^ w := by omega
  let s₁ := {st with regs := Function.update st.regs 17 q}
  let s₂ := {s₁ with regs := Function.update s₁.regs 18 flag}
  let out := {s₂ with regs := Function.update s₂.regs 47 (q + 3)}
  have hr₁ : Runs w p ω (.assign 17 (.bin .div (.bin .sub (.reg 15) (.const 1)) (.reg 16)))
      st .normal s₁ 6 :=
    runs_assign_iff.mpr ⟨q, by
      simp [Expr.eval, BinOp.eval, hh, hd, hsub, show 1 < 2 ^ w by omega, q,
        show (hi - 1) / scale < 2 ^ w from hqw], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 18 (.bin .lt (.bin .mul (.reg 17) (.reg 16)) (.reg 14)))
      s₁ .normal s₂ 6 :=
    runs_assign_iff.mpr ⟨flag, by
      by_cases hc : q * scale < lo <;>
        simp [Expr.eval, BinOp.eval, s₁, hd, hl, hcutw, flag, hc,
          show 1 < 2 ^ w by omega, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hr₃ : Runs w p ω (.assign 47 (.bin .add (.reg 17) (.const 3))) s₂ .normal out 4 :=
    runs_assign_iff.mpr ⟨q + 3, by simp [Expr.eval, BinOp.eval, s₂, s₁, hw, hcap],
      rfl, rfl, rfl⟩
  refine ⟨out, ?_, ?_, ?_, ?_, rfl⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s₁, 6, 11, hr₁,
      runs_seq_iff.mpr (Or.inr ⟨s₂, 6, 4, hr₂, hr₃, rfl⟩), rfl⟩)
  · intro hf
    have hc : q * scale < lo := by simpa [out, s₂, flag] using hf
    simpa [out, q] using
      (concreteBCap_eq_of_scaledBounds C Ψ M N lo hi scale hM hs hhiPos hlo hhi hc).symm
  · simp [out, s₂, flag, q]
  · intro r h17 h18 h47
    simp [out, s₂, s₁, h17, h18, h47]

/-- Combine the logarithm bounds and check the bucket cap. -/
@[expose] def computeInitBucketCap : Stmt :=
  prepareInitBucketRatio ;; selectInitBucketCap

/-- Given bounds on the two logarithms, a successful machine check yields
the concrete sparse-core bucket cap. -/
theorem computeInitBucketCap_runs
    (C : ℝ) (M N psi scale sigLo sigHi twoLo twoHi : ℕ) (hM : 1 ≤ M)
    {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hpsi : st.regs 20 = psi) (hd : st.regs 75 = (concreteChainParams M hM).d)
    (hs : st.regs 4 = scale) (hpos : 0 < scale)
    (h26 : st.regs 26 = sigLo) (h27 : st.regs 27 = sigHi)
    (h28 : st.regs 28 = twoLo) (h29 : st.regs 29 = twoHi)
    (hw : 3 < 2 ^ w) (hPsiWord : 2 * psi < 2 ^ w)
    (hTwoPos : 0 < twoLo) (hden : twoLo * twoHi < 2 ^ w) :
    let P := concreteChainParams M hM
    let σ := max (2 : ℝ) (max 1 (mwuK0 C * (P.k : ℝ) * (Real.log ((N : ℝ) + 2)) ^ 6))
    let lo := (2 * psi * scale + P.d * sigLo) * twoLo
    let hi := (2 * psi * scale + P.d * sigHi) * twoHi
    (sigLo : ℝ) / scale ≤ Real.log σ → Real.log σ ≤ (sigHi : ℝ) / scale →
    (twoLo : ℝ) / scale ≤ Real.log 2 → Real.log 2 ≤ (twoHi : ℝ) / scale →
    lo < 2 ^ w → 0 < hi → hi + 2 < 2 ^ w →
    ∃ out, Runs w p ω computeInitBucketCap st .normal out 48 ∧
      (out.regs 18 = 1 → out.regs 47 = concreteBCap C psi M N hM) ∧
      (out.regs 18 = 1 ↔ (hi - 1) / (twoLo * twoHi) * (twoLo * twoHi) < lo) ∧
      (out.regs 18 = 1 ↔ (out.regs 15 - 1) / out.regs 16 * out.regs 16 < out.regs 14) ∧
      out.mem = st.mem ∧
      (∀ r, r ∉ ([14, 15, 16, 17, 18, 19, 47] : List ℕ) → out.regs r = st.regs r) := by
  dsimp only
  intro hSigLo hSigHi hTwoLo hTwoHi hLoWord hHiPos hHiWord
  have hTwoHiPos : 0 < twoHi := by
    by_contra! hz
    have he : twoHi = 0 := by omega
    simp only [he, Nat.cast_zero, zero_div] at hTwoHi
    exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).not_ge hTwoHi
  obtain ⟨mid, hr, h14, h15, h16, hm, hk⟩ :=
    prepareInitBucketRatio_runs (ω := ω) hpsi hd hs h26 h27 h28 h29 (by omega)
      hPsiWord hTwoPos hTwoHiPos hLoWord (by omega) hden
  have hb := initBucketRatio_commonDen_bounds _ psi (concreteChainParams M hM).d
    scale sigLo sigHi twoLo twoHi (by exact_mod_cast hpos) hTwoPos hSigLo hSigHi hTwoLo hTwoHi
  obtain ⟨out, hr', hcap, hflag, hk', hm'⟩ :=
    selectInitBucketCap_runs (ω := ω) C (psi : ℝ) M N _ _ _ hM
      (Nat.mul_pos hTwoPos hTwoHiPos) hHiPos h14 h15 h16 hw hHiWord hb.1 hb.2
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 29, 18, hr, hr', rfl⟩),
    hcap, hflag, ?_, hm'.trans hm, ?_⟩
  · rw [hk' 14 (by decide) (by decide) (by decide), h14,
      hk' 15 (by decide) (by decide) (by decide), h15,
      hk' 16 (by decide) (by decide) (by decide), h16]
    exact hflag
  intro r hn
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  rcases hn with ⟨h14, h15, h16, h17, h18, h19, h47⟩
  exact (hk' r h17 h18 h47).trans (hk r h14 h15 h16 h19)

/-- Once the enclosure is separated from the adjacent integers, the
machine sets the bucket flag and installs the exact model cap. -/
theorem selectInitBucketCap_certified_runs
    (C Ψ : ℝ) (M N lo hi scale : ℕ) (hM : 1 ≤ M)
    {w ceil : ℕ} {error : ℝ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hs : 0 < scale) (hhiPos : 0 < hi) (hc : 0 < ceil)
    (hl : st.regs 14 = lo) (hh : st.regs 15 = hi) (hd : st.regs 16 = scale)
    (hw : 3 < 2 ^ w) (hword : hi + 2 < 2 ^ w) :
    let P := concreteChainParams M hM
    let σ := max (2 : ℝ) (max 1 (mwuK0 C * (P.k : ℝ) * (Real.log ((N : ℝ) + 2)) ^ 6))
    let b := (2 * max 0 Ψ + (P.d : ℝ) * Real.log σ) / Real.log 2
    (lo : ℝ) / scale ≤ b → b ≤ (hi : ℝ) / scale →
    b - error ≤ (lo : ℝ) / scale → (hi : ℝ) / scale ≤ b + error →
    ((ceil - 1 : ℕ) : ℝ) + error < b → b + error ≤ (ceil : ℝ) →
    ∃ out, Runs w p ω selectInitBucketCap st .normal out 18 ∧
      out.regs 18 = 1 ∧ out.regs 47 = concreteBCap C Ψ M N hM ∧
      (∀ r, r ≠ 17 → r ≠ 18 → r ≠ 47 → out.regs r = st.regs r) ∧
      out.mem = st.mem := by
  dsimp only
  intro hlo hhi hloErr hhiErr hprev hnext
  obtain ⟨out, hr, hcap, hflag, hkeep, hm⟩ :=
    selectInitBucketCap_runs C Ψ M N lo hi scale hM hs hhiPos hl hh hd hw hword hlo hhi
  have hcert := hflag.mpr (initBucketCeiling_passes_of_error hc hs hloErr hhiErr hprev hnext)
  exact ⟨out, hr, hcert, hcap hcert, hkeep, hm⟩

end MinCostFlow.MinRatio
