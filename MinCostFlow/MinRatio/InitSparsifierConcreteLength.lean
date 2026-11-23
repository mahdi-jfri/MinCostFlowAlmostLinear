module

public import MinCostFlow.MinRatio.InitSparsifierQueryFactor
public import MinCostFlow.MinRatio.InitBucketAssembly
import MinCostFlow.MinRatio.ShiftForestScan
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Rebuild thresholds from the runtime sparsifier length

Use the squared padded edge cap for the Section 8 factors. The
threshold routine consumes the length endpoints at the working scale.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- After the path calculations, form the sparsifier coefficient and
populate the checked threshold table. -/
@[expose] def initThresholdsAfterLength (power bits load log pack coefficient : ℕ) : Stmt :=
  initSparsifierCoefficient coefficient ;; initThresholdTableFromSparseCoreLog power bits load log pack

/-- The threshold calculation retains both query-factor endpoints. -/
theorem initThresholdsAfterLength_preserves_query
    {w power bits load log pack coefficient cost : ℕ} {p : Program} {ω : ℕ → Bool}
    {st out : State} {outcome : Outcome}
    (hr : Runs w p ω (initThresholdsAfterLength power bits load log pack coefficient)
      st outcome out cost) :
    out.regs 114 = st.regs 114 ∧ out.regs 115 = st.regs 115 := by
  have hframe : writesBelow 114 (initThresholdsAfterLength power bits load log pack coefficient) = true := rfl
  exact ⟨runs_preserves_above (by decide) hframe hr, runs_preserves_above (by decide) hframe hr⟩

/-- The coefficient stage preserves both length bounds and hands the
threshold routine the same heap. -/
theorem initThresholdsAfterLength_runs
    {w power bits load log pack coefficient scale heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {post : State → Prop} {budget : ℕ}
    (hs : st.regs 4 = scale) (hsPos : 0 < scale) (hh : st.regs 98 = heap)
    (hlog : 0 < st.regs 28 ∧ (st.regs 28 : ℝ) / scale ≤ Real.log 2 ∧
      Real.log 2 ≤ (st.regs 29 : ℝ) / scale)
    (hw : coefficient < 2 ^ w) (hword : scale + coefficient * scale * scale + (st.regs 28 - 1) < 2 ^ w)
    (htable : ∀ ready,
      (ready.regs 49 : ℝ) / scale ≤ 1 + coefficient / Real.log 2 →
      1 + coefficient / Real.log 2 ≤ (ready.regs 51 : ℝ) / scale →
      ready.mem = st.mem →
      (∀ r, r ≠ 37 → r ≠ 49 → r ≠ 51 → ready.regs r = st.regs r) →
      ready.regs 98 = heap →
      ∃ out cost, Runs w p ω (initThresholdTableFromSparseCoreLog power bits load log pack)
        ready .normal out cost ∧ post out ∧ cost ≤ budget) :
    ∃ out cost, Runs w p ω (initThresholdsAfterLength power bits load log pack coefficient) st .normal out cost ∧
      post out ∧ cost ≤ budget + 25 := by
  have hsReal : (0 : ℝ) < scale := by exact_mod_cast hsPos
  have hord : st.regs 28 ≤ st.regs 29 := by
    exact_mod_cast (div_le_div_iff_of_pos_right hsReal).mp (hlog.2.1.trans hlog.2.2)
  obtain ⟨ready, hr₁, lb, ub, _, _, hm, hk⟩ :=
    initSparsifierCoefficient_runs (p := p) (ω := ω) hs rfl rfl hsPos hlog.1 hord
      hlog.2.1 hlog.2.2 hw hword
  obtain ⟨out, cost, hr₂, hp, hcost⟩ :=
    htable ready lb ub hm hk ((hk 98 (by decide) (by decide) (by decide)).trans hh)
  exact ⟨out, 24 + cost + 1, runs_seq_iff.mpr (Or.inr ⟨ready, 24, cost, hr₁, hr₂, rfl⟩), hp, by omega⟩

/-- At precision at least sixteen, the log-two enclosure produced by
the logarithm routine lies above half the scale at its lower endpoint.
Its endpoint gap in integer units is independent of the precision. -/
theorem initCoefficientLogTwo_bounds {precision lo hi : ℕ}
    (hprec : 16 ≤ precision)
    (hlo : Real.log 2 - 2 / (2 : ℝ) ^ (precision - 12) ≤ (lo : ℝ) / (2 : ℕ) ^ precision)
    (hhi : (hi : ℝ) / (2 : ℕ) ^ precision ≤ Real.log 2 + 2 / (2 : ℝ) ^ (precision - 12)) :
    2 ^ precision ≤ 2 * lo ∧ hi - lo ≤ 16384 := by
  let scale : ℝ := 2 ^ precision
  have hs : 0 < scale := by dsimp [scale]; positivity
  have hden : (16 : ℝ) ≤ 2 ^ (precision - 12) := by
    calc
      16 = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have herr : 2 / (2 : ℝ) ^ (precision - 12) ≤ 1 / 8 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hden]
  push_cast at hlo hhi
  change Real.log 2 - 2 / (2 : ℝ) ^ (precision - 12) ≤ (lo : ℝ) / scale at hlo
  change (hi : ℝ) / scale ≤ Real.log 2 + 2 / (2 : ℝ) ^ (precision - 12) at hhi
  have hhalf : (1 / 2 : ℝ) ≤ (lo : ℝ) / scale := by
    linarith only [Real.log_two_gt_d9, herr, hlo]
  have hl := (le_div_iff₀ hs).mp hhalf
  have hcast : (scale : ℝ) ≤ 2 * (lo : ℝ) := by linarith only [hl]
  have hcancel : (2 / (2 : ℝ) ^ (precision - 12)) * scale = 8192 := by
    dsimp [scale]
    rw [show precision = precision - 12 + 12 by omega, pow_add]
    rw [show precision - 12 + 12 - 12 = precision - 12 by omega]
    have hpos : (2 : ℝ) ^ (precision - 12) ≠ 0 := by positivity
    field_simp
    norm_num
  have hdiff : ((hi : ℝ) - lo) / scale ≤ 2 * (2 / (2 : ℝ) ^ (precision - 12)) := by
    rw [sub_div]
    linarith only [hlo, hhi]
  have hdiff' := (div_le_iff₀ hs).mp hdiff
  rw [mul_assoc, hcancel] at hdiff'
  refine ⟨?_, Nat.sub_le_iff_le_add.mpr ?_⟩
  · dsimp [scale] at hcast
    exact_mod_cast hcast
  · have hle : (hi : ℝ) ≤ 16384 + (lo : ℝ) := by linarith only [hdiff']
    exact_mod_cast hle

/-- If the lower logarithm endpoint is at least half the scale, reciprocal
division widens the interval by at most four times the coefficient times
the logarithm gap, plus one unit for each integer rounding. -/
theorem initSparsifierCoefficient_gap
    {coefficient scale logLo logHi : ℕ}
    (hpos : 0 < scale) (hh : scale ≤ 2 * logLo) (hle : logLo ≤ logHi) :
    (scale + (coefficient * scale * scale + (logLo - 1)) / logLo) -
      (scale + coefficient * scale * scale / logHi) ≤
      4 * coefficient * (logHi - logLo) + 2 := by
  let n := coefficient * scale * scale
  have hLo : 0 < logLo := by omega
  have hHi : 0 < logHi := hLo.trans_le hle
  have hl : (0 : ℝ) < logLo := by exact_mod_cast hLo
  have hu : (0 : ℝ) < logHi := by exact_mod_cast hHi
  have hlower : (n : ℝ) / logHi ≤ ((n / logHi : ℕ) : ℝ) + 1 := by
    apply (div_le_iff₀ hu).mpr
    have hlt : n < (n / logHi + 1) * logHi := by
      rw [Nat.add_mul, Nat.one_mul]
      have hmod := Nat.mod_lt n hHi
      have heq := Nat.mod_add_div n logHi
      rw [Nat.mul_comm logHi] at heq
      omega
    exact_mod_cast hlt.le
  have hupper : (((n + (logLo - 1)) / logLo : ℕ) : ℝ) ≤ (n : ℝ) / logLo + 1 := by
    apply Nat.cast_div_le.trans
    apply (div_le_iff₀ hl).mpr
    have hsub : ((logLo - 1 : ℕ) : ℝ) ≤ logLo := by exact_mod_cast Nat.sub_le logLo 1
    rw [Nat.cast_add, add_mul, div_mul_cancel₀ _ hl.ne', one_mul]
    exact add_le_add_right hsub _
  have hprod : (scale : ℝ) * scale ≤ 4 * ((logLo : ℝ) * logHi) := by
    have hl₂ : (scale : ℝ) ≤ 2 * logLo := by exact_mod_cast hh
    have hu₂ : (scale : ℝ) ≤ 2 * logHi := by exact_mod_cast hh.trans (Nat.mul_le_mul_left 2 hle)
    calc
      _ ≤ (2 * (logLo : ℝ)) * (2 * logHi) :=
        mul_le_mul hl₂ hu₂ (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  have hgap : (n : ℝ) / logLo - (n : ℝ) / logHi ≤
      4 * coefficient * (logHi - logLo : ℝ) := by
    rw [div_sub_div _ _ hl.ne' hu.ne']
    apply (div_le_iff₀ (mul_pos hl hu)).mpr
    have hnonneg : 0 ≤ (logHi : ℝ) - logLo := sub_nonneg.mpr (by exact_mod_cast hle)
    have hmul := mul_le_mul_of_nonneg_right hprod (mul_nonneg (Nat.cast_nonneg coefficient) hnonneg)
    push_cast [n]
    linarith only [show (scale : ℝ) * scale * (coefficient * (logHi - logLo : ℝ)) ≤
      4 * ((logLo : ℝ) * logHi) * (coefficient * (logHi - logLo : ℝ)) from hmul]
  have hfinal : (n + (logLo - 1)) / logLo ≤ n / logHi + (4 * coefficient * (logHi - logLo) + 2) := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast [Nat.cast_sub hle]
    linarith only [hupper, hlower, hgap]
  rw [Nat.add_sub_add_left]
  exact Nat.sub_le_iff_le_add.mpr (by simpa [n, Nat.add_comm] using hfinal)

/-- The coefficient routine returns ordered endpoints with an integer
magnitude bound and a precision-independent bound in terms of the input
logarithm gap. -/
theorem initSparsifierCoefficient_withGap_runs
    {w scale logLo logHi coefficient : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hs : st.regs 4 = scale) (h28 : st.regs 28 = logLo) (h29 : st.regs 29 = logHi)
    (hsPos : 0 < scale) (hh : scale ≤ 2 * logLo) (hord : logLo ≤ logHi)
    (hlo : (logLo : ℝ) / scale ≤ Real.log 2)
    (hhi : Real.log 2 ≤ (logHi : ℝ) / scale)
    (hw : coefficient < 2 ^ w)
    (hword : scale + coefficient * scale * scale + (logLo - 1) < 2 ^ w) :
    ∃ out, Runs w p ω (initSparsifierCoefficient coefficient) st .normal out 24 ∧
      (out.regs 49 : ℝ) / scale ≤ 1 + coefficient / Real.log 2 ∧
      1 + coefficient / Real.log 2 ≤ (out.regs 51 : ℝ) / scale ∧
      out.regs 49 ≤ out.regs 51 ∧ out.regs 51 ≤ (2 * coefficient + 2) * scale ∧
      out.regs 51 - out.regs 49 ≤ 4 * coefficient * (logHi - logLo) + 2 ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 37 → r ≠ 49 → r ≠ 51 → out.regs r = st.regs r) := by
  have hloPos : 0 < logLo := by omega
  obtain ⟨out, hr, lb, ub, h49, h51, hm, hf⟩ :=
    initSparsifierCoefficient_runs (p := p) (ω := ω) hs h28 h29 hsPos hloPos hord hlo hhi hw hword
  have hsReal : (0 : ℝ) < scale := by exact_mod_cast hsPos
  have ho : out.regs 49 ≤ out.regs 51 := by
    exact_mod_cast (div_le_div_iff_of_pos_right hsReal).mp (lb.trans ub)
  have hn : coefficient * scale * scale ≤ (2 * coefficient * scale) * logLo := by
    calc
      _ ≤ coefficient * scale * (2 * logLo) := Nat.mul_le_mul_left _ hh
      _ = _ := by ring
  have hquot : (coefficient * scale * scale + (logLo - 1)) / logLo ≤
      2 * coefficient * scale + 1 := by
    apply Nat.div_le_of_le_mul
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm logLo]
    exact Nat.add_le_add hn (Nat.sub_le _ _)
  refine ⟨out, hr, lb, ub, ho, ?_, ?_, hm, hf⟩
  · rw [h51]
    calc
      _ ≤ scale + (2 * coefficient * scale + 1) := Nat.add_le_add_left hquot _
      _ ≤ scale + (2 * coefficient * scale + scale) := by omega
      _ = _ := by ring
  · rw [h49, h51]
    exact initSparsifierCoefficient_gap hsPos hh hord

/-- Compute the logarithm of two and use it to enclose the sparsifier
coefficient at the working scale. Register 92 supplies zero to the
logarithm loader, which adds two. -/
@[expose] def initSparsifierCoefficientFromLogTwo (bits load log pack coefficient : ℕ) : Stmt :=
  computeInitBucketLogBounds bits load log pack 28 29 ;; initSparsifierCoefficient coefficient

/-- The logarithm and coefficient routines together produce an enclosure
with a fixed integer gap bound. -/
theorem initSparsifierCoefficientFromLogTwo_runs
    {w h bits load log pack coefficient precision limbs heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - 12)))
    (h92 : st.regs 92 = 0) (h4 : st.regs 4 = 2 ^ precision)
    (h67 : st.regs 67 = limbs) (h68 : st.regs 68 = precision) (h98 : st.regs 98 = heap)
    (hprec : 16 ≤ precision) (hwidth : precision < w) (hdiv : h ∣ precision)
    (hcap : precision + 6 ≤ h * limbs) (hprecWord : 2 * precision + 9 < 2 ^ w)
    (hfit : 4 * 2 ^ precision < Num.capacity h limbs)
    (hroom : heap + limbs + limbs + Num.logarithmSpace limbs precision 2 < 2 ^ w)
    (hz : ZeroFrom st.mem heap)
    (hword : (coefficient + 3) * (2 ^ precision) ^ 2 < 2 ^ w) :
    ∃ out cost ret, Runs w p ω (initSparsifierCoefficientFromLogTwo bits load log pack coefficient)
      st .normal out cost ∧
      (out.regs 49 : ℝ) / (2 ^ precision : ℕ) ≤ 1 + coefficient / Real.log 2 ∧
      1 + coefficient / Real.log 2 ≤ (out.regs 51 : ℝ) / (2 ^ precision : ℕ) ∧
      out.regs 49 ≤ out.regs 51 ∧ out.regs 51 ≤ (2 * coefficient + 2) * 2 ^ precision ∧
      out.regs 51 - out.regs 49 ≤ 65536 * coefficient + 2 ∧
      out.regs 4 = 2 ^ precision ∧ out.regs 99 = ret ∧
      heap + limbs ≤ ret ∧ ret ≤ heap + limbs + limbs + Num.logarithmSpace limbs precision 2 ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 95, r ∉ ([2, 3, 4, 28, 29, 37, 49, 51] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ 71 * limbs + Num.logarithmCost limbs precision 2 + 146 := by
  let scale := 2 ^ precision
  have hs : 0 < scale := Nat.two_pow_pos _
  have hsq : scale ≤ scale ^ 2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hs (by decide : 1 ≤ 2)
  have hscaled : 2 * scale < 2 ^ w := by
    exact (Nat.mul_le_mul (by omega : 2 ≤ coefficient + 3) hsq).trans_lt hword
  have hlog' : MeetsContract w p log (Num.logarithmContract w h (precision - (0 + 2 : ℕ).size - 10)) := by
    have he : precision - (0 + 2 : ℕ).size - 10 = precision - 12 := by
      change precision - 2 - 10 = precision - 12
      omega
    rw [he]
    exact hlog
  obtain ⟨mid, c, ret, hr, hlo, hhi, _, hupper, hscale, h99, hretLo, hretHi,
    hm, hzero, hf, hc, hel, heu⟩ :=
    computeInitBucketLogBounds_runs (ω := ω) (lower := 28) (upper := 29)
      hbits hload hpack hlog' h92 h4 h67 h68 h98
      ((Nat.le_mul_of_pos_right 2 hs).trans_lt hscaled) hscaled
      (by simpa [← Nat.mul_assoc] using hfit) hroom hz hdiv
      (by change 2 + 11 ≤ precision; omega) hcap hprecWord hwidth
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hreal : (0 : ℝ) < scale := by exact_mod_cast hs
  have hord : mid.regs 28 ≤ mid.regs 29 := by
    exact_mod_cast (div_le_div_iff_of_pos_right hreal).mp (hlo.trans hhi)
  have hlogBounds := initCoefficientLogTwo_bounds hprec (lo := mid.regs 28) (hi := mid.regs 29)
    (by simpa [show (0 + 2 : ℕ).size = 2 by decide, Nat.sub_sub] using hel)
    (by simpa [show (0 + 2 : ℕ).size = 2 by decide, Nat.sub_sub] using heu)
  have hcoeff : coefficient < 2 ^ w :=
    ((Nat.le_add_right coefficient 3).trans
      (Nat.le_mul_of_pos_right _ (Nat.pow_pos hs))).trans_lt hword
  have hdivWord : scale + coefficient * scale * scale + (mid.regs 28 - 1) < 2 ^ w := by
    have hsmall := (Nat.sub_le (mid.regs 28) 1).trans (hord.trans hupper)
    calc
      _ ≤ scale + coefficient * scale * scale + 2 * scale := Nat.add_le_add_left hsmall _
      _ = coefficient * scale ^ 2 + 3 * scale := by ring
      _ ≤ coefficient * scale ^ 2 + 3 * scale ^ 2 :=
        Nat.add_le_add_left (Nat.mul_le_mul_left 3 hsq) _
      _ = (coefficient + 3) * scale ^ 2 := by ring
      _ < _ := hword
  obtain ⟨out, hrun, lb, ub, ho, hu, hg, hm', hf'⟩ :=
    initSparsifierCoefficient_withGap_runs (p := p) (ω := ω)
      hscale rfl rfl hs hlogBounds.1 hord (by simpa using hlo) (by simpa using hhi) hcoeff hdivWord
  have hgap := hg.trans (Nat.add_le_add_right (Nat.mul_le_mul_left (4 * coefficient) hlogBounds.2) 2)
  change c ≤ 71 * limbs + Num.logarithmCost limbs precision 2 + 14 * 2 + 93 at hc
  refine ⟨out, c + 25, ret, runs_seq_iff.mpr (Or.inr ⟨mid, c, 24, hr, hrun, by omega⟩),
    lb, ub, ho, hu, ?_, (hf' 4 (by decide) (by decide) (by decide)).trans hscale,
    (hf' 99 (by decide) (by decide) (by decide)).trans h99, hretLo, hretHi,
    fun a ha => (congrFun hm' a).trans (hm a ha), hm'.symm ▸ hzero, ?_, by omega⟩
  · convert hgap using 1
    ring
  · intro r hrange hnot
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
    obtain ⟨h2, h3, h4r, h28, h29, h37, h49, h51⟩ := hnot
    exact (hf' r h37 h49 h51).trans (hf r hrange h2 h3 h4r h28 h29)

/-- Save the graph vertex count during the log-two computation and use
the returned heap cursor for the next initializer. -/
@[expose] def initRebuildCoefficient (bits load log pack coefficient : ℕ) : Stmt :=
  .assign 57 (.reg 92) ;;
  .assign 92 (.const 0) ;;
  initSparsifierCoefficientFromLogTwo bits load log pack coefficient ;;
  .assign 92 (.reg 57) ;;
  .assign 98 (.reg 99)

/-- Coefficient initialization preserves the graph vertex count and
passes the fresh heap to the next stage. -/
theorem initRebuildCoefficient_runs
    {w h bits load log pack coefficient precision limbs heap N : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - 12)))
    (h92 : st.regs 92 = N) (h4 : st.regs 4 = 2 ^ precision)
    (h67 : st.regs 67 = limbs) (h68 : st.regs 68 = precision) (h98 : st.regs 98 = heap)
    (hprec : 16 ≤ precision) (hwidth : precision < w) (hdiv : h ∣ precision)
    (hcap : precision + 6 ≤ h * limbs) (hprecWord : 2 * precision + 9 < 2 ^ w)
    (hfit : 4 * 2 ^ precision < Num.capacity h limbs)
    (hroom : heap + limbs + limbs + Num.logarithmSpace limbs precision 2 < 2 ^ w)
    (hz : ZeroFrom st.mem heap)
    (hword : (coefficient + 3) * (2 ^ precision) ^ 2 < 2 ^ w) :
    ∃ out cost ret, Runs w p ω (initRebuildCoefficient bits load log pack coefficient)
      st .normal out cost ∧
      (out.regs 49 : ℝ) / (2 ^ precision : ℕ) ≤ 1 + coefficient / Real.log 2 ∧
      1 + coefficient / Real.log 2 ≤ (out.regs 51 : ℝ) / (2 ^ precision : ℕ) ∧
      out.regs 49 ≤ out.regs 51 ∧ out.regs 51 ≤ (2 * coefficient + 2) * 2 ^ precision ∧
      out.regs 51 - out.regs 49 ≤ 65536 * coefficient + 2 ∧
      out.regs 4 = 2 ^ precision ∧ out.regs 98 = ret ∧ out.regs 92 = N ∧
      heap + limbs ≤ ret ∧ ret ≤ heap + limbs + limbs + Num.logarithmSpace limbs precision 2 ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      (∀ r < 95, r ∉ ([2, 3, 4, 28, 29, 37, 49, 51, 57] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ 71 * limbs + Num.logarithmCost limbs precision 2 + 158 := by
  let saved := {st with regs := Function.update st.regs 57 N}
  let ready := {saved with regs := Function.update saved.regs 92 0}
  have hs : Runs w p ω (.assign 57 (.reg 92)) st .normal saved 2 :=
    runs_assign_iff.mpr ⟨N, by simp [Expr.eval, h92], rfl, rfl, rfl⟩
  have h0 : Runs w p ω (.assign 92 (.const 0)) saved .normal ready 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval], rfl, rfl, rfl⟩
  obtain ⟨mid, c, ret, hr, hlo, hhi, horder, hu, hg, hscale, h99, hretLo, hretHi,
    hm, hz', hf, hc⟩ :=
    initSparsifierCoefficientFromLogTwo_runs (ω := ω) (st := ready) hbits hload hpack hlog
      (by simp [ready]) (by simp [ready, saved, h4]) (by simp [ready, saved, h67])
      (by simp [ready, saved, h68]) (by simp [ready, saved, h98])
      hprec hwidth hdiv hcap hprecWord hfit hroom hz hword
  have h57 : mid.regs 57 = N := (hf 57 (by decide) (by decide)).trans (by simp [ready, saved])
  let restored := {mid with regs := Function.update mid.regs 92 N}
  let out := {restored with regs := Function.update restored.regs 98 ret}
  have hrestore : Runs w p ω (.assign 92 (.reg 57)) mid .normal restored 2 :=
    runs_assign_iff.mpr ⟨N, by simp [Expr.eval, h57], rfl, rfl, rfl⟩
  have hheap : Runs w p ω (.assign 98 (.reg 99)) restored .normal out 2 :=
    runs_assign_iff.mpr ⟨ret, by simp [Expr.eval, restored, h99], rfl, rfl, rfl⟩
  refine ⟨out, c + 12, ret, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hretLo, hretHi,
    hm, hz', ?_, by omega⟩
  · refine runs_seq_iff.mpr (Or.inr ⟨saved, 2, c + 9, hs, ?_, by omega⟩)
    refine runs_seq_iff.mpr (Or.inr ⟨ready, 2, c + 6, h0, ?_, by omega⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨mid, c, 5, hr,
      runs_seq_iff.mpr (Or.inr ⟨restored, 2, 2, hrestore, hheap, rfl⟩), by omega⟩)
  · simpa [out, restored] using hlo
  · simpa [out, restored] using hhi
  · simpa [out, restored] using horder
  · simpa [out, restored] using hu
  · simpa [out, restored] using hg
  · simpa [out, restored] using hscale
  · simp [out]
  · simp [out, restored]
  · intro r hrange hn
    by_cases h : r = 92
    · subst r
      simp [out, restored, h92]
    · have h98r : r ≠ 98 := by omega
      have h57r : r ≠ 57 := fun he => hn (he.symm ▸ (by decide : 57 ∈
        ([2, 3, 4, 28, 29, 37, 49, 51, 57] : List ℕ)))
      have hnot : r ∉ ([2, 3, 4, 28, 29, 37, 49, 51] : List ℕ) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn ⊢
        exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1,
          hn.2.2.2.2.2.1, hn.2.2.2.2.2.2.1, hn.2.2.2.2.2.2.2.1⟩
      simpa [out, restored, ready, saved, h, h98r, h57r] using hf r hrange hnot

/-- The coefficient emitted by the threshold prefix encloses the
Section 8 sparsifier's cost coefficient when its numerator is the
fixed product of the decomposition and construction constants. -/
theorem initThresholdCoefficient_bounds {coefficient scale M : ℕ} {st : State}
    (tools : Spanner.SpannerTools) (costs : Spanner.SpannerToolCosts)
    (phi dec : ℝ) (hphi : 0 < phi) (hdec : 0 ≤ dec)
    (hcoeff : (coefficient : ℝ) = tools.decompose.c_ℓ * tools.constructExpander.c_deg)
    (hl : (st.regs 49 : ℝ) / scale ≤ 1 + (coefficient : ℝ) / Real.log 2)
    (hu : 1 + (coefficient : ℝ) / Real.log 2 ≤ (st.regs 51 : ℝ) / scale) :
    let params := Spanner.sparsifyMGParamsOfDecWithTime tools costs phi hphi M dec hdec
    (st.regs 49 : ℝ) / scale ≤ params.K_s ∧ params.K_s ≤ (st.regs 51 : ℝ) / scale := by
  change (st.regs 49 : ℝ) / scale ≤ 1 + tools.decompose.c_ℓ * tools.constructExpander.c_deg / Real.log 2 ∧
    1 + tools.decompose.c_ℓ * tools.constructExpander.c_deg / Real.log 2 ≤ (st.regs 51 : ℝ) / scale
  rw [← hcoeff]
  exact ⟨hl, hu⟩

/-- Use the squared base edge bound for the sparse-core length factor
that enters the rebuild thresholds of Algorithm 2 (page 28). -/
@[expose] def stageInitSparsifierEdgeCap : Stmt :=
  .assign 23 (.bin .mul (.reg 22) (.reg 22))

/-- The sparse-core length calculation receives the runtime squared cap. -/
theorem stageInitSparsifierEdgeCap_runs {w M₀ : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hM : st.regs 22 = M₀) (hfit : M₀ ^ 2 < 2 ^ w) :
    ∃ out, Runs w p ω stageInitSparsifierEdgeCap st .normal out 4 ∧
      out.regs 23 = M₀ ^ 2 ∧ out.mem = st.mem ∧
      (∀ r ≠ 23, out.regs r = st.regs r) := by
  let out := {st with regs := Function.update st.regs 23 (M₀ ^ 2)}
  have hr : Runs w p ω stageInitSparsifierEdgeCap st .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hM, ← pow_two, hfit],
      rfl, rfl, rfl⟩
  exact ⟨out, hr, by simp [out], rfl, fun r h => by simp [out, h]⟩

end MinCostFlow.MinRatio
