module

public import MinCostFlow.MinRatio.InitSparsifierPath
public import MinCostFlow.Expander.DecomposePhiProg

public import MinCostFlow.MinRatio.InitSparsifierConductanceInputs

/-!
# Runtime inputs for the sparsifier path calls

Compute the conductance denominator and witness edge cap from the input
size. Use the working precision to scale both conductances and the fixed
coefficient bounds.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Scale rational bounds on the fixed cited path coefficient. Register
55 holds the runtime scale divided by the bounds' common denominator. -/
@[expose] def initSparsifierPathCoefficient (lower upper : ℕ) : Stmt :=
  .assign 39 (.bin .mul (.const lower) (.reg 55)) ;;
  .assign 40 (.bin .mul (.const upper) (.reg 55))

/-- The coefficient bounds use the caller's runtime scale. The fixed
numerators encode an enclosure of the witness coefficient. -/
theorem initSparsifierPathCoefficient_runs {w lower upper divisor unit : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {K : ℝ}
    (h55 : st.regs 55 = unit) (hu : 0 < unit)
    (hlo : (lower : ℝ) / divisor ≤ max K 1) (hhi : max K 1 ≤ (upper : ℝ) / divisor)
    (hfit : max lower upper * unit < 2 ^ w) :
    ∃ out, Runs w p ω (initSparsifierPathCoefficient lower upper) st .normal out 9 ∧
      (out.regs 39 : ℝ) / ((divisor * unit : ℕ) : ℝ) ≤ max K 1 ∧
      max K 1 ≤ (out.regs 40 : ℝ) / ((divisor * unit : ℕ) : ℝ) ∧
      out.regs 39 = lower * unit ∧ out.regs 40 = upper * unit ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 39 → r ≠ 40 → out.regs r = st.regs r) := by
  have hL := (Nat.mul_le_mul_right unit (le_max_left lower upper)).trans_lt hfit
  have hU := (Nat.mul_le_mul_right unit (le_max_right lower upper)).trans_lt hfit
  have hL' := (Nat.le_mul_of_pos_right lower hu).trans_lt hL
  have hU' := (Nat.le_mul_of_pos_right upper hu).trans_lt hU
  let mid := {st with regs := Function.update st.regs 39 (lower * unit)}
  let out := {mid with regs := Function.update mid.regs 40 (upper * unit)}
  have hr₁ : Runs w p ω (.assign 39 (.bin .mul (.const lower) (.reg 55))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, h55, hL, hL'], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 40 (.bin .mul (.const upper) (.reg 55))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, mid, h55, hU, hU'], rfl, rfl, rfl⟩
  have he₁ : out.regs 39 = lower * unit := by simp [out, mid]
  have he₂ : out.regs 40 = upper * unit := by simp [out]
  have hu' : (unit : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 4, 4, hr₁, hr₂, rfl⟩),
    ?_, ?_, he₁, he₂, rfl, fun r h39 h40 => by simp [out, mid, h39, h40]⟩
  · simpa only [he₁, Nat.cast_mul, mul_div_mul_right _ _ hu'] using hlo
  · simpa only [he₂, Nat.cast_mul, mul_div_mul_right _ _ hu'] using hhi

/-- Divide the runtime scale by the fixed dyadic denominator before
scaling the witness coefficient endpoints. -/
@[expose] def prepareInitSparsifierPathCoefficient (lower upper bits : ℕ) : Stmt :=
  .assign 55 (.bin .div (.reg 4) (.const (2 ^ bits))) ;;
  initSparsifierPathCoefficient lower upper

/-- The endpoint numerators represent the fixed dyadic witnesses at
the runtime precision. -/
theorem prepareInitSparsifierPathCoefficient_runs {w lower upper bits precision : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {K : ℝ}
    (h4 : st.regs 4 = 2 ^ precision) (hbits : bits ≤ precision) (hwidth : precision < w)
    (hlo : (lower : ℝ) / (2 ^ bits : ℕ) ≤ max K 1)
    (hhi : max K 1 ≤ (upper : ℝ) / (2 ^ bits : ℕ))
    (hfit : max lower upper * 2 ^ (precision - bits) < 2 ^ w) :
    ∃ out, Runs w p ω (prepareInitSparsifierPathCoefficient lower upper bits) st .normal out 14 ∧
      (out.regs 39 : ℝ) / (2 ^ precision : ℕ) ≤ max K 1 ∧
      max K 1 ≤ (out.regs 40 : ℝ) / (2 ^ precision : ℕ) ∧
      out.regs 39 = lower * 2 ^ (precision - bits) ∧
      out.regs 40 = upper * 2 ^ (precision - bits) ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 39 → r ≠ 40 → r ≠ 55 → out.regs r = st.regs r) := by
  let unit := 2 ^ (precision - bits)
  have he : (2 : ℕ) ^ bits * unit = 2 ^ precision := by
    rw [show unit = 2 ^ (precision - bits) from rfl, ← pow_add, Nat.add_sub_of_le hbits]
  have hq : (2 : ℕ) ^ precision / 2 ^ bits = unit := by
    rw [← he, Nat.mul_comm, Nat.mul_div_cancel _ (by positivity)]
  have hd := Nat.pow_lt_pow_right (show 1 < 2 by decide) (hbits.trans_lt hwidth)
  have hu : unit < 2 ^ w := Nat.pow_lt_pow_right (by decide)
    ((Nat.sub_le precision bits).trans_lt hwidth)
  let mid := {st with regs := Function.update st.regs 55 unit}
  have hr₁ : Runs w p ω (.assign 55 (.bin .div (.reg 4) (.const (2 ^ bits)))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, h4, hd, hq, hu], rfl, rfl, rfl⟩
  obtain ⟨out, hr₂, lb, ub, h39, h40, hm, hk⟩ :=
    initSparsifierPathCoefficient_runs (p := p) (ω := ω) (st := mid) (divisor := 2 ^ bits) (unit := unit)
      (by simp [mid]) (by change 0 < (2 : ℕ) ^ (precision - bits); positivity) hlo hhi hfit
  rw [he] at lb ub
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 4, 9, hr₁, hr₂, rfl⟩),
    lb, ub, h39, h40, hm, fun r h39' h40' h55 => by simpa [mid, h55] using hk r h39' h40'⟩

/-- Prepare the shared coefficient and conductance words for the two
path calls from the runtime graph size and precision. -/
@[expose] def prepareInitSparsifierLengthInputsWithDegree (K thr c lower upper bits cDeg : ℕ) : Stmt :=
  prepareInitSparsifierPathInputsWithDegree K thr c cDeg ;;
  prepareInitSparsifierPathCoefficient lower upper bits

/-- The setup leaves the path inputs at their common working precision. -/
theorem prepareInitSparsifierLengthInputsWithDegree_runs
    {w K thr c lower upper bits M precision cDeg : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {coefficient : ℝ}
    (hK : 1 ≤ K) (hM : st.regs 23 = M) (hs : st.regs 4 = 2 ^ precision)
    (hm : 4 * M + 2 < 2 ^ w) (hcube : (Nat.log 2 (4 * M + 2) + 2) ^ 3 < 2 ^ w)
    (hcPos : 0 < cDeg) (hcWord : cDeg < 2 ^ w)
    (hcoeff : cDeg * Expander.maxPhiDenOf K thr M < 2 ^ w)
    (hfit : cDeg * Expander.maxPhiDenOf K thr M * M + 1 < 2 ^ w)
    (hden : Expander.maxPhiDenOf K thr M ≤ 2 ^ precision)
    (hround : 2 ^ precision + (Expander.maxPhiDenOf K thr M - 1) < 2 ^ w)
    (hc : 0 < c) (hcScale : c ≤ 2 ^ precision) (hcRound : 2 ^ precision + (c - 1) < 2 ^ w)
    (hbits : bits ≤ precision) (hwidth : precision < w)
    (hlo : (lower : ℝ) / (2 ^ bits : ℕ) ≤ max coefficient 1)
    (hhi : max coefficient 1 ≤ (upper : ℝ) / (2 ^ bits : ℕ))
    (hword : max lower upper * 2 ^ (precision - bits) < 2 ^ w) :
    let scale := (2 : ℕ) ^ precision
    let den := Expander.maxPhiDenOf K thr M
    ∃ out cost, Runs w p ω (prepareInitSparsifierLengthInputsWithDegree K thr c lower upper bits cDeg)
      st .normal out cost ∧
      out.regs 63 = den ∧ out.regs 58 = Spanner.capM_W cDeg (1 / (den : ℝ)) M ∧
      (out.regs 53 : ℝ) / scale ≤ 1 / (den : ℝ) ∧ 1 / (den : ℝ) ≤ (out.regs 54 : ℝ) / scale ∧
      (out.regs 56 : ℝ) / scale ≤ 1 / (c : ℝ) ∧ 1 / (c : ℝ) ≤ (out.regs 57 : ℝ) / scale ∧
      (out.regs 39 : ℝ) / scale ≤ max coefficient 1 ∧ max coefficient 1 ≤ (out.regs 40 : ℝ) / scale ∧
      out.regs 53 = scale / den ∧ out.regs 54 = (scale + (den - 1)) / den ∧
      out.regs 56 = scale / c ∧ out.regs 57 = (scale + (c - 1)) / c ∧
      out.regs 39 = lower * 2 ^ (precision - bits) ∧ out.regs 40 = upper * 2 ^ (precision - bits) ∧
      0 < out.regs 53 ∧ 0 < out.regs 56 ∧ out.mem = st.mem ∧
      (∀ r, r ∉ ([24, 31, 32, 33, 36, 39, 40, 53, 54, 55, 56, 57, 58, 63] : List ℕ) →
        out.regs r = st.regs r) ∧
      cost ≤ 120 * (Nat.log 2 (4 * M + 2) + K * (Expander.rOf (4 * M)) ^ 2 + 4) + 57 := by
  obtain ⟨mid, cost, hr₁, h63, h58, a, b, d, e, h53, h54, h56, h57, hp, hp', hm₁, hk₁, hc₁⟩ :=
    prepareInitSparsifierPathInputsWithDegree_runs (ω := ω) hK hM hs (by positivity)
      hm hcube hcPos hcWord hcoeff hfit hden hround hc hcScale hcRound
  obtain ⟨out, hr₂, lb, ub, h39, h40, hm₂, hk₂⟩ :=
    prepareInitSparsifierPathCoefficient_runs (p := p) (ω := ω)
      ((hk₁ 4 (by decide)).trans hs) hbits hwidth hlo hhi hword
  have h (r : ℕ) (h39 : r ≠ 39) (h40 : r ≠ 40) (h55 : r ≠ 55) := hk₂ r h39 h40 h55
  have h53' := h 53 (by decide) (by decide) (by decide)
  have h54' := h 54 (by decide) (by decide) (by decide)
  have h56' := h 56 (by decide) (by decide) (by decide)
  have h57' := h 57 (by decide) (by decide) (by decide)
  refine ⟨out, cost + 15, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 14, hr₁, hr₂, by omega⟩),
    (h 63 (by decide) (by decide) (by decide)).trans h63,
    (h 58 (by decide) (by decide) (by decide)).trans h58,
    h53'.symm ▸ a, h54'.symm ▸ b, h56'.symm ▸ d, h57'.symm ▸ e, lb, ub,
    h53'.trans h53, h54'.trans h54, h56'.trans h56, h57'.trans h57, h39, h40,
    h53'.symm ▸ hp, h56'.symm ▸ hp', hm₂.trans hm₁, ?_, by omega⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h24, h31, h32, h33, h36, h39', h40', h53'', h54'', h55, h56'', h57'', h58', h63⟩ := hr
  exact (hk₂ r h39' h40' h55).trans
    (hk₁ r (by simp [h24, h31, h32, h33, h36, h53'', h54'', h56'', h57'', h58', h63]))

/-- Prepare the shared coefficient and conductance words for the two
path calls from the runtime graph size and precision. -/
@[expose] def prepareInitSparsifierLengthInputs (K thr c lower upper bits : ℕ) : Stmt :=
  prepareInitSparsifierLengthInputsWithDegree K thr c lower upper bits 36

/-- The setup leaves the path inputs at their common working precision. -/
theorem prepareInitSparsifierLengthInputs_runs
    {w K thr c lower upper bits M precision : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {coefficient : ℝ}
    (hK : 1 ≤ K) (hM : st.regs 23 = M) (hs : st.regs 4 = 2 ^ precision)
    (hm : 4 * M + 2 < 2 ^ w) (hcube : (Nat.log 2 (4 * M + 2) + 2) ^ 3 < 2 ^ w)
    (hcoeff : 36 * Expander.maxPhiDenOf K thr M < 2 ^ w)
    (hfit : 36 * Expander.maxPhiDenOf K thr M * M + 1 < 2 ^ w)
    (hden : Expander.maxPhiDenOf K thr M ≤ 2 ^ precision)
    (hround : 2 ^ precision + (Expander.maxPhiDenOf K thr M - 1) < 2 ^ w)
    (hc : 0 < c) (hcScale : c ≤ 2 ^ precision) (hcRound : 2 ^ precision + (c - 1) < 2 ^ w)
    (hbits : bits ≤ precision) (hwidth : precision < w)
    (hlo : (lower : ℝ) / (2 ^ bits : ℕ) ≤ max coefficient 1)
    (hhi : max coefficient 1 ≤ (upper : ℝ) / (2 ^ bits : ℕ))
    (hword : max lower upper * 2 ^ (precision - bits) < 2 ^ w) :
    let scale := (2 : ℕ) ^ precision
    let den := Expander.maxPhiDenOf K thr M
    ∃ out cost, Runs w p ω (prepareInitSparsifierLengthInputs K thr c lower upper bits)
      st .normal out cost ∧
      out.regs 63 = den ∧ out.regs 58 = Spanner.capM_W 36 (1 / (den : ℝ)) M ∧
      (out.regs 53 : ℝ) / scale ≤ 1 / (den : ℝ) ∧ 1 / (den : ℝ) ≤ (out.regs 54 : ℝ) / scale ∧
      (out.regs 56 : ℝ) / scale ≤ 1 / (c : ℝ) ∧ 1 / (c : ℝ) ≤ (out.regs 57 : ℝ) / scale ∧
      (out.regs 39 : ℝ) / scale ≤ max coefficient 1 ∧ max coefficient 1 ≤ (out.regs 40 : ℝ) / scale ∧
      out.regs 53 = scale / den ∧ out.regs 54 = (scale + (den - 1)) / den ∧
      out.regs 56 = scale / c ∧ out.regs 57 = (scale + (c - 1)) / c ∧
      out.regs 39 = lower * 2 ^ (precision - bits) ∧ out.regs 40 = upper * 2 ^ (precision - bits) ∧
      0 < out.regs 53 ∧ 0 < out.regs 56 ∧ out.mem = st.mem ∧
      (∀ r, r ∉ ([24, 31, 32, 33, 36, 39, 40, 53, 54, 55, 56, 57, 58, 63] : List ℕ) →
        out.regs r = st.regs r) ∧
      cost ≤ 120 * (Nat.log 2 (4 * M + 2) + K * (Expander.rOf (4 * M)) ^ 2 + 4) + 57 := by
  exact prepareInitSparsifierLengthInputsWithDegree_runs hK hM hs hm hcube
    (by decide) (by have := Expander.maxPhiDenOf_pos K thr M; omega)
    hcoeff hfit hden hround hc hcScale hcRound hbits hwidth hlo hhi hword

/-- Prepare both conductance intervals and compute the input graph's
path interval, preserving the witness inputs for the second call. -/
@[expose] def computeInitSparsifierFirstPathWithDegree
    (qEntry bits load log pack exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits cDeg : ℕ) : Stmt :=
  prepareInitSparsifierLengthInputsWithDegree decK thr c coeffLo coeffHi coeffBits cDeg ;;
  computeInitSparsifierCitedPath qEntry bits load log pack exp shiftEntry Kγ c 60 61

/-- A fixed pair of distinct coefficient endpoints cannot supply a
uniform integer gap when Init lifts it to an unbounded working precision. -/
theorem initPathCoefficient_exists_gap_gt {lo hi coeffBits : ℕ}
    (h : lo < hi) (budget : ℕ) :
    ∃ precision ≥ coeffBits,
      budget < hi * 2 ^ (precision - coeffBits) - lo * 2 ^ (precision - coeffBits) := by
  refine ⟨budget + coeffBits, Nat.le_add_left _ _, ?_⟩
  rw [Nat.add_sub_cancel, ← Nat.sub_mul]
  have hmul : 2 ^ budget ≤ (hi - lo) * 2 ^ budget :=
    Nat.le_mul_of_pos_left _ (Nat.sub_pos_of_lt h)
  exact Nat.lt_two_pow_self.trans_le hmul

/-- An integer path coefficient uses a single exact endpoint and leaves
only the logarithm error in the exponent input. -/
theorem initPathIntegerCoefficient_exponent_gap
    {K q exponent scale lo hi err : ℕ}
    (horder : lo ≤ hi) (herr : hi - lo ≤ err) :
    (K * scale) * q * (exponent * hi) - (K * scale) * q * (exponent * lo) ≤
      (q * exponent * K * err) * scale := by
  by_cases hs : scale = 0
  · simp [hs]
  have hlog : hi ≤ hi * scale := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hs)
  have hbound := initSparsifierPathExponent_gap (kLo := K * scale) (kHi := K * scale)
    (logLo := lo) (logHi := hi) (q := q) (exponent := exponent) (scale := scale)
    (kBound := K) (logBound := hi) (kErr := 0) (logErr := err)
    le_rfl horder le_rfl hlog (by simp) herr
  simpa only [zero_mul, zero_add, Nat.mul_assoc] using hbound

/-- Rounding a conductance of the form `1 / den` gives a gap of at
most one integer unit. At scale at least `den`, the lower endpoint
loses at most a factor of two and its rounded reciprocal stays bounded. -/
theorem initPathConductanceWords_bounds {scale den : ℕ}
    (hd : 0 < den) (hs : den ≤ scale) :
    let lo := scale / den
    let hi := (scale + (den - 1)) / den
    hi - lo ≤ 1 ∧ scale ≤ (2 * den) * lo ∧
      (scale * scale + (lo - 1)) / lo ≤ (2 * den + 1) * scale := by
  dsimp only
  let lo := scale / den
  let hi := (scale + (den - 1)) / den
  have hlo : 0 < lo := Nat.div_pos hs hd
  have hmod := Nat.mod_lt scale hd
  have he : scale % den + lo * den = scale := by
    simpa only [lo, Nat.mul_comm den] using Nat.mod_add_div scale den
  have hhi : hi ≤ lo + 1 := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    rw [Nat.succ_mul, Nat.add_mul, Nat.one_mul]
    omega
  have hprod : den ≤ lo * den := Nat.le_mul_of_pos_left _ hlo
  have hlow : scale ≤ (2 * den) * lo := by
    have heq : (2 * den) * lo = lo * den + lo * den := by ring
    rw [heq]
    omega
  have hrec : (scale * scale + (lo - 1)) / lo ≤ (2 * den + 1) * scale := by
    apply Nat.div_le_of_le_mul
    have hn : scale * scale ≤ lo * (2 * den * scale) := by
      exact (Nat.mul_le_mul_right scale hlow).trans_eq (by ring)
    have hrem : lo - 1 ≤ lo * scale :=
      (Nat.sub_le _ _).trans (Nat.le_mul_of_pos_right _ (hd.trans_le hs))
    have hsum := Nat.add_le_add hn hrem
    exact hsum.trans_eq (by ring)
  exact ⟨Nat.sub_le_iff_le_add.mpr (hhi.trans_eq (Nat.add_comm _ _)), hlow, hrec⟩

/-- The first call computes its path enclosure from runtime setup and
leaves the witness cap, conductance and scale ready for the second. -/
theorem computeInitSparsifierFirstPathWithDegree_runs
    {w h Kγ c M precision limbs heap bits load log pack qEntry exp shiftEntry accuracy logLo logHi decK thr coeffLo coeffHi coeffBits cDeg : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {K : ℝ}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (2 * M + 2).size - 10)))
    (hexp : MeetsContract w p exp (Num.positiveExponentialContract w h accuracy))
    (hshift : MeetsContract w p shiftEntry (Num.shiftRightContract w h))
    (hqImpl : MeetsContract w p qEntry (initSparsifierPathQContract w))
    (hq8 : (Expander.PathDSProg.qRoot M + 1) ^ 8 < 2 ^ w)
    (hq2 : Expander.PathDSProg.qRoot M + 2 < 2 ^ w)
    (hM : st.regs 23 = M)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision) (hh : st.regs 98 = heap)
    (hK : Kγ < 2 ^ w) (htriple : 3 * M < 2 ^ w)
    (hcube : (Nat.log 2 (3 * M) + 2) ^ 4 < 2 ^ w)
    (hexpWord : Expander.PathDSProg.csGammaExp Kγ (3 * M) < 2 ^ w) (hw₄ : 4 < 2 ^ w)

    (hwide : precision + precision < w)
    (hsfit : 2 * 2 ^ (precision + precision) < Num.capacity h limbs)
    (h28 : st.regs 28 = logLo) (h29 : st.regs 29 = logHi) (horder : logLo ≤ logHi)
    (hlogFit : Expander.PathDSProg.csGammaExp Kγ (3 * M) * logHi < 2 ^ w)
    (hlLo : (logLo : ℝ) / (2 ^ precision : ℕ) ≤ Real.log 2)
    (hlHi : Real.log 2 ≤ (logHi : ℝ) / (2 ^ precision : ℕ))
    (hc : 0 < c)
    (hw : 2 * M + 2 < 2 ^ w) (hword : (2 * M + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((2 * M + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : (2 * M + 2).size + 11 ≤ precision)
    (hcap : precision + (2 * M + 2).size + 4 ≤ h * limbs)
    (hprecExp : 2 * (precision + precision) + 9 < 2 ^ w) (hwidth : precision < w)
    (hdec : 1 ≤ decK) (h4 : st.regs 4 = 2 ^ precision)
    (hm : 4 * M + 2 < 2 ^ w) (hcubeDec : (Nat.log 2 (4 * M + 2) + 2) ^ 3 < 2 ^ w)
    (hcDegPos : 0 < cDeg) (hcDegWord : cDeg < 2 ^ w)
    (hcoeff : cDeg * Expander.maxPhiDenOf decK thr M < 2 ^ w)
    (hcapFit : cDeg * Expander.maxPhiDenOf decK thr M * M + 1 < 2 ^ w)
    (hden : Expander.maxPhiDenOf decK thr M ≤ 2 ^ precision)
    (hround : 2 ^ precision + (Expander.maxPhiDenOf decK thr M - 1) < 2 ^ w)
    (hcScale : c ≤ 2 ^ precision) (hcRound : 2 ^ precision + (c - 1) < 2 ^ w)
    (hcoeffBits : coeffBits ≤ precision)
    (hcoeffLo : (coeffLo : ℝ) / (2 ^ coeffBits : ℕ) ≤ max K 1)
    (hcoeffHi : max K 1 ≤ (coeffHi : ℝ) / (2 ^ coeffBits : ℕ))
    (hcoeffWord : max coeffLo coeffHi * 2 ^ (precision - coeffBits) < 2 ^ w) :
    let kLo := coeffLo * 2 ^ (precision - coeffBits)
    let kHi := coeffHi * 2 ^ (precision - coeffBits)
    kLo * Expander.qOf M < 2 ^ w → kHi * Expander.qOf M < 2 ^ w →
    let exponent := Expander.PathDSProg.csGammaExp Kγ (3 * M)
    let expLo := kLo * Expander.qOf M * (exponent * logLo)
    let expHi := kHi * Expander.qOf M * (exponent * logHi)
    expHi + 1 < 2 ^ w →
    max expLo expHi < 2 ^ w →
    2 * max expLo expHi < Num.capacity h limbs →
    let range := expHi / 2 ^ (precision + precision) + 1
    accuracy + range + 10 ≤ precision + precision →
    precision + precision + 2 * range + 4 ≤ h * limbs →
    precision + 2 * range ≤ accuracy →
    2 ^ (precision + 2 * range) + 2 < 2 ^ w →
    let space := limbs + limbs + Num.positiveExponentialSpace limbs (precision + precision) range +
      (2 * limbs + 1)
    let afterPower := heap + space + space
    afterPower + limbs + limbs + Num.logarithmSpace limbs precision (2 * M + 2).size < 2 ^ w →
    let scale := (2 : ℕ) ^ precision
    let cited := max 2 (c * Cited.csGamma Kγ (3 * M)) * scale
    let den := Expander.maxPhiDenOf decK thr M
    let lo := scale / den
    let hi := (scale + (den - 1)) / den
    let recLo := scale * scale / hi
    let recHi := (scale * scale + (lo - 1)) / lo
    let logCap := (2 * M + 2) * scale
    scale * scale + (lo - 1) < 2 ^ w →
    max (max recLo recHi) cited < 2 ^ w →
    25 * (logCap + scale) < 2 ^ w →
    25 * (logCap + scale) * max recLo cited < 2 ^ w →
    25 * (logCap + scale) * max recHi cited + (scale - 1) < 2 ^ w →
    ∃ out cost ret, Runs w p ω (computeInitSparsifierFirstPathWithDegree qEntry bits load log pack exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits cDeg) st .normal out cost ∧
      (out.regs 60 : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K (1 / (den : ℝ)) M ∧
      Expander.csGammaExpPath Kγ c K (1 / (den : ℝ)) M ≤ (out.regs 61 : ℝ) / scale ∧
      out.regs 61 ≤ max (2 ^ (precision + 2 * range) + 2) ((25 * (logCap + scale) * max recHi cited + (scale - 1)) / scale) ∧
      (∀ kBound logBound logErr, coeffHi ≤ kBound * 2 ^ coeffBits →
        logHi ≤ logBound * scale → logHi - logLo ≤ logErr →
        let kErr := (coeffHi - coeffLo) * 2 ^ (precision - coeffBits)
        let exponentErr := Expander.qOf M * exponent * (kErr * logBound + kBound * logErr)
        let invBound := max (2 * den + 1) (max 2 (c * Cited.csGamma Kγ (3 * M)))
        out.regs 61 - out.regs 60 ≤
          max (2 ^ (2 * range) * exponentErr + 4)
            (25 * ((4 * 2 ^ ((2 * M + 2).size + 10)) * invBound +
              (2 * M + 3) * (invBound ^ 2 + 2)) + 2)) ∧
      out.regs 4 = scale ∧ out.regs 68 = precision ∧ out.regs 99 = ret ∧ heap ≤ ret ∧
      ret ≤ afterPower + limbs + limbs + Num.logarithmSpace limbs precision (2 * M + 2).size ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      out.regs 63 = den ∧ out.regs 58 = Spanner.capM_W cDeg (1 / (den : ℝ)) M ∧
      out.regs 56 = scale / c ∧ out.regs 57 = (scale + (c - 1)) / c ∧
      out.regs 39 = kLo ∧ out.regs 40 = kHi ∧
      out.regs 28 = logLo ∧ out.regs 29 = logHi ∧ out.regs 67 = limbs ∧
      (∀ r ∈ ([1, 18, 22, 25, 28, 29, 64, 65, 66, 67, 74, 75, 76, 89] : List ℕ),
        out.regs r = st.regs r) ∧
      cost ≤ 345 * limbs + 2 * Num.positiveExponentialCost limbs (precision + precision) range + Num.logarithmCost limbs precision (2 * M + 2).size +
        14 * (2 * M + 2).size + 35 * (Nat.log 2 (3 * M) + 1) + 65 * (Nat.log 2 (M + 2) + 1) + 120 * (Nat.log 2 (4 * M + 2) + decK * (Expander.rOf (4 * M)) ^ 2 + 4) + 822 := by
  intro kLo kHi hkl hkh exponent expLo expHi hup hwExp hfitExp range haccExp hcapExp hq hwordExp
    space afterPower hroom scale cited den lo hi recLo recHi logCap hrec hmax hml hfLo hfHi
  obtain ⟨mid, cost₁, hr₁, h63, h58, al, au, _, _, kl, ku, h53, h54, h56, h57, h39, h40, hp,
    _, hmem, hk₁, hc₁⟩ := prepareInitSparsifierLengthInputsWithDegree_runs (ω := ω) hdec hM h4 hm hcubeDec
      hcDegPos hcDegWord hcoeff hcapFit hden hround hc hcScale hcRound hcoeffBits hwidth hcoeffLo hcoeffHi hcoeffWord
  obtain ⟨out, cost₂, ret, hr₂, lb, ub, hwOut, hgap, hsOut, hpOut, hret, hbase, htop, hf, hz', hk₂, hc₂⟩ :=
    computeInitSparsifierCitedPath_runs (ω := ω) (lower := 60) (upper := 61) hbits hload hpack hlog hexp hshift hqImpl hq8 hq2
      ((hk₁ 23 (by decide)).trans hM) ((hk₁ 67 (by decide)).trans hL)
      ((hk₁ 68 (by decide)).trans hP) ((hk₁ 98 (by decide)).trans hh)
      hK htriple hcube hexpWord hw₄ h53 h54 hwide hsfit h39 h40
      ((hk₁ 28 (by decide)).trans h28) ((hk₁ 29 (by decide)).trans h29) horder hlogFit
      (h39 ▸ kl) (h40 ▸ ku) hlLo hlHi hkl hkh
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hc (h53 ▸ hp) hw hword hfit (hmem.symm ▸ hz)
      hdiv hacc hcap hprecExp hwidth hup hwExp hfitExp haccExp hcapExp hq hwordExp hroom
      (h53 ▸ al) (h54 ▸ au) hrec hmax hml hfLo hfHi
  change cost₂ ≤ 345 * limbs + 2 * Num.positiveExponentialCost limbs (precision + precision) range +
    Num.logarithmCost limbs precision (2 * M + 2).size +
    14 * (2 * M + 2).size + 35 * (Nat.log 2 (3 * M) + 1) + 65 * (Nat.log 2 (M + 2) + 1) + 764 at hc₂
  let citedFactor := max 2 (c * Cited.csGamma Kγ (3 * M))
  let invBound := max (2 * den + 1) citedFactor
  obtain ⟨hcond, hloBound, hrecBound⟩ :=
    initPathConductanceWords_bounds (scale := scale) (Expander.maxPhiDenOf_pos decK thr M) hden
  have hrecHi : max recHi cited ≤ invBound * scale :=
    max_le (hrecBound.trans (Nat.mul_le_mul_right _ (le_max_left _ _)))
      (Nat.mul_le_mul_right _ (le_max_right _ _))
  have hlow : scale ≤ invBound * lo :=
    hloBound.trans (Nat.mul_le_mul_right _ ((Nat.le_succ _).trans (le_max_left _ _)))
  have hcoeffOrder : coeffLo ≤ coeffHi := by
    have hscaleCoeff : (0 : ℝ) < ((2 ^ coeffBits : ℕ) : ℝ) := by positivity
    exact_mod_cast (div_le_div_iff_of_pos_right hscaleCoeff).mp (hcoeffLo.trans hcoeffHi)
  have hkOrder : kLo ≤ kHi := Nat.mul_le_mul_right _ hcoeffOrder
  have hscaleSplit : 2 ^ coeffBits * 2 ^ (precision - coeffBits) = scale := by
    rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel hcoeffBits]
  have hgap' (kBound logBound logErr : ℕ)
      (hk : coeffHi ≤ kBound * 2 ^ coeffBits) (hlog : logHi ≤ logBound * scale)
      (hlogErr : logHi - logLo ≤ logErr) :
      let kErr := (coeffHi - coeffLo) * 2 ^ (precision - coeffBits)
      let expErr := Expander.qOf M * exponent * (kErr * logBound + kBound * logErr)
      out.regs 61 - out.regs 60 ≤ max (2 ^ (2 * range) * expErr + 4)
        (25 * ((4 * 2 ^ ((2 * M + 2).size + 10)) * invBound +
          (2 * M + 3) * (invBound ^ 2 * 1 + 2)) + 2) := by
    let kErr := (coeffHi - coeffLo) * 2 ^ (precision - coeffBits)
    let expErr := Expander.qOf M * exponent * (kErr * logBound + kBound * logErr)
    have hku : kHi ≤ kBound * scale := by
      calc
        _ ≤ (kBound * 2 ^ coeffBits) * 2 ^ (precision - coeffBits) :=
          Nat.mul_le_mul_right _ hk
        _ = _ := by rw [Nat.mul_assoc, hscaleSplit]
    have hkErr : kHi - kLo ≤ kErr := by
      dsimp [kHi, kLo, kErr]
      rw [Nat.sub_mul]
    have he : expHi - expLo ≤ expErr * scale :=
      initSparsifierPathExponent_gap hkOrder horder hku hlog hkErr hlogErr
    exact hgap (2 * M + 3) invBound 1 expErr le_rfl hrecHi hlow hcond he
  refine ⟨out, cost₁ + cost₂ + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, cost₁, cost₂, hr₁, hr₂, rfl⟩),
    lb, ub, hwOut, ?_, hsOut, hpOut, hret, hbase, htop,
    fun a ha => (hf a ha).trans (congrFun hmem a), hz',
    (hk₂ 63 (by decide) (by decide) (by decide) (by decide)).trans h63,
    (hk₂ 58 (by decide) (by decide) (by decide) (by decide)).trans h58,
    (hk₂ 56 (by decide) (by decide) (by decide) (by decide)).trans h56,
    (hk₂ 57 (by decide) (by decide) (by decide) (by decide)).trans h57,
    (hk₂ 39 (by decide) (by decide) (by decide) (by decide)).trans h39,
    (hk₂ 40 (by decide) (by decide) (by decide) (by decide)).trans h40,
    (hk₂ 28 (by decide) (by decide) (by decide) (by decide)).trans ((hk₁ 28 (by decide)).trans h28),
    (hk₂ 29 (by decide) (by decide) (by decide) (by decide)).trans ((hk₁ 29 (by decide)).trans h29),
    (hk₂ 67 (by decide) (by decide) (by decide) (by decide)).trans ((hk₁ 67 (by decide)).trans hL),
    ?_, by omega⟩
  · intro kBound logBound logErr hk hlog herr
    simpa only [Nat.mul_one] using hgap' kBound logBound logErr hk hlog herr
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (hk₂ _ (by decide) (by decide) (by decide) (by decide)).trans (hk₁ _ (by decide))

/-- Prepare both conductance intervals and compute the input graph's
path interval, preserving the witness inputs for the second call. -/
@[expose] def computeInitSparsifierFirstPath
    (qEntry bits load log pack exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits : ℕ) : Stmt :=
  computeInitSparsifierFirstPathWithDegree qEntry bits load log pack exp shiftEntry Kγ c decK thr
    coeffLo coeffHi coeffBits 36

/-- The first call computes its path enclosure from runtime setup and
leaves the witness cap, conductance and scale ready for the second. -/
theorem computeInitSparsifierFirstPath_runs
    {w h Kγ c M precision limbs heap bits load log pack qEntry exp shiftEntry accuracy logLo logHi decK thr coeffLo coeffHi coeffBits : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {K : ℝ}
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hload : MeetsContract w p load (Num.loadSmallContract w h))
    (hpack : MeetsContract w p pack (Num.packWordContract w h))
    (hlog : MeetsContract w p log (Num.logarithmContract w h (precision - (2 * M + 2).size - 10)))
    (hexp : MeetsContract w p exp (Num.positiveExponentialContract w h accuracy))
    (hshift : MeetsContract w p shiftEntry (Num.shiftRightContract w h))
    (hqImpl : MeetsContract w p qEntry (initSparsifierPathQContract w))
    (hq8 : (Expander.PathDSProg.qRoot M + 1) ^ 8 < 2 ^ w)
    (hq2 : Expander.PathDSProg.qRoot M + 2 < 2 ^ w)
    (hM : st.regs 23 = M)
    (hL : st.regs 67 = limbs) (hP : st.regs 68 = precision) (hh : st.regs 98 = heap)
    (hK : Kγ < 2 ^ w) (htriple : 3 * M < 2 ^ w)
    (hcube : (Nat.log 2 (3 * M) + 2) ^ 4 < 2 ^ w)
    (hexpWord : Expander.PathDSProg.csGammaExp Kγ (3 * M) < 2 ^ w) (hw₄ : 4 < 2 ^ w)

    (hwide : precision + precision < w)
    (hsfit : 2 * 2 ^ (precision + precision) < Num.capacity h limbs)
    (h28 : st.regs 28 = logLo) (h29 : st.regs 29 = logHi) (horder : logLo ≤ logHi)
    (hlogFit : Expander.PathDSProg.csGammaExp Kγ (3 * M) * logHi < 2 ^ w)
    (hlLo : (logLo : ℝ) / (2 ^ precision : ℕ) ≤ Real.log 2)
    (hlHi : Real.log 2 ≤ (logHi : ℝ) / (2 ^ precision : ℕ))
    (hc : 0 < c)
    (hw : 2 * M + 2 < 2 ^ w) (hword : (2 * M + 2) * 2 ^ precision < 2 ^ w)
    (hfit : 2 * ((2 * M + 2) * 2 ^ precision) < Num.capacity h limbs)
    (hz : ZeroFrom st.mem heap) (hdiv : h ∣ precision)
    (hacc : (2 * M + 2).size + 11 ≤ precision)
    (hcap : precision + (2 * M + 2).size + 4 ≤ h * limbs)
    (hprecExp : 2 * (precision + precision) + 9 < 2 ^ w) (hwidth : precision < w)
    (hdec : 1 ≤ decK) (h4 : st.regs 4 = 2 ^ precision)
    (hm : 4 * M + 2 < 2 ^ w) (hcubeDec : (Nat.log 2 (4 * M + 2) + 2) ^ 3 < 2 ^ w)
    (hcoeff : 36 * Expander.maxPhiDenOf decK thr M < 2 ^ w)
    (hcapFit : 36 * Expander.maxPhiDenOf decK thr M * M + 1 < 2 ^ w)
    (hden : Expander.maxPhiDenOf decK thr M ≤ 2 ^ precision)
    (hround : 2 ^ precision + (Expander.maxPhiDenOf decK thr M - 1) < 2 ^ w)
    (hcScale : c ≤ 2 ^ precision) (hcRound : 2 ^ precision + (c - 1) < 2 ^ w)
    (hcoeffBits : coeffBits ≤ precision)
    (hcoeffLo : (coeffLo : ℝ) / (2 ^ coeffBits : ℕ) ≤ max K 1)
    (hcoeffHi : max K 1 ≤ (coeffHi : ℝ) / (2 ^ coeffBits : ℕ))
    (hcoeffWord : max coeffLo coeffHi * 2 ^ (precision - coeffBits) < 2 ^ w) :
    let kLo := coeffLo * 2 ^ (precision - coeffBits)
    let kHi := coeffHi * 2 ^ (precision - coeffBits)
    kLo * Expander.qOf M < 2 ^ w → kHi * Expander.qOf M < 2 ^ w →
    let exponent := Expander.PathDSProg.csGammaExp Kγ (3 * M)
    let expLo := kLo * Expander.qOf M * (exponent * logLo)
    let expHi := kHi * Expander.qOf M * (exponent * logHi)
    expHi + 1 < 2 ^ w →
    max expLo expHi < 2 ^ w →
    2 * max expLo expHi < Num.capacity h limbs →
    let range := expHi / 2 ^ (precision + precision) + 1
    accuracy + range + 10 ≤ precision + precision →
    precision + precision + 2 * range + 4 ≤ h * limbs →
    precision + 2 * range ≤ accuracy →
    2 ^ (precision + 2 * range) + 2 < 2 ^ w →
    let space := limbs + limbs + Num.positiveExponentialSpace limbs (precision + precision) range +
      (2 * limbs + 1)
    let afterPower := heap + space + space
    afterPower + limbs + limbs + Num.logarithmSpace limbs precision (2 * M + 2).size < 2 ^ w →
    let scale := (2 : ℕ) ^ precision
    let cited := max 2 (c * Cited.csGamma Kγ (3 * M)) * scale
    let den := Expander.maxPhiDenOf decK thr M
    let lo := scale / den
    let hi := (scale + (den - 1)) / den
    let recLo := scale * scale / hi
    let recHi := (scale * scale + (lo - 1)) / lo
    let logCap := (2 * M + 2) * scale
    scale * scale + (lo - 1) < 2 ^ w →
    max (max recLo recHi) cited < 2 ^ w →
    25 * (logCap + scale) < 2 ^ w →
    25 * (logCap + scale) * max recLo cited < 2 ^ w →
    25 * (logCap + scale) * max recHi cited + (scale - 1) < 2 ^ w →
    ∃ out cost ret, Runs w p ω (computeInitSparsifierFirstPath qEntry bits load log pack exp shiftEntry Kγ c decK thr coeffLo coeffHi coeffBits) st .normal out cost ∧
      (out.regs 60 : ℝ) / scale ≤ Expander.csGammaExpPath Kγ c K (1 / (den : ℝ)) M ∧
      Expander.csGammaExpPath Kγ c K (1 / (den : ℝ)) M ≤ (out.regs 61 : ℝ) / scale ∧
      out.regs 61 ≤ max (2 ^ (precision + 2 * range) + 2) ((25 * (logCap + scale) * max recHi cited + (scale - 1)) / scale) ∧
      out.regs 4 = scale ∧ out.regs 68 = precision ∧ out.regs 99 = ret ∧ heap ≤ ret ∧
      ret ≤ afterPower + limbs + limbs + Num.logarithmSpace limbs precision (2 * M + 2).size ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem ret ∧
      out.regs 58 = Spanner.capM_W 36 (1 / (den : ℝ)) M ∧
      out.regs 56 = scale / c ∧ out.regs 57 = (scale + (c - 1)) / c ∧
      out.regs 39 = kLo ∧ out.regs 40 = kHi ∧
      out.regs 28 = logLo ∧ out.regs 29 = logHi ∧ out.regs 67 = limbs ∧
      (∀ r ∈ ([1, 18, 22, 25, 28, 29, 64, 65, 66, 67, 74, 75, 76, 89] : List ℕ),
        out.regs r = st.regs r) ∧
      cost ≤ 345 * limbs + 2 * Num.positiveExponentialCost limbs (precision + precision) range + Num.logarithmCost limbs precision (2 * M + 2).size +
        14 * (2 * M + 2).size + 35 * (Nat.log 2 (3 * M) + 1) + 65 * (Nat.log 2 (M + 2) + 1) + 120 * (Nat.log 2 (4 * M + 2) + decK * (Expander.rOf (4 * M)) ^ 2 + 4) + 822 := by
  intro kLo kHi hkl hkh exponent expLo expHi hup hwExp hfitExp range haccExp hcapExp hq hwordExp
    space afterPower hroom scale cited den lo hi recLo recHi logCap hrec hmax hml hfLo hfHi
  obtain ⟨mid, cost₁, hr₁, _, h58, al, au, _, _, kl, ku, h53, h54, h56, h57, h39, h40, hp,
    _, hmem, hk₁, hc₁⟩ := prepareInitSparsifierLengthInputs_runs (ω := ω) hdec hM h4 hm hcubeDec
      hcoeff hcapFit hden hround hc hcScale hcRound hcoeffBits hwidth hcoeffLo hcoeffHi hcoeffWord
  obtain ⟨out, cost₂, ret, hr₂, lb, ub, hwOut, _, hsOut, hpOut, hret, hbase, htop, hf, hz', hk₂, hc₂⟩ :=
    computeInitSparsifierCitedPath_runs (ω := ω) (lower := 60) (upper := 61) hbits hload hpack hlog hexp hshift hqImpl hq8 hq2
      ((hk₁ 23 (by decide)).trans hM) ((hk₁ 67 (by decide)).trans hL)
      ((hk₁ 68 (by decide)).trans hP) ((hk₁ 98 (by decide)).trans hh)
      hK htriple hcube hexpWord hw₄ h53 h54 hwide hsfit h39 h40
      ((hk₁ 28 (by decide)).trans h28) ((hk₁ 29 (by decide)).trans h29) horder hlogFit
      (h39 ▸ kl) (h40 ▸ ku) hlLo hlHi hkl hkh
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hc (h53 ▸ hp) hw hword hfit (hmem.symm ▸ hz)
      hdiv hacc hcap hprecExp hwidth hup hwExp hfitExp haccExp hcapExp hq hwordExp hroom
      (h53 ▸ al) (h54 ▸ au) hrec hmax hml hfLo hfHi
  change cost₂ ≤ 345 * limbs + 2 * Num.positiveExponentialCost limbs (precision + precision) range +
    Num.logarithmCost limbs precision (2 * M + 2).size +
    14 * (2 * M + 2).size + 35 * (Nat.log 2 (3 * M) + 1) + 65 * (Nat.log 2 (M + 2) + 1) + 764 at hc₂
  refine ⟨out, cost₁ + cost₂ + 1, ret, runs_seq_iff.mpr (Or.inr ⟨mid, cost₁, cost₂, hr₁, hr₂, rfl⟩),
    lb, ub, hwOut, hsOut, hpOut, hret, hbase, htop,
    fun a ha => (hf a ha).trans (congrFun hmem a), hz',
    (hk₂ 58 (by decide) (by decide) (by decide) (by decide)).trans h58,
    (hk₂ 56 (by decide) (by decide) (by decide) (by decide)).trans h56,
    (hk₂ 57 (by decide) (by decide) (by decide) (by decide)).trans h57,
    (hk₂ 39 (by decide) (by decide) (by decide) (by decide)).trans h39,
    (hk₂ 40 (by decide) (by decide) (by decide) (by decide)).trans h40,
    (hk₂ 28 (by decide) (by decide) (by decide) (by decide)).trans ((hk₁ 28 (by decide)).trans h28),
    (hk₂ 29 (by decide) (by decide) (by decide) (by decide)).trans ((hk₁ 29 (by decide)).trans h29),
    (hk₂ 67 (by decide) (by decide) (by decide) (by decide)).trans ((hk₁ 67 (by decide)).trans hL),
    ?_, by omega⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact (hk₂ _ (by decide) (by decide) (by decide) (by decide)).trans (hk₁ _ (by decide))

end MinCostFlow.MinRatio
