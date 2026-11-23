module

public import MinCostFlow.IPM.Machine.PrecisionCoefficient
public import MinCostFlow.IPM.Machine.MinRatioContract

/-!
# Concrete fixed-point format parameters

Four-bit limbs suffice for all arithmetic modules when the machine word
has at least fourteen bits. The precision below covers the power and
gradient error budgets, the data structure's precision margin, and exact
storage of the dyadic barrier exponent. These are static format choices.
The bounds on values during a run are proved separately.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine

/-- A common range margin beyond the slack and integer-coefficient ranges. -/
def ipmRangeExponent (m U : ℕ) : ℕ :=
  4*slackRangeExponent m U+2*gradientCoefficientExponent m U+100

/-- Relative-error bits for the length and gradient modules. -/
def ipmErrorBits (m U : ℕ) : ℕ := ipmRangeExponent m U+10

/-- Four-bit-aligned precision covers both numerical and DS interfaces. -/
def ipmPrecision (m U : ℕ) : ℕ :=
  4*(ipmErrorBits m U+5*ipmRangeExponent m U+m.size+Num.IPM.alphaScale m U+100)

/-- Signed blocks include all the gradient's intermediate guard bits. -/
def ipmLimbs (m U : ℕ) : ℕ :=
  ipmPrecision m U+gradientCoefficientExponent m U+5*ipmRangeExponent m U+40

/-- The format parameters and small integer intermediates fit below this
single bound. Heap addresses require their own allocation bound. -/
def ipmParameterBound (m U : ℕ) : ℕ :=
  2*ipmPrecision m U+20*m+Num.IPM.alphaScale m U+U+ipmLimbs m U+
    ipmRangeExponent m U+100

/-- A sufficient local word width for these parameter computations.
The final solver's `wordSize c` must also cover its total workspace. -/
def ipmParameterWordBits (m U : ℕ) : ℕ := 14+(ipmParameterBound m U).size

/-- Each of the static numerical margins follows from the chosen precision. -/
theorem ipm_precision_margins (m U : ℕ) :
    4 ∣ ipmPrecision m U ∧
    ipmErrorBits m U+4*ipmRangeExponent m U+42 ≤ ipmPrecision m U ∧
    5*ipmRangeExponent m U+m.size+30 ≤ ipmPrecision m U ∧
    ipmPrecision m U+gradientCoefficientExponent m U+4*ipmRangeExponent m U+30 ≤
      4*ipmLimbs m U ∧
    ipmPrecision m U+5*ipmRangeExponent m U+30 ≤ 4*ipmLimbs m U ∧
    Num.IPM.alphaExponent m U ≤ ipmPrecision m U := by
  have ha : Num.IPM.alphaExponent m U ≤ Num.IPM.alphaScale m U :=
    (Num.IPM.alphaExponent_le_iff m U _).mpr (Nat.lt_two_pow_self.le)
  simp only [ipmPrecision,ipmLimbs]
  exact ⟨dvd_mul_right 4 _,by omega,by omega,by omega,by omega,by omega⟩

/-- One parameter bound supplies every scalar word-fit premise, including
`2P+9` for division and `20m` for the gradient. -/
theorem ipm_parameter_words_fit (m U : ℕ) {w : ℕ}
    (hw : ipmParameterWordBits m U ≤ w) :
    14 ≤ w ∧ ipmLimbs m U < 2^w ∧ ipmPrecision m U < 2^w ∧
    ipmRangeExponent m U < 2^w ∧ 2*ipmPrecision m U+9 < 2^w ∧
    20*m < 2^w ∧ Num.IPM.alphaScale m U+1 < 2^w ∧ U < 2^w := by
  have hsize : (ipmParameterBound m U).size ≤ w := by
    unfold ipmParameterWordBits at hw
    omega
  have hb : ipmParameterBound m U < 2^w := (Nat.size_le).mp hsize
  unfold ipmParameterBound at hb
  unfold ipmParameterWordBits at hw
  omega

/-- A concrete format meeting the data structure's signed-width and
arithmetic margins. This does not assert a numerical range for a run. -/
def ipmMinRatioFormat (m U : ℕ) {w : ℕ}
    (hw : ipmParameterWordBits m U ≤ w) : MinRatioFormat w where
  fmt := {
    limbBits := 4
    precision := ipmPrecision m U
    limbBits_pos := by decide
    product_fits := by have hh := (ipm_parameter_words_fit m U hw).1; omega
    precision_aligned := (ipm_precision_margins m U).1 }
  limbs := ipmLimbs m U
  rangeExponent := ipmRangeExponent m U
  divide_fits := by have hh := (ipm_parameter_words_fit m U hw).1; omega
  width := (ipm_precision_margins m U).2.2.2.2.1
  parameters_fit := by
    have hh := ipm_parameter_words_fit m U hw
    exact ⟨hh.2.1,hh.2.2.1,hh.2.2.2.1⟩


/-- Effective slack exponent for the fixed-point arithmetic of page 7.
The potential bound supplies the base range and the runtime quality
exponent can increase it. -/
def qualitySlackExponent (m U k : ℕ) : ℕ := max (slackRangeExponent m U) k

theorem slackRangeExponent_le_qualitySlackExponent (m U k : ℕ) :
    slackRangeExponent m U ≤ qualitySlackExponent m U k := le_max_left _ _

theorem qualityExponent_le_qualitySlackExponent (m U k : ℕ) :
    k ≤ qualitySlackExponent m U k := le_max_right _ _

theorem qualitySlackExponent_eq {m U k : ℕ} (hk : k ≤ slackRangeExponent m U) :
    qualitySlackExponent m U k = slackRangeExponent m U := max_eq_left hk

/-- The numerical range after accounting for the runtime quality. -/
def ipmQualityRangeExponent (m U k : ℕ) : ℕ :=
  4*qualitySlackExponent m U k+2*gradientCoefficientExponent m U+100

/-- The error budget and fixed-point precision for the enlarged range. -/
def ipmQualityErrorBits (m U k : ℕ) : ℕ := ipmQualityRangeExponent m U k+10

def ipmQualityPrecision (m U k : ℕ) : ℕ :=
  4*(ipmQualityErrorBits m U k+5*ipmQualityRangeExponent m U k+
    m.size+Num.IPM.alphaScale m U+100)

def ipmQualityLimbs (m U k : ℕ) : ℕ :=
  ipmQualityPrecision m U k+gradientCoefficientExponent m U+5*ipmQualityRangeExponent m U k+40

def ipmQualityParameterBound (m U k : ℕ) : ℕ :=
  2*ipmQualityPrecision m U k+20*m+Num.IPM.alphaScale m U+U+ipmQualityLimbs m U k+
    ipmQualityRangeExponent m U k+100

def ipmQualityParameterWordBits (m U k : ℕ) : ℕ := 14+(ipmQualityParameterBound m U k).size

/-- The base precision, range and word-size formulas are recovered when
the potential-derived slack range already covers the quality. -/
theorem ipmQualityParameters_eq {m U k : ℕ} (hk : k ≤ slackRangeExponent m U) :
    ipmQualityRangeExponent m U k = ipmRangeExponent m U ∧
    ipmQualityErrorBits m U k = ipmErrorBits m U ∧
    ipmQualityPrecision m U k = ipmPrecision m U ∧
    ipmQualityLimbs m U k = ipmLimbs m U ∧
    ipmQualityParameterWordBits m U k = ipmParameterWordBits m U := by
  simp only [ipmQualityRangeExponent, ipmQualityErrorBits, ipmQualityPrecision, ipmQualityLimbs,
    ipmQualityParameterWordBits, ipmQualityParameterBound, qualitySlackExponent_eq hk,
    ipmRangeExponent, ipmErrorBits, ipmPrecision, ipmLimbs, ipmParameterWordBits, ipmParameterBound,
    and_self]

/-- Increasing quality-dependent precision adds at most a linear term
in the quality exponent to the number of limbs. -/
theorem ipmQualityLimbs_le (m U k : ℕ) :
    ipmQualityLimbs m U k ≤ ipmLimbs m U+116*k := by
  have h := max_le (Nat.le_add_right (slackRangeExponent m U) k)
    (Nat.le_add_left k (slackRangeExponent m U))
  simp only [ipmQualityLimbs, ipmQualityPrecision, ipmQualityErrorBits, ipmQualityRangeExponent,
    qualitySlackExponent, ipmLimbs, ipmPrecision, ipmErrorBits, ipmRangeExponent]
  omega
/-- Each of the static numerical margins follows from the chosen precision. -/
theorem ipm_quality_precision_margins (m U k : ℕ) :
    4 ∣ ipmQualityPrecision m U k ∧
    ipmQualityErrorBits m U k+4*ipmQualityRangeExponent m U k+42 ≤ ipmQualityPrecision m U k ∧
    5*ipmQualityRangeExponent m U k+m.size+30 ≤ ipmQualityPrecision m U k ∧
    ipmQualityPrecision m U k+gradientCoefficientExponent m U+4*ipmQualityRangeExponent m U k+30 ≤
      4*ipmQualityLimbs m U k ∧
    ipmQualityPrecision m U k+5*ipmQualityRangeExponent m U k+30 ≤ 4*ipmQualityLimbs m U k ∧
    Num.IPM.alphaExponent m U ≤ ipmQualityPrecision m U k := by
  have ha : Num.IPM.alphaExponent m U ≤ Num.IPM.alphaScale m U :=
    (Num.IPM.alphaExponent_le_iff m U _).mpr (Nat.lt_two_pow_self.le)
  simp only [ipmQualityPrecision,ipmQualityLimbs]
  exact ⟨dvd_mul_right 4 _,by omega,by omega,by omega,by omega,by omega⟩

/-- One parameter bound supplies every scalar word-fit premise, including
`2P+9` for division and `20m` for the gradient. -/
theorem ipm_quality_parameter_words_fit (m U k : ℕ) {w : ℕ}
    (hw : ipmQualityParameterWordBits m U k ≤ w) :
    14 ≤ w ∧ ipmQualityLimbs m U k < 2^w ∧ ipmQualityPrecision m U k < 2^w ∧
    ipmQualityRangeExponent m U k < 2^w ∧ 2*ipmQualityPrecision m U k+9 < 2^w ∧
    20*m < 2^w ∧ Num.IPM.alphaScale m U+1 < 2^w ∧ U < 2^w := by
  have hsize : (ipmQualityParameterBound m U k).size ≤ w := by
    unfold ipmQualityParameterWordBits at hw
    omega
  have hb : ipmQualityParameterBound m U k < 2^w := (Nat.size_le).mp hsize
  unfold ipmQualityParameterBound at hb
  unfold ipmQualityParameterWordBits at hw
  omega

/-- A concrete format meeting the data structure's signed-width and
arithmetic margins. This does not assert a numerical range for a run. -/
def ipmQualityMinRatioFormat (m U k : ℕ) {w : ℕ}
    (hw : ipmQualityParameterWordBits m U k ≤ w) : MinRatioFormat w where
  fmt := {
    limbBits := 4
    precision := ipmQualityPrecision m U k
    limbBits_pos := by decide
    product_fits := by have hh := (ipm_quality_parameter_words_fit m U k hw).1; omega
    precision_aligned := (ipm_quality_precision_margins m U k).1 }
  limbs := ipmQualityLimbs m U k
  rangeExponent := ipmQualityRangeExponent m U k
  divide_fits := by have hh := (ipm_quality_parameter_words_fit m U k hw).1; omega
  width := (ipm_quality_precision_margins m U k).2.2.2.2.1
  parameters_fit := by
    have hh := ipm_quality_parameter_words_fit m U k hw
    exact ⟨hh.2.1,hh.2.2.1,hh.2.2.2.1⟩



/-- Increasing the slack exponent only increases the required word width. -/
theorem ipmParameterWordBits_le_quality (m U k : ℕ) :
    ipmParameterWordBits m U ≤ ipmQualityParameterWordBits m U k := by
  have hs := slackRangeExponent_le_qualitySlackExponent m U k
  apply Nat.add_le_add_left
  apply Nat.size_le_size
  simp only [ipmParameterBound, ipmQualityParameterBound, ipmPrecision, ipmQualityPrecision,
    ipmErrorBits, ipmQualityErrorBits, ipmRangeExponent, ipmQualityRangeExponent,
    ipmLimbs, ipmQualityLimbs]
  omega

/-- Multiplying the old parameter bound by the reciprocal dyadic quality
and a constant covers the enlarged record. -/
theorem ipmQualityParameterWordBits_le (m U k : ℕ) :
    ipmQualityParameterWordBits m U k ≤ ipmParameterWordBits m U + k + 9 := by
  have hs : qualitySlackExponent m U k ≤ slackRangeExponent m U + k := by
    unfold qualitySlackExponent
    omega
  have hb : 1 ≤ ipmParameterBound m U := by unfold ipmParameterBound; omega
  have hlinear : ipmQualityParameterBound m U k ≤ ipmParameterBound m U + 312*k := by
    simp only [ipmParameterBound, ipmQualityParameterBound, ipmPrecision, ipmQualityPrecision,
      ipmErrorBits, ipmQualityErrorBits, ipmRangeExponent, ipmQualityRangeExponent,
      ipmLimbs, ipmQualityLimbs]
    omega
  have hsmall := Nat.lt_two_pow_self (n := k)
  have hbase := (Nat.size_le).mp (le_refl (ipmParameterBound m U).size)
  have hmul : ipmParameterBound m U + 312*k ≤ 313*(ipmParameterBound m U*2^k) := by
    have h₁ := Nat.le_mul_of_pos_right (ipmParameterBound m U) (Nat.two_pow_pos k)
    have h₂ := Nat.mul_le_mul_right (2^k) hb
    simp only [one_mul] at h₂
    omega
  have hfit : ipmQualityParameterBound m U k < 2^((ipmParameterBound m U).size+k+9) := by
    refine lt_of_le_of_lt (hlinear.trans hmul) ?_
    rw [pow_add, pow_add]
    calc
      313*(ipmParameterBound m U*2^k) < 313*(2^(ipmParameterBound m U).size*2^k) :=
        Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_right hbase (Nat.two_pow_pos k)) (by decide)
      _ ≤ _ := by
        rw [Nat.mul_comm 313]
        exact Nat.mul_le_mul_left _ (by decide)
  have hw := (Nat.size_le).mpr hfit
  unfold ipmParameterWordBits ipmQualityParameterWordBits
  omega

/-- A polynomial reciprocal-quality bound gives a logarithmic additive
width bound in the bit length of the base. -/
theorem ipmQualityParameterWordBits_le_of_pow {m U k B d : ℕ}
    (hquality : 2^k ≤ B^d) :
    ipmQualityParameterWordBits m U k ≤ ipmParameterWordBits m U + d*B.size + 9 := by
  have hb := (Nat.size_le).mp (le_refl B.size)
  have hp : B^d ≤ (2^B.size)^d := Nat.pow_le_pow_left hb.le d
  rw [← pow_mul, Nat.mul_comm B.size d] at hp
  have hk : k ≤ d*B.size := by
    by_contra hn
    exact (not_lt_of_ge (hquality.trans hp)) (Nat.pow_lt_pow_right (by decide) (Nat.lt_of_not_ge hn))
  exact (ipmQualityParameterWordBits_le m U k).trans (by omega)

end MinCostFlow.IPM.Machine
