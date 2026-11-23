module

public import MinCostFlow.IPM.Machine.MinRatioUnreportedMovement
public import MinCostFlow.IPM.Machine.PrecisionParameters
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# A bounded implicit coordinate from Detect and the stored cache

The cached coordinate and base flow each lie in the capacity range.
For an unreported edge, Detect bounds its displacement from that cache.
A capacity-based lower length bound and threshold at most one put its
implicit Query value inside the selected machine range. This reasoning
uses no hidden witness and therefore also applies to lower guesses.
-/

public section
namespace MinCostFlow.IPM.Machine

private theorem query_bound_of_displacement {current previous base capacity ell eps : ℝ}
    (B R : ℕ) (hmove : ell*|current-previous|<eps)
    (hell : 1/(2:ℝ)^B≤ell) (heps : eps≤1)
    (hcache : |base+previous|≤capacity) (hbase : |base|≤capacity)
    (hmargin : 2*capacity+(2:ℝ)^B≤(2:ℝ)^R) : |current|<(2:ℝ)^R := by
  have hdisp : |current-previous|<(2:ℝ)^B := by
    have hh := (mul_le_mul_of_nonneg_right hell (abs_nonneg (current-previous))).trans_lt
      (hmove.trans_le heps)
    rw [one_div,mul_comm,← div_eq_mul_inv] at hh
    exact (div_lt_one (by positivity : (0:ℝ)<2^B)).mp hh
  have hlast : |previous|≤2*capacity := by
    calc
      |previous|=|(base+previous)-base| := by congr 1; ring
      _≤|base+previous|+|base| := by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (base+previous) (-base)
      _≤capacity+capacity := add_le_add hcache hbase
      _=2*capacity := by ring
  have htriangle : |current|≤|current-previous|+|previous| := by
    simpa only [sub_add_cancel] using abs_add_le (current-previous) previous
  exact htriangle.trans_lt ((add_lt_add_of_lt_of_le hdisp hlast).trans_le
    (by simpa only [add_comm] using hmargin))

/-- The chosen range has room for two capacity bounds and the Detect
error allowed by the capacity-based cached-length lower bound. -/
theorem ipm_query_range_margin (m U : ℕ) {capacity : ℝ}
    (hcapacity : capacity≤(2:ℝ)^(slackRangeExponent m U)) :
    2*capacity+(2:ℝ)^(2*slackRangeExponent m U+1)≤(2:ℝ)^(ipmRangeExponent m U) := by
  have hp : (2:ℝ)^(slackRangeExponent m U)≤(2:ℝ)^(2*slackRangeExponent m U) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have htwice : 2*capacity≤(2:ℝ)^(2*slackRangeExponent m U+1) := by
    have hh := mul_le_mul_of_nonneg_left (hcapacity.trans hp) (by norm_num : (0:ℝ)≤2)
    simpa only [pow_succ,mul_comm] using hh
  have hexp : 2*slackRangeExponent m U+2≤ ipmRangeExponent m U := by
    unfold ipmRangeExponent
    omega
  calc
    _≤(2:ℝ)^(2*slackRangeExponent m U+1)+(2:ℝ)^(2*slackRangeExponent m U+1) :=
      add_le_add htwice (le_refl _)
    _=(2:ℝ)^(2*slackRangeExponent m U+2) := by rw [show 2*slackRangeExponent m U+2=(2*slackRangeExponent m U+1)+1 by omega,pow_succ]; ring
    _≤_ := pow_le_pow_right₀ (by norm_num) hexp

/-- On every valid fixed-graph history, the last cached coordinate and
Detect's unconditional answer bound an unreported Query within the
machine range. All hypotheses concern stored inputs or the original
specification, with no progress or hidden-stability condition. -/
theorem minRatio_unreported_query_range_on (A : MinRatioDataStructure) (κ α Ψ eps : ℝ)
    (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T t e : ℕ) (G : MGraph) (m U : ℕ)
    (base capacity : ℝ)
    (hvalid : MinRatioHistoryValid D op T) (hA : MinRatioSpecOn A κ α Ψ eps D eta op T) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=G) (he : e∈G.E)
    (hne : e∉(A.detect (minRatioState A D eta op t)).1)
    (hell : 1/(2:ℝ)^(2*slackRangeExponent m U+1)≤D.ℓ (t+1) e)
    (heps : eps≤1) (hbase : |base|≤capacity)
    (hcache : |base+A.query (minRatioState A D eta op (minRatioLast A D eta op t e)) e|≤capacity)
    (hcapacity : capacity≤(2:ℝ)^(slackRangeExponent m U)) :
    |A.query (minRatioState A D eta op (t+1)) e|<(2:ℝ)^(ipmRangeExponent m U) :=
  query_bound_of_displacement _ _
    (minRatio_unreported_query_displacement_on A κ α Ψ eps D eta op T t e G hvalid hA ht hop hG he hne)
    hell heps hcache hbase (ipm_query_range_margin m U hcapacity)

/-- On every valid fixed-graph history, the last cached coordinate and
Detect's unconditional answer bound an unreported Query within the
machine range. All hypotheses concern stored inputs or the original
specification, with no progress or hidden-stability condition. -/
theorem minRatio_unreported_query_range (A : MinRatioDataStructure) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpec A κ α Ψ eps) (D : DynamicInstance)
    (eta : ℕ → ℝ) (op : ℕ → Bool) (T t e : ℕ) (G : MGraph) (m U : ℕ)
    (base capacity : ℝ)
    (hvalid : MinRatioHistoryValid D op T) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=G) (he : e∈G.E)
    (hne : e∉(A.detect (minRatioState A D eta op t)).1)
    (hell : 1/(2:ℝ)^(2*slackRangeExponent m U+1)≤D.ℓ (t+1) e)
    (heps : eps≤1) (hbase : |base|≤capacity)
    (hcache : |base+A.query (minRatioState A D eta op (minRatioLast A D eta op t e)) e|≤capacity)
    (hcapacity : capacity≤(2:ℝ)^(slackRangeExponent m U)) :
    |A.query (minRatioState A D eta op (t+1)) e|<(2:ℝ)^(ipmRangeExponent m U) :=
  minRatio_unreported_query_range_on A κ α Ψ eps D eta op T t e G m U base capacity
    hvalid (hA D eta op T hvalid) ht hop hG he hne hell heps hbase hcache hcapacity

end MinCostFlow.IPM.Machine
