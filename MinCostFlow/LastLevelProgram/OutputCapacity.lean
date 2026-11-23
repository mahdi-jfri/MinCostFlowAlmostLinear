module

public import MinCostFlow.MinRatio.LastLevelContract
public import MinCostFlow.LastLevelProgram.FixedPoint
public import MinCostFlow.IPM.Machine.PrecisionParameters
import MinCostFlow.Num.WordBounds
import MinCostFlow.LSF.Congestion
import Mathlib.Tactic

/-!
# Capacity of the last-level stretch output

The path length is bounded by the sum of live lengths. Bounding each
length from above and below gives a sufficient width for the rounded
stretch of Definition 5.8 (pages 19–20).
-/

public section

namespace MinCostFlow.LastLevelProgram

open MinRatio

/-- For the solver's four-bit limbs, the range bound leaves room for an
internal stretch grid of at most `P + 2*R + 26` fractional bits. -/
theorem stretchCapacity_of_solverRange (G : MGraph) (length : ℕ → ℝ)
    (R P Q L : ℕ) (hm : (G.m : ℝ) ≤ (2 : ℝ)^R)
    (hlen : ∀ e ∈ G.E, 1 / (2 : ℝ)^R ≤ length e ∧ length e ≤ (2 : ℝ)^R)
    (hq : Q ≤ P + 2*R + 26) (hL : P + 5*R + 30 ≤ 4*L)
    {e : ℕ} (he : e ∈ G.E) :
    2 * (2 : ℝ)^Q * lastLevelStretchBound G length e < Num.capacity 4 L := by
  let x := (2 : ℝ)^R
  have hx : 1 ≤ x := one_le_pow₀ (by norm_num)
  have hxp : 0 < x := by positivity
  have hsum : (∑ f ∈ G.E, length f) ≤ x*x := by
    calc
      (∑ f ∈ G.E, length f) ≤ ∑ _f ∈ G.E, x :=
        Finset.sum_le_sum (fun f hf => (hlen f hf).2)
      _ = (G.m : ℝ)*x := by simp [MGraph.m]
      _ ≤ x*x := mul_le_mul_of_nonneg_right hm hxp.le
  have hepos : 0 < length e := (one_div_pos.mpr hxp).trans_le (hlen e he).1
  have hratio : (∑ f ∈ G.E, length f) / length e ≤ x^3 := by
    apply (div_le_iff₀ hepos).2
    refine hsum.trans ?_
    calc
      x*x = x^3 * (1/x) := by field_simp
      _ ≤ x^3 * length e := mul_le_mul_of_nonneg_left (hlen e he).1 (by positivity)
  have hB : lastLevelStretchBound G length e ≤ 4 * x^3 := by
    unfold lastLevelStretchBound
    have hx3 : 1 ≤ x^3 := one_le_pow₀ hx
    linarith
  have hpow : (2 : ℝ)^Q * (8 * x^3) = (2 : ℝ)^(Q + 3*R + 3) := by
    rw [pow_add,pow_add,pow_mul]
    rw [show x^3 = ((2 : ℝ)^3)^R by dsimp [x]; rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
    norm_num
    ring
  calc
    _ ≤ (2 : ℝ)^Q * (8*x^3) := by
      nlinarith [mul_le_mul_of_nonneg_left hB (show 0 ≤ (2 : ℝ)^Q by positivity)]
    _ = (2 : ℝ)^(Q + 3*R + 3) := hpow
    _ < Num.capacity 4 L := by
      rw [Num.capacity_eq_two_pow, Nat.cast_pow, Nat.cast_ofNat]
      exact pow_lt_pow_right₀ (by norm_num) (by omega)

/-- The graph-derived grid fits the solver's numerical slack once the
fixed tree-guarantee constant fits its stated bit budget. -/
theorem weightPrecision_le_solverGrid (C : ℝ) (G : MGraph) (R P : ℕ)
    (hm : G.m ≤ 2^R) (hn : G.n ≤ G.m+1)
    (hD : (⌈max 1 C⌉₊ : ℕ).size + R ≤ P) :
    weightPrecision C G ≤ P+2*R+26 := by
  let D := (⌈max 1 C⌉₊ : ℕ)
  have hm' : G.m < 2^(R+1) := by
    rw [pow_succ]
    have hp := Nat.two_pow_pos R
    omega
  have hn' : G.n+2 < 2^(R+3) := by
    rw [show R+3 = R+1+1+1 by omega, pow_succ,pow_succ,pow_succ]
    have hp := Nat.two_pow_pos R
    omega
  have hlog : Nat.log 2 (G.n+2) < R+3 :=
    (Nat.log_lt_iff_lt_pow (by decide) (by omega)).2 hn'
  have hbits : Nat.log 2 (G.n+2)+1 < 2^(R+3) := by
    have hp := (Nat.lt_two_pow_self : R+3 < 2^(R+3))
    omega
  have hdp : D < 2^D.size := Nat.lt_size_self _
  have hp : (2 : ℕ)^(D.size+3*R+11) ≤ 2^(P+2*R+26) :=
    Nat.pow_le_pow_right (by decide) (by change D.size+R ≤ P at hD; omega)
  apply Nat.size_le.mpr
  refine lt_of_lt_of_le ?_ hp
  change 2 * integerScale D G < _
  unfold integerScale
  calc
    _ = 8 * D * G.m * (Nat.log 2 (G.n+2)+1)^2 := by ring
    _ ≤ 8 * 2^D.size * 2^(R+1) * (2^(R+3))^2 :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 8 hdp.le) hm'.le)
        (Nat.pow_le_pow_left hbits.le 2)
    _ = 2^(D.size+3*R+10) := by
      rw [← pow_mul, show (8 : ℕ) = 2^3 by decide, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega
    _ < 2^(D.size+3*R+11) :=
      Nat.pow_lt_pow_right (by decide) (by omega)

open IPM.Machine in
/-- The actual IPM format meets the stretch capacity check for a
connected-size graph whose lengths obey the solver's range. The fixed
tree-guarantee constant uses at most the unused precision budget. -/
theorem stretchCapacity_ipmQualityFormat {w m U k : ℕ}
    (hw : ipmQualityParameterWordBits m U k ≤ w) (C : ℝ)
    (G : MGraph) (length : ℕ → ℝ)
    (hm : G.m ≤ 2^(ipmQualityRangeExponent m U k))
    (hn : G.n ≤ G.m+1)
    (hlen : ∀ e ∈ G.E, 1 / (2 : ℝ)^(ipmQualityRangeExponent m U k) ≤ length e ∧
      length e ≤ (2 : ℝ)^(ipmQualityRangeExponent m U k))
    (hD : (⌈max 1 C⌉₊ : ℕ).size ≤ 4*ipmQualityRangeExponent m U k+30)
    {e : ℕ} (he : e ∈ G.E) :
    let F := ipmQualityMinRatioFormat m U k hw
    2 * (2 : ℝ)^weightPrecision C G * lastLevelStretchBound G length e <
      Num.capacity F.fmt.limbBits F.limbs := by
  have hP := (ipm_quality_precision_margins m U k).2.2.1
  have hL := (ipm_quality_precision_margins m U k).2.2.2.2.1
  exact stretchCapacity_of_solverRange G length _ _ _ _
    (by exact_mod_cast hm) hlen
    (weightPrecision_le_solverGrid C G _ _ hm hn (by omega)) hL he

open IPM.Machine in
/-- The graph-only stretch grid used by the runtime implementation fits
the solver's four-bit format under the same scale and length bounds. -/
theorem runtimeStretchCapacity_ipmQualityFormat {w m U k d : ℕ}
    (hw : ipmQualityParameterWordBits m U k ≤ w)
    (G : MGraph) (length : ℕ → ℝ)
    (hm : G.m ≤ 2^(ipmQualityRangeExponent m U k))
    (hlen : ∀ e ∈ G.E, 1 / (2 : ℝ)^ipmQualityRangeExponent m U k ≤ length e ∧
      length e ≤ (2 : ℝ)^ipmQualityRangeExponent m U k)
    (hd : d.size ≤ 4*ipmQualityRangeExponent m U k+30) {e : ℕ} (he : e ∈ G.E) :
    let F := ipmQualityMinRatioFormat m U k hw
    2*(2 : ℝ)^((1024*d).size+3*(G.m+1).size)*lastLevelStretchBound G length e <
      Num.capacity F.fmt.limbBits F.limbs := by
  let R := ipmQualityRangeExponent m U k
  let P := ipmQualityPrecision m U k
  have hsize : (G.m+1).size ≤ R+2 := Nat.size_le.mpr (by
    rw [show R+2 = R+1+1 by omega, pow_succ, pow_succ]
    have hpos := Nat.two_pow_pos R
    change G.m ≤ 2^R at hm
    omega)
  have hdSize : (1024*d).size ≤ d.size+10 := Nat.size_le.mpr (by
    rw [Nat.pow_add, Nat.mul_comm]
    exact Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self d) (by decide))
  have hP : 5*R+m.size+30 ≤ P := (ipm_quality_precision_margins m U k).2.2.1
  have hgrid : (1024*d).size+3*(G.m+1).size ≤ P+2*R+26 := by
    change d.size ≤ 4*R+30 at hd
    omega
  exact stretchCapacity_of_solverRange G length R P _ _ (by exact_mod_cast hm)
    hlen hgrid (ipm_quality_precision_margins m U k).2.2.2.2.1 he

/-- The numeric pass needs room for root distances before dividing by an
edge length. This condition counts the bits of the integer length numerator. -/
theorem numericTreeCapacity_of_bits {h L P n B r b : ℕ}
    (hn : n ≤ 2^r) (hB : B ≤ 2^b) (hbits : P+b+r+3 < h*L) :
    2*((2*(n : ℤ)*B+B)*(2 : ℤ)^P) < (Num.capacity h L : ℤ) := by
  have hn' : (n : ℤ) ≤ (2 : ℤ)^r := by exact_mod_cast hn
  have hb' : (B : ℤ) ≤ (2 : ℤ)^b := by exact_mod_cast hB
  have hr : (1 : ℤ) ≤ 2^r := one_le_pow₀ (by decide)
  have hmul : (n : ℤ)*B ≤ (2 : ℤ)^r*2^b :=
    mul_le_mul hn' hb' (by positivity) (by positivity)
  have hbnd : (2 : ℤ)^b ≤ (2 : ℤ)^r*2^b :=
    le_mul_of_one_le_left (by positivity) hr
  have hpoly : 2*(2*(n : ℤ)*B+B) ≤ 8*((2 : ℤ)^r*2^b) := by
    nlinarith only [hmul,hb',hbnd,show 0 ≤ (2 : ℤ)^r*2^b by positivity]
  calc
    _ ≤ (8*((2 : ℤ)^r*2^b))*2^P := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = (2 : ℤ)^(P+b+r+3) := by
      simp only [pow_add]
      ring
    _ < _ := by
      rw [Num.capacity_eq_two_pow, Nat.cast_pow, Nat.cast_ofNat]
      exact pow_lt_pow_right₀ (by decide) hbits

/-- Widening the scratch by enough limbs for the model precision and
vertex count covers the distance calculation for every caller numerator. -/
theorem numericTreeCapacity_widen {L P n B r : ℕ}
    (hn : n ≤ 2^r) (hB : B ≤ Num.capacity 4 L) :
    let scratch := L+(P+r+7)/4
    2*((2*(n : ℤ)*B+B)*(2 : ℤ)^P) < (Num.capacity 4 scratch : ℤ) := by
  intro scratch
  have hb : B ≤ 2^(4*L) := Num.capacity_eq_two_pow 4 L ▸ hB
  apply numericTreeCapacity_of_bits hn hb
  dsimp only [scratch]
  omega

/-- A stretch ratio bound is invariant under common rescaling, while
the distance numerator bound grows with the input length numerators.
These four-bit blocks fit the ratio check for a one-edge graph with
stretch bound three, but fail the distance check with two vertices. -/
theorem numericTreeCapacity_ratio_gap :
    (6 : ℝ) * 2^8 < Num.capacity 4 3 ∧
    Num.Fits 4 3 (1024 : ℤ) ∧
    ¬ 2*((2*(2 : ℤ)*1024+1024)*(2 : ℤ)^8) < (Num.capacity 4 3 : ℤ) := by
  have hc : Num.capacity 4 3 = 4096 := by decide
  rw [hc]
  refine ⟨by norm_num,?_,by norm_num⟩
  norm_num [Num.Fits,hc]

open IPM.Machine in
/-- The solver format supplies the runtime initializer's limb and precision bounds. -/
theorem runtimeCallerFormat_ipmQuality {w m U k : ℕ}
    (hw : ipmQualityParameterWordBits m U k ≤ w) :
    let F := ipmQualityMinRatioFormat m U k hw
    F.fmt.limbBits = 4 ∧ F.fmt.precision ≤ 4*F.limbs := by
  intro F
  refine ⟨rfl,?_⟩
  have h := (ipm_quality_precision_margins m U k).2.2.2.2.1
  change ipmQualityPrecision m U k ≤ 4*ipmQualityLimbs m U k
  omega

/-- The stretch bound at a shortest original edge covers both packed
tables. The other weights each contribute at least one to the sum. -/
theorem packedCapacity_of_stretchCapacity (G H : MGraph) (length weight : ℕ → ℝ)
    (h P L : ℕ) (hm : H.m ≤ G.m) (hne : G.E.Nonempty)
    (hlen : ∀ e ∈ G.E, 0 < length e)
    (hwidth : ∀ e ∈ G.E, 2*(2 : ℝ)^P*lastLevelStretchBound G length e < Num.capacity h L)
    (hw : ∀ e ∈ H.E, 1 ≤ weight e) (hsum : ∑ e ∈ H.E, weight e ≤ 2*H.m) :
    ∃ B : ℝ, 2*(2 : ℝ)^P*B < Num.capacity h L ∧
      (∀ e ∈ G.E, lastLevelStretchBound G length e ≤ B) ∧
      ∀ e ∈ H.E, 0 ≤ weight e ∧ weight e ≤ B := by
  classical
  obtain ⟨f,hf,hmin⟩ := Finset.exists_min_image G.E length hne
  have htotal : (G.m : ℝ)*length f ≤ ∑ x ∈ G.E, length x := by
    simpa [MGraph.m] using (Finset.sum_le_sum fun x hx => hmin x hx :
      (∑ _x ∈ G.E, length f) ≤ ∑ x ∈ G.E, length x)
  have hratio : (G.m : ℝ) ≤ (∑ x ∈ G.E, length x)/length f :=
    (le_div_iff₀ (hlen f hf)).2 htotal
  refine ⟨lastLevelStretchBound G length f,hwidth f hf,?_,?_⟩
  · intro e he
    have hsumNonneg : 0 ≤ ∑ x ∈ G.E, length x :=
      Finset.sum_nonneg (fun x hx => (hlen x hx).le)
    unfold lastLevelStretchBound
    exact add_le_add (le_refl _) (div_le_div_of_nonneg_left hsumNonneg (hlen f hf) (hmin e he))
  intro e he
  have herase : ((H.E.erase e).card : ℝ) ≤ ∑ x ∈ H.E.erase e, weight x := by
    simpa using (Finset.sum_le_sum fun x hx => hw x (Finset.mem_of_mem_erase hx) :
      (∑ _x ∈ H.E.erase e, (1 : ℝ)) ≤ ∑ x ∈ H.E.erase e, weight x)
  have hcard : ((H.E.erase e).card : ℝ)+1 = H.m := by
    exact_mod_cast Finset.card_erase_add_one he
  rw [← Finset.sum_erase_add H.E weight he] at hsum
  have hm' : (H.m : ℝ) ≤ G.m := by exact_mod_cast hm
  have hweight : weight e ≤ lastLevelStretchBound G length f := by
    unfold lastLevelStretchBound
    linarith only [herase,hcard,hsum,hm',hratio]
  exact ⟨(by norm_num : (0 : ℝ) ≤ 1).trans (hw e he),hweight⟩

/-- A rounded representative stretch is bounded by the total length
of the original graph divided by the representative edge's length,
plus the additive stretch and rounding terms. -/
theorem stretchQuery_le_stretchCapacityBound
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (G H : MGraph) (length weight : ℕ → ℝ) (P e : ℕ)
    (hsub : H.E ⊆ G.E) (he : e ∈ H.E)
    (hlen : ∀ f ∈ G.E, 0 < length f)
    (hforest : (oracle H (LSF.safeLen H length) weight).IsForest)
    (hpathEdges : walkEdges ((oracle H (LSF.safeLen H length) weight).forestPath
      (H.tail e) (H.head e)) ⊆ H.E)
    (hconn : (oracle H (LSF.safeLen H length) weight).Connected (H.tail e) (H.head e)) :
    0 ≤ stretchQuery oracle H length P weight e ∧
      stretchQuery oracle H length P weight e ≤ lastLevelStretchBound G length e := by
  let T := oracle H (LSF.safeLen H length) weight
  let path := T.forestPath (H.tail e) (H.head e)
  have hp := LSF.forestPath_isPath hforest hconn
  have hpath : walkEdges path ⊆ G.E :=
    hpathEdges.trans hsub
  have hlenEq (f : ℕ) (hf : f ∈ H.E) : LSF.safeLen H length f = length f := by
    simp [LSF.safeLen,hf]
  have hsum : walkLength (LSF.safeLen H length) path = ∑ f ∈ walkEdges path, length f := by
    unfold walkLength
    apply Finset.sum_congr rfl
    intro f hf
    have hfH := hpathEdges hf
    have habs := LSF.walkFlow_abs_of_nodup (LSF.isPath_nodup_edges hp) f
    change |walkFlow path f| = _ at habs
    rw [hlenEq f hfH,habs,ite_eq_left hf,mul_one]
  have hupper : (∑ f ∈ walkEdges path, length f) ≤ ∑ f ∈ G.E, length f :=
    Finset.sum_le_sum_of_subset_of_nonneg hpath (fun f hf _ => (hlen f hf).le)
  have hnonneg : 0 ≤ ∑ f ∈ walkEdges path, length f :=
    Finset.sum_nonneg (fun f hf => (hlen f (hpath hf)).le)
  have hepos := hlen e (hsub he)
  have hround := roundStretch_bounds P (treeStretch H T (LSF.safeLen H length) e)
  have hgrid : 1 / (2 : ℝ)^P ≤ 1 :=
    (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  change 0 ≤ roundStretch P (treeStretch H T (LSF.safeLen H length) e) ∧ _
  constructor
  · refine le_trans ?_ hround.1
    unfold treeStretch
    rw [hlenEq e he,hsum]
    positivity
  · apply hround.2.trans
    unfold treeStretch lastLevelStretchBound
    rw [hlenEq e he,hsum]
    have hd := div_le_div_of_nonneg_right hupper hepos.le
    linarith only [hgrid,hd]

/-- The LSST path guarantee and the multiplicative-weights sum bound
supply caller capacity for both numeric outputs in each round. -/
theorem packedRoundOutputCapacity
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (G H : MGraph) (length : ℕ → ℝ) (h P L j : ℕ) (ρ γ : ℝ)
    (hsub : H.E ⊆ G.E) (hG : G.E.Nonempty) (hH : H.IsValid)
    (hlen : ∀ e ∈ G.E, 0 < length e)
    (hwidth : ∀ e ∈ G.E, 2*(2 : ℝ)^P*lastLevelStretchBound G length e < Num.capacity h L) :
    let query := stretchQuery oracle H length P
    let v := weights P ρ query
    LSF.IsLSST H (LSF.safeLen H length) (v j) γ (oracle H (LSF.safeLen H length) (v j)) →
    (∀ e ∈ H.E, 1 ≤ v (j+1) e) →
    (∑ e ∈ H.E, v (j+1) e) ≤ 2*H.m →
    ∃ B : ℝ, 2*(2 : ℝ)^P*B < Num.capacity h L ∧
      (∀ e ∈ H.E, 0 ≤ query (v j) e ∧ query (v j) e ≤ B) ∧
      ∀ e ∈ H.E, 0 ≤ v (j+1) e ∧ v (j+1) e ≤ B := by
  intro query v ht hone hsum
  have hm : H.m ≤ G.m := Finset.card_le_card hsub
  obtain ⟨B,hcap,hstretch,hweight⟩ :=
    packedCapacity_of_stretchCapacity G H length (v (j+1)) h P L hm hG hlen hwidth hone hsum
  refine ⟨B,hcap,?_,hweight⟩
  intro e he
  obtain ⟨hu,hv⟩ := hH e he
  have heConn := ht.1.2.2 _ hu _ hv
  obtain ⟨hlo,hhi⟩ := stretchQuery_le_stretchCapacityBound oracle G H length (v j) P e
    hsub he hlen ht.1.1 (ht.2.2.1 e he) heConn
  exact ⟨hlo,hhi.trans (hstretch e (hsub he))⟩

/-- The scratch width has at least one more limb than the caller.
This covers the aggregate weight bound used by the arithmetic contract. -/
theorem widenedWeightCapacity (G H : MGraph) (length : ℕ → ℝ)
    (L P levels : ℕ) (hm : H.m ≤ G.m) (hne : G.E.Nonempty)
    (hlen : ∀ e ∈ G.E, 0 < length e)
    (hwidth : ∀ e ∈ G.E, 2*(2 : ℝ)^P*lastLevelStretchBound G length e < Num.capacity 4 L) :
    2*(2 : ℝ)^P*(2*(H.m : ℝ)) < Num.capacity 4 (L+(P+levels+7)/4) := by
  classical
  obtain ⟨e,he,hmin⟩ := Finset.exists_min_image G.E length hne
  have htotal : (G.m : ℝ)*length e ≤ ∑ f ∈ G.E, length f := by
    simpa [MGraph.m] using (Finset.sum_le_sum fun f hf => hmin f hf :
      (∑ _f ∈ G.E, length e) ≤ ∑ f ∈ G.E, length f)
  have hratio : (G.m : ℝ) ≤ (∑ f ∈ G.E, length f)/length e :=
    (le_div_iff₀ (hlen e he)).2 htotal
  have hm' : (H.m : ℝ) ≤ G.m := by exact_mod_cast hm
  have hsize : (H.m : ℝ) ≤ lastLevelStretchBound G length e := by
    unfold lastLevelStretchBound
    linarith only [hm',hratio]
  have hfit := (mul_le_mul_of_nonneg_left hsize (by positivity : 0 ≤ 2*(2 : ℝ)^P)).trans_lt (hwidth e he)
  have hcap : 2*Num.capacity 4 L ≤ Num.capacity 4 (L+(P+levels+7)/4) := by
    rw [Num.capacity_eq_two_pow,Num.capacity_eq_two_pow]
    rw [← Nat.pow_succ']
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hcap' : (2 : ℝ)*Num.capacity 4 L ≤ Num.capacity 4 (L+(P+levels+7)/4) := by exact_mod_cast hcap
  calc
    _ = 2*(2*(2 : ℝ)^P*(H.m : ℝ)) := by ring
    _ < 2*(Num.capacity 4 L : ℝ) := mul_lt_mul_of_pos_left hfit (by norm_num)
    _ ≤ _ := hcap'

end MinCostFlow.LastLevelProgram
