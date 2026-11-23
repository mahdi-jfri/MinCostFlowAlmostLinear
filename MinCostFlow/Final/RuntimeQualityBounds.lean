module

public import MinCostFlow.Final.RuntimeQuality
public import MinCostFlow.Chain.Theorem5_1Asymptotics
public import MinCostFlow.IPM.Machine.PrecisionDyadic
public import MinCostFlow.IPM.Machine.SolverInitialBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Asymptotic bounds on the integer quality exponent

Taking two binary lengths replaces the real logarithms in the
Theorem 5.1 (page 15) quality bound by integer estimates. The shift
rounds the logarithmic power upward, at a constant multiplicative cost.
-/

public section
namespace MinCostFlow.Final
open Chain

private theorem size_log_upper (n : ℕ) :
    Real.log ((n:ℝ)+2) ≤ (n.size:ℝ)+1 := by
  have h : n+2 ≤ 2^(n.size+1) := by
    rw [pow_succ]
    have := Nat.lt_size_self n
    omega
  have hx : (0:ℝ) < (n:ℝ)+2 := by positivity
  have hcast : (n:ℝ)+2 ≤ (2:ℝ)^(n.size+1) := by exact_mod_cast h
  refine (Real.log_le_log hx hcast).trans ?_
  rw [Real.log_pow, Nat.cast_add, Nat.cast_one]
  exact mul_le_of_le_one_right (by positivity) (Real.log_two_lt_d9.le.trans (by norm_num))

private theorem size_log_lower (n : ℕ) (hn : 0 < n) :
    (n.size:ℝ) ≤ 2*Real.log (n:ℝ)+1 := by
  have hk : 0 < n.size := Nat.size_pos.mpr hn
  have hp : 2^(n.size-1) ≤ n := Nat.lt_size.mp (by omega)
  have hcast : (2:ℝ)^(n.size-1) ≤ n := by exact_mod_cast hp
  have hl := Real.log_le_log (show 0 < (2:ℝ)^(n.size-1) by positivity) hcast
  rw [Real.log_pow, Nat.cast_sub (by omega : 1 ≤ n.size), Nat.cast_one] at hl
  have hHalf : (1/2:ℝ) ≤ Real.log 2 := Real.log_two_gt_d9.le.trans' (by norm_num)
  have hz : (0:ℝ) ≤ (n.size:ℝ)-1 := by exact sub_nonneg.mpr (by exact_mod_cast hk)
  have hl' := (mul_le_mul_of_nonneg_left hHalf hz).trans hl
  linarith only [hl']

private theorem binary_rounded_power (L : ℕ) (hL : 0 < L) :
    let b := L.size
    let q := (47*b+47)/48
    (L:ℝ)^((47:ℝ)/48) ≤ (2:ℝ)^q ∧ (2:ℝ)^q ≤ 4*(L:ℝ)^((47:ℝ)/48) := by
  dsimp only
  let a : ℝ := 47/48
  let b := L.size
  let q := (47*b+47)/48
  have hb : 0 < b := Nat.size_pos.mpr hL
  have hl : (L:ℝ) ≤ (2:ℝ)^b := by exact_mod_cast (Nat.lt_size_self L).le
  have hu : (2:ℝ)^b ≤ 2*(L:ℝ) := by
    have hp : 2^(b-1) ≤ L := Nat.lt_size.mp (by omega)
    have he : b = b-1+1 := by omega
    have h₁ : 2^b ≤ L*2 := by
      conv_lhs => rw [he, pow_succ]
      exact Nat.mul_le_mul_right _ hp
    simpa [mul_comm] using (show (2:ℝ)^b ≤ (L:ℝ)*2 by exact_mod_cast h₁)
  have hceil : 47*b ≤ 48*q ∧ 48*q ≤ 47*b+47 := by dsimp [q]; omega
  have hcast₁ : (47:ℝ)*b ≤ 48*q := by exact_mod_cast hceil.1
  have hcast₂ : (48:ℝ)*q ≤ 47*b+47 := by exact_mod_cast hceil.2
  have hlow : (b:ℝ)*a ≤ q := by dsimp [a]; linarith only [hcast₁]
  have hhigh : (q:ℝ) ≤ (b:ℝ)*a+1 := by dsimp [a]; linarith only [hcast₂]
  have h₂ : (1:ℝ) ≤ 2 := by norm_num
  have ha : 0 ≤ a := by norm_num [a]
  have hbase : 0 ≤ (L:ℝ) := by positivity
  have hrewrite : (2:ℝ)^((b:ℝ)*a) = ((2:ℝ)^b)^a :=
    Real.rpow_natCast_mul (by norm_num) b a
  change (L:ℝ)^a ≤ (2:ℝ)^q ∧ (2:ℝ)^q ≤ 4*(L:ℝ)^a
  constructor
  · rw [← Real.rpow_natCast]
    exact (Real.rpow_le_rpow hbase hl ha).trans
      (hrewrite.symm.trans_le (Real.rpow_le_rpow_of_exponent_le h₂ hlow))
  · have hA : (2:ℝ)^a ≤ 2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le h₂ (show a ≤ 1 by norm_num [a])
    calc
      (2:ℝ)^q ≤ (2:ℝ)^((b:ℝ)*a+1) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le h₂ hhigh
      _ = ((2:ℝ)^b)^a*2 := by rw [Real.rpow_add (by norm_num), hrewrite, Real.rpow_one]
      _ ≤ (2*(L:ℝ))^a*2 :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hu ha) (by norm_num)
      _ ≤ 4*(L:ℝ)^a := by
        rw [Real.mul_rpow (by norm_num) hbase]
        calc
          (2:ℝ)^a*(L:ℝ)^a*2 ≤ 2*(L:ℝ)^a*2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA (by positivity)) (by norm_num)
          _ = _ := by ring

/-- The integer procedure returns a dyadic quality no larger than the
Theorem 5.1 lower bound with coefficient `A`, and its reciprocal is
bounded by the same subpolynomial shape with an explicit coefficient. -/
theorem integerQualityExponent_bounds (A M : ℕ) :
    1/(2:ℝ)^integerQualityExponent A M ≤ alg2KappaLower A (47/48) M ∧
    (2:ℝ)^integerQualityExponent A M ≤ alg2TimeFactor (65536*((A:ℝ)+1)) (47/48) M := by
  let a : ℝ := 47/48
  let x := Real.log ((M:ℝ)+2)
  let y := Real.log (x+2)
  let L := M.size+1
  let b := L.size
  let q := (47*b+47)/48
  have hHalf : (1/2:ℝ) ≤ Real.log 2 := Real.log_two_gt_d9.le.trans' (by norm_num)
  have hTwo : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
  have hx : (1/2:ℝ) ≤ x := hHalf.trans (Real.log_le_log (by norm_num) (le_add_of_nonneg_left (Nat.cast_nonneg M)))
  have hy : (1/2:ℝ) ≤ y := hHalf.trans (Real.log_le_log (by norm_num) (by linarith))
  have hxL : x ≤ (L:ℝ) := by simpa only [L,Nat.cast_add,Nat.cast_one] using size_log_upper M
  have hLx : (L:ℝ) ≤ 6*x := by
    cases M with
    | zero => simp only [L,Nat.size_zero,Nat.zero_add,Nat.cast_one]; linarith only [hx]
    | succ m =>
      have hs := size_log_lower (m+1) (by omega)
      have hlog : Real.log ((m+1:ℕ):ℝ) ≤ x :=
        Real.log_le_log (by positivity) (by linarith)
      simp only [L,Nat.cast_add,Nat.cast_one]
      linarith only [hx,hs,hlog]
  have hyb : y ≤ 2*(b:ℝ) := by
    have hle : y ≤ Real.log ((L:ℝ)+2) := Real.log_le_log (by linarith) (by linarith only [hxL])
    have hb : (1:ℝ) ≤ b := by exact_mod_cast Nat.size_pos.mpr (show 0 < L by unfold L; omega)
    linarith only [hle,size_log_upper L,hb]
  have hby : (b:ℝ) ≤ 16*y := by
    have hs := size_log_lower L (show 0 < L by unfold L; omega)
    have hle : Real.log (L:ℝ) ≤ Real.log (6*(x+2)) :=
      Real.log_le_log (by exact_mod_cast (show 0 < L by unfold L; omega)) (by linarith only [hLx])
    rw [Real.log_mul (by norm_num) (by linarith only [hx])] at hle
    have h6 : Real.log 6 ≤ 3 := by
      have hh := Real.log_le_log (by norm_num : (0:ℝ)<6) (show (6:ℝ)≤2^3 by norm_num)
      rw [Real.log_pow] at hh
      norm_num at hh
      linarith only [hh,hTwo]
    change _ ≤ Real.log 6 + y at hle
    linarith only [hs,hle,h6,hy]
  obtain ⟨hLo,hHi⟩ := binary_rounded_power L (show 0 < L by unfold L; omega)
  change (L:ℝ)^a ≤ (2:ℝ)^q at hLo
  change (2:ℝ)^q ≤ 4*(L:ℝ)^a at hHi
  have hLow : x^a ≤ (2:ℝ)^q := (Real.rpow_le_rpow (by linarith) hxL (by norm_num [a])).trans hLo
  have hHigh : (2:ℝ)^q ≤ 24*x^a := by
    have hex : (L:ℝ)^a ≤ (6*x)^a := Real.rpow_le_rpow (by positivity) hLx (by norm_num [a])
    rw [Real.mul_rpow (by norm_num) (by linarith only [hx])] at hex
    have hsix : (6:ℝ)^a ≤ 6 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (show (1:ℝ)≤6 by norm_num) (show a≤1 by norm_num [a])
    have h' := mul_le_mul_of_nonneg_right hsix (Real.rpow_nonneg (by linarith only [hx]) a)
    linarith only [hHi,hex,h']
  have hK : (integerQualityExponent A M:ℝ) = 128*((A:ℝ)+1)*b*(2:ℝ)^q := by
    simp only [integerQualityExponent,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,Nat.cast_pow]
    rfl
  have hxpow : 0 ≤ x^a := Real.rpow_nonneg (by linarith only [hx]) _
  have hab : 0 ≤ (A:ℝ)+1 := by positivity
  have hLower : (A:ℝ)*x^a*y ≤ (integerQualityExponent A M:ℝ)*Real.log 2 := by
    rw [hK]
    have h := mul_le_mul (show y/2 ≤ (b:ℝ) by linarith only [hyb]) hLow hxpow (by positivity)
    have h' := mul_le_mul_of_nonneg_left (mul_le_mul h hHalf (by norm_num) (by positivity)) hab
    have h₀ : 0 ≤ (A:ℝ)*x^a*y := by positivity
    have h₁ : 0 ≤ x^a*y := mul_nonneg hxpow (by linarith only [hy])
    nlinarith only [h',h₀,h₁]
  have hUpper : (integerQualityExponent A M:ℝ)*Real.log 2 ≤
      65536*((A:ℝ)+1)*x^a*y := by
    rw [hK]
    have h := mul_le_mul hby hHigh (by positivity) (by linarith only [hy])
    have hPos : 0 ≤ 16*y*(24*x^a) := mul_nonneg (by linarith only [hy]) (mul_nonneg (by norm_num) hxpow)
    have h' := mul_le_mul_of_nonneg_left (mul_le_mul h hTwo (by linarith only [hHalf]) hPos)
      (show 0 ≤ 128*((A:ℝ)+1) by positivity)
    have hn : 0 ≤ ((A:ℝ)+1)*x^a*y := by positivity
    nlinarith only [h',hn]
  have hE : (2:ℝ)^integerQualityExponent A M =
      Real.exp ((integerQualityExponent A M:ℝ)*Real.log 2) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  constructor
  · rw [alg2KappaLower,hE,one_div,← Real.exp_neg]
    exact Real.exp_le_exp.mpr (neg_le_neg hLower)
  · rw [alg2TimeFactor,hE]
    exact Real.exp_le_exp.mpr hUpper


/-- The computed reciprocal quality satisfies the linear envelope needed
by the solver's polynomial reservation. -/
theorem integerQualityExponent_linear (A : ℕ) :
    ∃ C : ℕ, ∀ M, 2^integerQualityExponent A M ≤ C*(M+2) := by
  obtain ⟨B,hB,hBound⟩ :=
    alg2TimeFactor_le_rpow (C := 65536*((A:ℝ)+1)) (a := 47/48)
      (by norm_num) (by norm_num) (δ := 1) (by norm_num)
  refine ⟨max (Nat.ceil B) (2^integerQualityExponent A 0), ?_⟩
  intro M
  by_cases hM : M = 0
  · subst M
    exact (le_max_right _ _).trans (Nat.le_mul_of_pos_right _ (by decide))
  · have h := (integerQualityExponent_bounds A M).2.trans (hBound M (Nat.pos_of_ne_zero hM))
    rw [Real.rpow_one] at h
    have hc : B ≤ (max (Nat.ceil B) (2^integerQualityExponent A 0) : ℕ) :=
      (Nat.le_ceil B).trans (by exact_mod_cast le_max_left (Nat.ceil B) (2^integerQualityExponent A 0))
    have h' : (2:ℝ)^integerQualityExponent A M ≤
        (max (Nat.ceil B) (2^integerQualityExponent A 0) : ℕ) * ((M:ℝ)+2) := by
      have h₁ := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg M)
      have h₂ := mul_le_mul_of_nonneg_left (show (M:ℝ) ≤ (M:ℝ)+2 by linarith)
        (Nat.cast_nonneg (max (Nat.ceil B) (2^integerQualityExponent A 0)))
      exact h.trans (h₁.trans h₂)
    exact_mod_cast h'

/-- Computing the exponent once costs at most a linear function of the
augmented edge count. -/
theorem integerQualityCost_le (M : ℕ) : integerQualityCost M ≤ 100*(M+1) := by
  have h₁ := Num.IPM.size_le_value M
  have h₂ := Num.IPM.size_le_value (M.size+1)
  unfold integerQualityCost
  omega


/-- The fixed IPM range fits the integer exponent whenever the chosen
quality budget is at most 858 and the numerical input bound is positive. -/
theorem integerQualityExponent_le_slackRange (A M V : ℕ) (hA : A ≤ 858) (hV : 0 < V) :
    integerQualityExponent A M ≤ IPM.Machine.slackRangeExponent M V := by
  let L := M.size+1
  let b := L.size
  let q := (47*b+47)/48
  have hL : 0 < L := by unfold L; omega
  have hb : 0 < b := Nat.size_pos.mpr hL
  have hq : q ≤ b := by unfold q; omega
  have hPow : 2^b ≤ 2*L := by
    have h := Nat.lt_size.mp (show b-1 < L.size by change b-1<b; omega)
    have he : b = (b-1)+1 := by omega
    conv_lhs => rw [he, pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_left 2 h
  have hbL := Num.IPM.size_le_value L
  have hSize : L ≤ M.size+V.size := Nat.add_le_add_left (Nat.size_pos.mpr hV) _
  change 128*(A+1)*b*2^q ≤ 220000*(M.size+V.size)^2
  calc
    _ ≤ (128*859)*L*(2*L) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 128 (by omega)) hbL)
        ((Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hq).trans hPow)
    _ = 219904*L^2 := by ring
    _ ≤ _ := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left hSize _)

/-- A large budget can exceed the IPM's numerical range even though the
integer computation and the subpolynomial bound both apply. -/
theorem integerQualityExponent_two_exceeds_range :
    IPM.Machine.slackRangeExponent 2 (IPM.Machine.solverPenalty 2) <
      integerQualityExponent 10000000 2 := by
  decide

end MinCostFlow.Final
