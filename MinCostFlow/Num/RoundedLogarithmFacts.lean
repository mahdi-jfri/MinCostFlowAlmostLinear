module

public import MinCostFlow.Num.DyadicRoundingFacts
public import MinCostFlow.Num.LogarithmFacts
import Mathlib.Tactic

/-!
# Rounded Horner evaluation of the logarithm series

The odd-power series is evaluated from its last coefficient towards its first.
Each coefficient is rounded down, as is each product. The squared argument is
also rounded once. Because that argument is at most one quarter, earlier errors
shrink at each step. Eight last-place units bound the Horner error, regardless
of the number of terms.
-/

@[expose] public section
namespace MinCostFlow.Num

/-- Horner evaluation of the even-power part of the odd logarithm series,
starting at coefficient `i` and taking `n` terms. -/
noncomputable def logHorner (s : ℝ) (i : ℕ) : ℕ→ℝ
  | 0 => 0
  | n+1 => 1/((2*i+1:ℕ):ℝ)+s*logHorner s (i+1) n

/-- The same recurrence with coefficients and products rounded at precision
`P`. The argument `s` is the stored, already rounded square. -/
noncomputable def roundedLogHorner (P : ℕ) (s : ℝ) (i : ℕ) : ℕ→ℝ
  | 0 => 0
  | n+1 => dyadicFloor P (1/((2*i+1:ℕ):ℝ))+
      dyadicFloor P (s*roundedLogHorner P s (i+1) n)

private theorem log_coefficient_bounds (i : ℕ) :
    0≤1/((2*i+1:ℕ):ℝ) ∧ 1/((2*i+1:ℕ):ℝ)≤1 := by
  have hp : (1:ℝ)≤((2*i+1:ℕ):ℝ) := by exact_mod_cast (show 1≤2*i+1 by omega)
  constructor
  · positivity
  · exact (div_le_one (by linarith)).mpr hp

/-- Both exact Horner tails and their rounded versions stay in `[0,2]`. -/
theorem logHorner_bounds {s : ℝ} (hs0 : 0≤s) (hs : s≤1/2) (i n : ℕ) :
    0≤logHorner s i n ∧ logHorner s i n≤2 := by
  induction n generalizing i with
  | zero => simp [logHorner]
  | succ n ih =>
    obtain ⟨hc0,hc1⟩ := log_coefficient_bounds i
    obtain ⟨ht0,ht2⟩ := ih (i+1)
    constructor
    · exact add_nonneg hc0 (mul_nonneg hs0 ht0)
    · change 1/((2*i+1:ℕ):ℝ)+s*logHorner s (i+1) n≤2
      have hm := mul_le_mul hs ht2 ht0 (by norm_num : (0:ℝ)≤1/2)
      linarith

/-- Rounding down preserves the same bounds on all intermediate Horner values. -/
theorem roundedLogHorner_bounds {s : ℝ} (hs0 : 0≤s) (hs : s≤1/2)
    (P i n : ℕ) :
    0≤roundedLogHorner P s i n ∧ roundedLogHorner P s i n≤2 := by
  induction n generalizing i with
  | zero => simp [roundedLogHorner]
  | succ n ih =>
    obtain ⟨hc0,hc1⟩ := log_coefficient_bounds i
    obtain ⟨ht0,ht2⟩ := ih (i+1)
    constructor
    · exact add_nonneg (dyadicFloor_nonneg hc0) (dyadicFloor_nonneg (mul_nonneg hs0 ht0))
    · change dyadicFloor P (1/((2*i+1:ℕ):ℝ))+
        dyadicFloor P (s*roundedLogHorner P s (i+1) n)≤2
      have hc := le_trans (dyadicFloor_le P _) hc1
      have hm := le_trans (dyadicFloor_le P _)
        (mul_le_mul hs ht2 ht0 (by norm_num : (0:ℝ)≤1/2))
      linarith

/-- Eight units cover every coefficient rounding, every product rounding,
and a one-unit error in the squared argument, for any number of terms. -/
theorem roundedLogHorner_error {s r : ℝ} {P : ℕ}
    (hs0 : 0≤s) (hs : s≤1/2) (hr0 : 0≤r) (hr : r≤1/2)
    (hsr : |s-r|≤1/(2:ℝ)^P) (i n : ℕ) :
    |roundedLogHorner P s i n-logHorner r i n|≤8/(2:ℝ)^P := by
  induction n generalizing i with
  | zero => simp [roundedLogHorner,logHorner]; positivity
  | succ n ih =>
    have htail := ih (i+1)
    obtain ⟨ht0,ht2⟩ := logHorner_bounds hr0 hr (i+1) n
    have hsplit : s*roundedLogHorner P s (i+1) n-r*logHorner r (i+1) n=
        s*(roundedLogHorner P s (i+1) n-logHorner r (i+1) n)+
          (s-r)*logHorner r (i+1) n := by ring
    have hprod : |s*roundedLogHorner P s (i+1) n-r*logHorner r (i+1) n|≤
        (1/2:ℝ)*(8/(2:ℝ)^P)+(1/(2:ℝ)^P)*2 := by
      rw [hsplit]
      calc
        _ ≤ |s*(roundedLogHorner P s (i+1) n-logHorner r (i+1) n)|+
            |(s-r)*logHorner r (i+1) n| := abs_add_le _ _
        _ = s*|roundedLogHorner P s (i+1) n-logHorner r (i+1) n|+
            |s-r| *logHorner r (i+1) n := by
          rw [abs_mul,abs_mul,abs_of_nonneg hs0,abs_of_nonneg ht0]
        _ ≤ (1/2:ℝ)*(8/(2:ℝ)^P)+(1/(2:ℝ)^P)*2 :=
          add_le_add (mul_le_mul hs htail (abs_nonneg _) (by norm_num))
            (mul_le_mul hsr ht2 ht0 (by positivity))
    have hp := abs_sub_le (dyadicFloor P (s*roundedLogHorner P s (i+1) n))
      (s*roundedLogHorner P s (i+1) n) (r*logHorner r (i+1) n)
    have hp' := le_trans hp (add_le_add (dyadicFloor_error P _) hprod)
    have hc := dyadicFloor_error P (1/((2*i+1:ℕ):ℝ))
    have hsum := abs_add_le
      (dyadicFloor P (1/((2*i+1:ℕ):ℝ))-1/((2*i+1:ℕ):ℝ))
      (dyadicFloor P (s*roundedLogHorner P s (i+1) n)-r*logHorner r (i+1) n)
    have he : roundedLogHorner P s i (n+1)-logHorner r i (n+1)=
        (dyadicFloor P (1/((2*i+1:ℕ):ℝ))-1/((2*i+1:ℕ):ℝ))+
        (dyadicFloor P (s*roundedLogHorner P s (i+1) n)-r*logHorner r (i+1) n) := by
      simp only [roundedLogHorner,logHorner]
      ring
    rw [he]
    have hb := le_trans hsum (add_le_add hc hp')
    simp only [div_eq_mul_inv] at hb ⊢
    linarith only [hb]

/-- The Horner recurrence is the finite even-power sum. -/
theorem logHorner_sum (s : ℝ) (i n : ℕ) :
    logHorner s i n=∑ k∈Finset.range n,s^k/((2*(i+k)+1:ℕ):ℝ) := by
  induction n generalizing i with
  | zero => simp [logHorner]
  | succ n ih =>
    rw [logHorner,ih,Finset.sum_range_succ',Finset.mul_sum]
    simp only [pow_zero,add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [show i+(k+1)=(i+1)+k by omega,pow_succ]
    ring

/-- Multiplying the even-power Horner sum by twice the argument recovers
the truncated odd-power logarithm series. -/
theorem logHorner_series (x : ℝ) (n : ℕ) :
    2*((x-1)/(x+1))*logHorner (((x-1)/(x+1))^2) 0 n=logSeries x n := by
  rw [logHorner_sum,logSeries]
  simp only [zero_add]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← pow_mul,pow_succ]
  push_cast
  ring

/-- Changing the squared argument changes a Horner tail by at most four
times that change, uniformly in its length. -/
theorem logHorner_argument_error {s r δ : ℝ}
    (hs0 : 0≤s) (hs : s≤1/2) (hr0 : 0≤r) (hr : r≤1/2)
    (hδ : 0≤δ) (hsr : |s-r|≤δ) (i n : ℕ) :
    |logHorner s i n-logHorner r i n|≤4*δ := by
  induction n generalizing i with
  | zero => simp [logHorner]; positivity
  | succ n ih =>
    obtain ⟨ht0,ht2⟩ := logHorner_bounds hr0 hr (i+1) n
    have he : logHorner s i (n+1)-logHorner r i (n+1)=
        s*(logHorner s (i+1) n-logHorner r (i+1) n)+(s-r)*logHorner r (i+1) n := by
      simp only [logHorner]
      ring
    rw [he]
    calc
      _ ≤ |s*(logHorner s (i+1) n-logHorner r (i+1) n)|+
          |(s-r)*logHorner r (i+1) n| := abs_add_le _ _
      _ = s*|logHorner s (i+1) n-logHorner r (i+1) n|+
          |s-r| * logHorner r (i+1) n := by
        rw [abs_mul,abs_mul,abs_of_nonneg hs0,abs_of_nonneg ht0]
      _ ≤ (1/2:ℝ)*(4*δ)+δ*2 := add_le_add
        (mul_le_mul hs (ih (i+1)) (abs_nonneg _) (by norm_num))
        (mul_le_mul hsr ht2 ht0 hδ)
      _ = 4*δ := by ring

end MinCostFlow.Num
