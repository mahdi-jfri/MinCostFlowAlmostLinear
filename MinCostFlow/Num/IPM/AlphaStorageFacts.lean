module

public import MinCostFlow.Num.Representation
import MinCostFlow.Num.WordBounds
import Mathlib.Tactic

/-!
# Storing the dyadic barrier exponent

The numerator of `2⁻ᵏ` at precision `P` has just one set bit, at position
`P-k`. Fresh-zero memory therefore needs only one limb store. Two spare bits
above precision ensure that signed decoding reads this numerator as positive.
-/

public section
namespace MinCostFlow.Num.IPM

/-- A block with one nonzero limb has the corresponding base-weighted value. -/
theorem unsignedVal_single_limb {mem : ℕ→ℕ} {a h L j d : ℕ}
    (hj : j<L) (hm : ∀ i<L,mem (a+i)=if i=j then d else 0) :
    unsignedVal mem a h L=d*base h^j := by
  induction L generalizing a j with
  | zero => omega
  | succ L ih =>
    cases j with
    | zero =>
      have hhead : mem a=d := by simpa using hm 0 (by omega)
      have htail : ∀ i<L,mem ((a+1)+i)=0 := by
        intro i hi
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hm (i+1) (by omega)
      rw [unsignedVal,hhead,unsignedVal_zero htail,mul_zero,add_zero,pow_zero,mul_one]
    | succ j =>
      have hhead : mem a=0 := by simpa using hm 0 (by omega)
      have htail : ∀ i<L,mem ((a+1)+i)=if i=j then d else 0 := by
        intro i hi
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hm (i+1) (by omega)
      rw [unsignedVal,hhead,zero_add,ih (by omega) htail,pow_succ]
      ring

/-- The single set bit denotes the intended dyadic fixed-point value. -/
theorem alphaBlock_spec {mem : ℕ→ℕ} {a h L P k : ℕ}
    (hh : 0<h) (hk : k≤P) (hwidth : P+2≤h*L)
    (hm : ∀ i<L,mem (a+i)=if i=(P-k)/h then 2^((P-k)%h) else 0) :
    Valid mem a h L ∧ fixVal mem a h L P=1/(2:ℝ)^k := by
  have hs : P-k<h*L := by omega
  have hj : (P-k)/h<L := (Nat.div_lt_iff_lt_mul hh).mpr (by simpa only [mul_comm] using hs)
  have hd : 2^((P-k)%h)<base h := by
    exact Nat.pow_lt_pow_right (by decide) (Nat.mod_lt _ hh)
  have hvalid : Valid mem a h L := by
    intro i hi
    rw [hm i hi]
    split_ifs
    · exact hd
    · exact base_pos h
  have hval := unsignedVal_single_limb (h:=h) hj hm
  have hpow : 2^((P-k)%h)*base h^((P-k)/h)=2^(P-k) := by
    rw [base,← pow_mul,← pow_add,Nat.mod_add_div]
  rw [hpow] at hval
  have hcap : ¬capacity h L≤2*2^(P-k) := by
    rw [capacity_eq_two_pow]
    have he : 2*2^(P-k)=2^(P-k+1) := by rw [pow_succ]; omega
    rw [he]
    exact not_le.mpr (Nat.pow_lt_pow_right (by decide) (by omega))
  have hdecode : intVal mem a h L=(2:ℤ)^(P-k) := by
    simp only [intVal,hval,signedVal,ite_eq_right hcap,sub_zero,Nat.cast_pow,Nat.cast_ofNat]
  refine ⟨hvalid,?_⟩
  rw [fixVal,hdecode]
  push_cast
  have he : (2:ℝ)^P=(2:ℝ)^(P-k)*(2:ℝ)^k := by rw [← pow_add,Nat.sub_add_cancel hk]
  rw [he]
  field_simp

end MinCostFlow.Num.IPM
