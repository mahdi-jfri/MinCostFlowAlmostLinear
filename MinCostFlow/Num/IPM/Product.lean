module

public import MinCostFlow.Num.FixedMultiply
public import MinCostFlow.Num.IPM.DivideFacts
public import MinCostFlow.Num.DyadicRoundingFacts
import Mathlib.Tactic

/-!
# Rounded products in gradient arithmetic

Fixed-point multiplication rounds once. An explicit bound on the real
product supplies the signed-fit condition and bounds the stored result.
These facts apply to alpha times the difference of the two slack powers.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM
open WordRAM

/-- The integer product numerator is the scaled real product rounded down. -/
theorem product_floor (A B : ℤ) (P : ℕ) :
    A*B/(2:ℤ)^P=⌊((A:ℝ)/(2:ℝ)^P*((B:ℝ)/(2:ℝ)^P))*(2:ℝ)^P⌋ := by
  have he := floorDiv_eq_floor (A*B) ((2:ℤ)^P)
  have hn : ¬(2:ℤ)^P<0 := not_lt.mpr (by positivity)
  simp only [floorDiv,if_neg hn] at he
  rw [he]
  congr 1
  push_cast
  field_simp

/-- The rounded-product procedure is the existing fixed multiplier. -/
def productModule (b h : ℕ) := fixedMultiplyModule b h

/-- A product of absolute size at most `2^D` requires `P+D+3` bits.
The result at `v-L` has error at most `2^-P` and absolute size at most `2^(D+1)`.
Cost and space are exactly the fixed multiplier's bounds. -/
def productContract (w h D : ℕ) : Contract where
  pre args mem := (∃ a d L P heap,args=[a,d,L,P,heap] ∧ h∣P ∧
    P+D+3≤h*L ∧ a+L≤heap ∧ d+L≤heap ∧ Valid mem a h L ∧ Valid mem d h L ∧
    |fixVal mem a h L P*fixVal mem d h L P|≤(2:ℝ)^D) ∧
    ZeroFrom mem (heapArg args) ∧ heapArg args+11*args.getD 2 0+1<2^w
  post args mem v mem' := (fixedMultiplyContract w h).post args mem v mem' ∧
    |fixVal mem' (v-args.getD 2 0) h (args.getD 2 0) (args.getD 3 0)-
      fixVal mem (args.getD 0 0) h (args.getD 2 0) (args.getD 3 0)*
      fixVal mem (args.getD 1 0) h (args.getD 2 0) (args.getD 3 0)|≤1/(2:ℝ)^(args.getD 3 0) ∧
    |fixVal mem' (v-args.getD 2 0) h (args.getD 2 0) (args.getD 3 0)|≤(2:ℝ)^(D+1)
  cost := (fixedMultiplyContract w h).cost

/-- Rounded multiplication is deterministic. -/
theorem productModule_noRand (b h : ℕ) : ∀ s∈productModule b h,s.NoRand :=
  fixedMultiplyModule_noRand b h

/-- Explicit real product ranges ensure that the multiplier does not wrap. -/
theorem product_meetsContract {w h b D : ℕ} {p : Program}
    (hh : 0<h) (hw : 2*h+2≤w) (hp : p.HasAt b (productModule b h)) :
    MeetsContract w p b (productContract w h D) := by
  have hc := fixedMultiply_meetsContract hh hw hp
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨a,d,L,P,heap,rfl,hP,hwidth,ha,hd,hva,hvd,hB⟩,hz,hbound⟩
  have hfit : Fits h L (intVal mem a h L*intVal mem d h L/(2:ℤ)^P) := by
    rw [product_floor]
    exact floor_scaled_fits hB hwidth
  have hpre' : (fixedMultiplyContract w h).pre [a,d,L,P,heap] mem :=
    ⟨⟨_,_,_,_,_,rfl,hP,ha,hd,hva,hvd⟩,hz,hbound⟩
  obtain ⟨body,hbody,o,st,c,hrun,hpost,hcost⟩ := hc _ _ pos ω hwords hpre'
  have he := fixedMultiply_value_of_fits hpost hfit
  have hv := hpost.1
  change o.value=heap+11*L+1 at hv
  have hptr : o.value-L=heap+10*L+1 := by omega
  have hdecode : fixVal st.mem (o.value-L) h L P=
      dyadicFloor P (fixVal mem a h L P*fixVal mem d h L P) := by
    rw [hptr,fixVal,he,← dyadicFloor_product]
    rfl
  have herr : |fixVal st.mem (o.value-L) h L P-
      fixVal mem a h L P*fixVal mem d h L P|≤1/(2:ℝ)^P := by
    rw [hdecode]; exact dyadicFloor_error _ _
  refine ⟨body,hbody,o,st,c,hrun,⟨hpost,herr,?_⟩,hcost⟩
  change |fixVal st.mem (o.value-L) h L P|≤(2:ℝ)^(D+1)
  have ht : |fixVal st.mem (o.value-L) h L P|≤
      |fixVal st.mem (o.value-L) h L P-fixVal mem a h L P*fixVal mem d h L P|+
      |fixVal mem a h L P*fixVal mem d h L P| := by
    simpa only [sub_add_cancel] using
      abs_add_le (fixVal st.mem (o.value-L) h L P-fixVal mem a h L P*fixVal mem d h L P)
        (fixVal mem a h L P*fixVal mem d h L P)
  have hu : 1/(2:ℝ)^P≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hD : (1:ℝ)≤(2:ℝ)^D := one_le_pow₀ (by norm_num)
  rw [pow_succ]
  linarith only [ht,herr,hB,hu,hD]

end MinCostFlow.Num.IPM
