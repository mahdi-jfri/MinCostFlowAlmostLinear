module

public import MinCostFlow.IPM.Machine.GuardedCoefficientAccuracy

/-!
# Preserving an already refreshed edge's coefficient bounds

A later reported edge can change a different flow and different
coefficient entries. The original bounds remain valid when the earlier
edge's source and coefficient blocks are unchanged. Use block equality
rather than whole-prefix equality, since other flow entries may change.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Preserving the eight relevant blocks preserves coefficient validity
and both numerical error bounds for an already refreshed edge. -/
theorem cached_coefficient_accuracy_congr
    {h q m c r lo f up a L P ld gd : ℕ} {mem mem' : ℕ → ℕ}
    (hblocks : ∀ p∈[c,r,lo,f,up,a,ld,gd],∀ i<L,mem' (p+i)=mem (p+i))
    (hacc : Num.Valid mem ld h L ∧
      ScalarApprox (1+1/(2:ℝ)^q) (Num.fixVal mem ld h L P)
        (Num.IPM.arrayLength mem lo f up a h L P 0) ∧
      Num.Valid mem gd h L ∧
      |Num.fixVal mem gd h L P-Num.IPM.arrayGradient mem m c r lo f up a h L P 0|≤
        (1/(2:ℝ)^q)*Num.IPM.arrayLength mem lo f up a h L P 0) :
    Num.Valid mem' ld h L ∧
      ScalarApprox (1+1/(2:ℝ)^q) (Num.fixVal mem' ld h L P)
        (Num.IPM.arrayLength mem' lo f up a h L P 0) ∧
      Num.Valid mem' gd h L ∧
      |Num.fixVal mem' gd h L P-Num.IPM.arrayGradient mem' m c r lo f up a h L P 0|≤
        (1/(2:ℝ)^q)*Num.IPM.arrayLength mem' lo f up a h L P 0 := by
  have hInt (p : ℕ) (hp : p∈[c,r,lo,f,up,a,ld,gd]) :
      Num.intVal mem' p h L=Num.intVal mem p h L := Num.intVal_congr (hblocks p hp)
  have hFix (p : ℕ) (hp : p∈[c,r,lo,f,up,a,ld,gd]) :
      Num.fixVal mem' p h L P=Num.fixVal mem p h L P := by
    unfold Num.fixVal
    rw [hInt p hp]
  have hLen : Num.IPM.arrayLength mem' lo f up a h L P 0=
      Num.IPM.arrayLength mem lo f up a h L P 0 := by
    simp only [Num.IPM.arrayLength,Nat.zero_mul,Nat.add_zero,
      hFix up (by simp),hFix f (by simp),hFix lo (by simp),hFix a (by simp)]
  have hGrad : Num.IPM.arrayGradient mem' m c r lo f up a h L P 0=
      Num.IPM.arrayGradient mem m c r lo f up a h L P 0 := by
    simp only [Num.IPM.arrayGradient,Nat.zero_mul,Nat.add_zero,
      hFix up (by simp),hFix f (by simp),hFix lo (by simp),hFix a (by simp),
      hFix r (by simp),hInt c (by simp)]
  refine ⟨?_,?_,?_,?_⟩
  · intro i hi
    rw [hblocks ld (by simp) i hi]
    exact hacc.1 i hi
  · rw [hFix ld (by simp),hLen]
    exact hacc.2.1
  · intro i hi
    rw [hblocks gd (by simp) i hi]
    exact hacc.2.2.1 i hi
  · rw [hFix gd (by simp),hGrad,hLen]
    exact hacc.2.2.2

end MinCostFlow.IPM.Machine
