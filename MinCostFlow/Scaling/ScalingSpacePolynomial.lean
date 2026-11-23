module

public import MinCostFlow.Scaling.PrunedScalingSpace

/-!
# Uniform polynomial workspace bounds for composed scaling

A size base covering both graph dimensions and the cost bound, with a
fourth-power supplied capacity budget, covers the entire nested scaling
reserve. The cost-round base is at most power twenty-one. Its fixed
per-round reserve and logarithmic count then give power 11008 for the
complete pruned scaling adapter. These bounds do not depend on which
optimal flow the deterministic solver chooses.
-/

public section
namespace MinCostFlow.Scaling.Machine

set_option exponentiation.threshold 32768 in
set_option maxRecDepth 65536 in
/-- Dimensions and cost at most `b`, and capacity budget at most `b^4`,
give a uniform `b^11008` reserve for the complete pruned scaling program. -/
theorem prunedScalingSpace_le_pow (J : Circulation) (C U b : ℕ) (hb6 : 6≤b)
    (hn : J.n≤b) (hm : J.m≤b) (hC : C≤b) (hU : U≤b^4) :
    prunedScalingSpace J C U≤b^11008 := by
  let V := max U (2*J.m+1)
  let D := costStepNumberBase J C V
  let fuel := costRounds J.n C
  have hbpos : 0<b := by omega
  have hb2 : 36≤b^2 := Nat.pow_le_pow_left hb6 2
  have h14b : 14*b≤b^3 :=
    (Nat.mul_le_mul_right b (show 14≤b^2 by omega)).trans_eq (pow_succ b 2).symm
  have h2_4 : b^2≤b^4 := Nat.pow_le_pow_right hbpos (by decide)
  have hb_4 : b≤b^4 := Nat.le_pow (by decide)
  have h3b : 3*b≤b^2 := by simpa only [pow_two] using Nat.mul_le_mul_right b (show 3≤b by omega)
  have hV : V≤b^4 := max_le hU (by omega)
  have hdouble : J.m+J.m≤b^2 := by
    have hh : 2*b≤b^2 := by simpa only [pow_two] using Nat.mul_le_mul_right b (show 2≤b by omega)
    omega
  have hten : (J.m+J.m)^10≤b^20 := by
    simpa only [←pow_mul] using Nat.pow_le_pow_left hdouble 10
  have hlinear : J.n+4*J.m+C+8≤14*b := by omega
  have hlinear' : J.n+4*J.m+C+V+8≤b^5 := by
    have h3_4 : b^3≤b^4 := Nat.pow_le_pow_right hbpos (by decide)
    have h4_5 : 2*b^4≤b^5 :=
      (Nat.mul_le_mul_right (b^4) (show 2≤b by omega)).trans_eq (pow_succ' b 4).symm
    omega
  have h5_20 : b^5≤b^20 := Nat.pow_le_pow_right hbpos (by decide)
  have hD : D≤b^21 := by
    have hh : 2*b^20≤b^21 :=
      (Nat.mul_le_mul_right (b^20) (show 2≤b by omega)).trans_eq (pow_succ' b 20).symm
    change J.n+4*J.m+(J.m+J.m)^10+C+V+8≤b^21
    omega
  have hN : D^524≤b^11004 := by
    simpa only [←pow_mul] using Nat.pow_le_pow_left hD 524
  have hCLog : Nat.clog 2 (C+1)≤C+1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hnLog : Nat.clog 2 (J.n+1)≤J.n+1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hfuel : fuel+2≤b^2 := by
    have hh : 3*b≤b^2 := by simpa only [pow_two] using Nat.mul_le_mul_right b (show 3≤b by omega)
    change 1+Nat.clog 2 (C+1)+Nat.clog 2 (J.n+1)+2≤b^2
    omega
  have hcells : (fuel+2)*D^524≤b^11006 := by
    simpa only [←pow_add] using Nat.mul_le_mul hfuel hN
  have hlinS : J.solverWords.length+J.n+2+J.m+2*J.n+3+J.m+3≤14*b := by
    rw [J.solverWords_length]
    omega
  have h3_11006 : b^3≤b^11006 := Nat.pow_le_pow_right hbpos (by decide)
  have hS : costScalingSpace J C V≤b^11007 := by
    have hh : 2*b^11006≤b^11007 :=
      (Nat.mul_le_mul_right (b^11006) (show 2≤b by omega)).trans_eq (pow_succ' b 11006).symm
    change J.solverWords.length+J.n+2+J.m+2*J.n+3+(fuel+2)*D^524+J.m+3≤b^11007
    omega
  have hprune : prunedScalingSpace J C U≤b^11008 := by
    have hs := prunedScalingSpace_le J C U
    change prunedScalingSpace J C U≤2+10*J.m+costScalingSpace J C V at hs
    have hlin : 2+10*J.m≤14*b := by omega
    have h3 : b^3≤b^11007 := Nat.pow_le_pow_right hbpos (by decide)
    have hh : 2*b^11007≤b^11008 :=
      (Nat.mul_le_mul_right (b^11007) (show 2≤b by omega)).trans_eq (pow_succ' b 11007).symm
    omega
  exact hprune

end MinCostFlow.Scaling.Machine
