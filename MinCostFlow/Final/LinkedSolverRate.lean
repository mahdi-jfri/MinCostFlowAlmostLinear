module

public import MinCostFlow.Final.LinkedProgram
public import MinCostFlow.Final.TimeFactorBounds
import MinCostFlow.IPM.Machine.RoundMachine
import Mathlib.Tactic

/-!
# Bounding linked solver costs by the supplied rates

Both dimensions in the solver comparison are at most a constant times
the original edge count. The forest and cycle charges and the quality
factor can therefore be bounded using that same edge count.
-/

public noncomputable section
namespace MinCostFlow.Final
open IPM.Machine Chain

/-- The zero-edge part of the advertised IPM cost is linear in the
vertex count up to its forest rate and a fixed setup constant. -/
theorem solverTime_zero_edge_bound (r : SolverResources) (n : ℕ) :
    solverTime r n 0 ≤ (solverTimeAt r 0 0 0 + 500)*(n+2)*(r.forestRate (n+1)+1) := by
  have hIcc : Finset.Icc (0:ℕ) (3*0) = {0} := by ext x; simp
  unfold solverTime
  rw [hIcc, Finset.sup_singleton]
  have hbase : solverTimeAt r n 0 0 ≤
      solverTimeAt r 0 0 0 + 430*n + r.forestRate (n+1)*(n+2) := by
    simp only [solverTimeAt, roundMachineCost, Nat.zero_mul, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    rw [show n+1+1=n+2 by rfl]
    omega
  have hconst : solverTimeAt r 0 0 0 + 430*n ≤ (solverTimeAt r 0 0 0 + 500)*(n+2) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    simp only [Nat.mul_comm 430, Nat.mul_comm 500]
    have hn := Nat.mul_le_mul_left n (show 430≤500 by decide)
    omega
  have hb : 1 ≤ solverTimeAt r 0 0 0 + 500 := by omega
  have hrate := Nat.mul_le_mul_right ((n+2)*r.forestRate (n+1)) hb
  rw [Nat.one_mul, ←Nat.mul_assoc] at hrate
  have hfixed : 30 ≤ (solverTimeAt r 0 0 0 + 500)*(n+2) := by
    exact (by omega : 30 ≤ solverTimeAt r 0 0 0 + 500).trans
      (Nat.le_mul_of_pos_right _ (by omega))
  rw [Nat.mul_add, Nat.mul_one]
  exact max_le (hfixed.trans (Nat.le_add_left _ _)) (hbase.trans (by
    rw [Nat.mul_comm (r.forestRate (n+1)) (n+2)]
    omega))

private def solverPolynomialCost (n m b forest cycle quality : ℝ) : ℝ :=
  500*n+100000*m*(30000000*b^2+3*b+3)+forest*(n+2+30*m)+
    (2+2*b)*(3276800000000001*b^3*quality^2*
      ((3*m)*(100000000*(30000000*b^2)^3)+(90*m+1)*cycle)+3000000000*b^2+419)+30

private theorem solverPolynomialCost_mono
    {n m b f c k N M B F C K : ℝ}
    (hn : 0≤n) (hm : 0≤m) (hb : 0≤b) (hf : 0≤f) (hc : 0≤c) (hk : 0≤k)
    (hN : n≤N) (hM : m≤M) (hB : b≤B) (hF : f≤F) (hC : c≤C) (hK : k≤K) :
    solverPolynomialCost n m b f c k ≤ solverPolynomialCost N M B F C K := by
  unfold solverPolynomialCost
  have hM0 := hm.trans hM
  have hB0 := hb.trans hB
  have hF0 := hf.trans hF
  have hK0 := hk.trans hK
  gcongr

private theorem solverPolynomialCost_bound {x H : ℝ} (hx : 1≤x) (hH : 1≤H) :
    solverPolynomialCost x x H H H H ≤ 10^48*x*H^12 := by
  have hx0 : 0≤x := by linarith
  have hH0 : 0≤H := by linarith
  have hpow (a b : ℕ) (hab : a≤b) : H^a≤H^b := pow_le_pow_right₀ hH hab
  have h0 : (1:ℝ) ≤ H^12 := by simpa only [pow_zero] using hpow 0 12 (by decide)
  have h1 : H ≤ H^12 := by simpa only [pow_one] using hpow 1 12 (by decide)
  have h2 : H^2 ≤ H^12 := hpow 2 12 (by decide)
  have h3 : H^3 ≤ H^12 := hpow 3 12 (by decide)
  have h6 : H^6 ≤ H^12 := hpow 6 12 (by decide)
  have h7 : H^7 ≤ H^12 := hpow 7 12 (by decide)
  have h11 : H^11 ≤ H^12 := hpow 11 12 (by decide)
  have le_all {y : ℝ} (hy : y ≤ H^12) : y ≤ x*H^12 :=
    hy.trans (le_mul_of_one_le_left (by positivity) hx)
  unfold solverPolynomialCost
  nlinarith only [le_all h0, le_all h1, le_all h2, le_all h3, le_all h6, le_all h7,
    mul_le_mul_of_nonneg_left h0 hx0, mul_le_mul_of_nonneg_left h1 hx0,
    mul_le_mul_of_nonneg_left h2 hx0, mul_le_mul_of_nonneg_left h6 hx0,
    mul_le_mul_of_nonneg_left h7 hx0, mul_le_mul_of_nonneg_left h11 hx0]

/-- The positive-edge formula is dominated by a single polynomial in
a common rate bound once it also bounds the logarithmic coefficient. -/
theorem linkedSolverLogCost_positive_bound (r : SolverResources) (n m : ℕ) (hm : 0<m)
    (x H : ℝ) (hx : 1≤x) (hH : 1≤H) (hn : (n:ℝ)≤x) (he : (m:ℝ)≤x)
    (hb : 430*Real.log ((m:ℝ)+2)≤H) (hF : (r.forestRate (n+1):ℝ)≤H)
    (hC : (((Finset.Icc m (3*m)).sup r.cycleRate : ℕ) : ℝ)≤H)
    (hK : (2:ℝ)^r.qualityExponent≤H) :
    linkedSolverLogCost r n m ≤ 10^48*x*H^12 := by
  have hlog : 0≤430*Real.log ((m:ℝ)+2) := by
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) m]))
  rw [linkedSolverLogCost, ite_eq_right (Nat.ne_of_gt hm)]
  refine le_trans ?_ (solverPolynomialCost_bound hx hH)
  exact solverPolynomialCost_mono (Nat.cast_nonneg n) (Nat.cast_nonneg m) hlog
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by positivity) hn he hb hF hC hK


/-- One scale covers the two solver dimensions and all augmented edge counts. -/
def DataStructurePrograms.rateScale (P : DataStructurePrograms) : ℝ :=
  3*(P.timeConstant:ℝ)+3

private theorem rateScale_ge_one (P : DataStructurePrograms) : 1 ≤ P.rateScale := by
  unfold DataStructurePrograms.rateScale
  linarith [Nat.cast_nonneg (α:=ℝ) P.timeConstant]

/-- Coefficient for the shared rate and logarithm bound. -/
def DataStructurePrograms.rateCoefficient (P : DataStructurePrograms) : ℝ :=
  1+430*logScale P.rateScale+max 0 P.forestConstant*(logScale P.rateScale)^P.forestLogDegree

/-- Exponent large enough for both subpolynomial rates and the forest logarithm. -/
def DataStructurePrograms.rateExponent (P : DataStructurePrograms) : ℝ :=
  (max 0 P.cycleConstant + max 0 P.qualityConstant) *
      (logScale P.rateScale)^(47/48:ℝ) * logScale (logScale P.rateScale) +
    (P.forestLogDegree+1:ℕ) / (Real.log 2)^(47/48:ℝ)

theorem DataStructurePrograms.rateCoefficient_ge_one (P : DataStructurePrograms) :
    1 ≤ P.rateCoefficient := by
  have h := logScale_one_le (rateScale_ge_one P)
  have hterm := mul_nonneg (le_max_left 0 P.forestConstant)
    (pow_nonneg (show 0≤logScale P.rateScale by linarith) P.forestLogDegree)
  unfold DataStructurePrograms.rateCoefficient
  linarith

theorem DataStructurePrograms.rateExponent_nonneg (P : DataStructurePrograms) :
    0 ≤ P.rateExponent := by
  have h := logScale_one_le (rateScale_ge_one P)
  have hh := logScale_one_le h
  unfold DataStructurePrograms.rateExponent
  positivity

private theorem rateEnvelope (P : DataStructurePrograms) (m n j M : ℕ)
    (hn : n ≤ P.timeConstant*m) (hj : j ≤ P.timeConstant*m) (hM : M≤3*j) :
    let W := alg2TimeFactor P.rateExponent (47/48) m
    let H := P.rateCoefficient*W
    1 ≤ H ∧ 430*Real.log ((j:ℝ)+2) ≤ H ∧
    (P.resources.forestRate (n+1):ℝ) ≤ H ∧
    (((Finset.Icc j (3*j)).sup P.resources.cycleRate : ℕ):ℝ) ≤ H ∧
    (2:ℝ)^P.runtimeResources.qualityExponent M ≤ H := by
  dsimp only
  let A := P.rateScale
  let a := logScale A
  let x := (m:ℝ)+2
  let L := Real.log x+2
  let W := alg2TimeFactor P.rateExponent (47/48) m
  let H := P.rateCoefficient*W
  have hA : 1≤A := rateScale_ge_one P
  have ha : 1≤a := logScale_one_le hA
  have haa : 1≤logScale a := logScale_one_le ha
  have hx : 2≤x := by dsimp [x]; linarith [Nat.cast_nonneg (α:=ℝ) m]
  have hL : 1≤L := by
    have h := Real.log_nonneg (show 1≤x by linarith)
    dsimp [L]; linarith
  have hW : 1≤W := scalingTimeFactor_one_le P.rateExponent_nonneg m
  have hH : 1≤H := by
    exact one_le_mul_of_one_le_of_one_le P.rateCoefficient_ge_one hW
  have hW_H : W≤H := le_mul_of_one_le_left (by linarith) P.rateCoefficient_ge_one
  have hpadded (q : ℕ) (hq : q≤P.forestLogDegree+1) : L^q≤W := by
    have hc : (q:ℝ) / (Real.log 2)^(47/48:ℝ) ≤ P.rateExponent := by
      unfold DataStructurePrograms.rateExponent
      have h := div_le_div_of_nonneg_right (show (q:ℝ) ≤ (↑(P.forestLogDegree+1):ℝ) by exact_mod_cast hq)
        (Real.rpow_nonneg (Real.log_nonneg (show (1:ℝ)≤2 by norm_num)) (47/48:ℝ))
      have hp : 0 ≤ (max 0 P.cycleConstant + max 0 P.qualityConstant) *
          a^(47/48:ℝ)*logScale a := by positivity
      exact h.trans (le_add_of_nonneg_left hp)
    exact (paddedLog_pow_le_timeFactor q m).trans (scalingTimeFactor_mono hc m)
  have hscaled (i : ℕ) (hi : i≤3*(P.timeConstant*m)+1) : (i:ℝ)+2≤A*x := by
    have hi' : (i:ℝ)≤3*((P.timeConstant:ℝ)*m)+1 := by exact_mod_cast hi
    change (i:ℝ)+2≤(3*(P.timeConstant:ℝ)+3)*x
    dsimp only [x]
    nlinarith only [hi', Nat.cast_nonneg (α:=ℝ) P.timeConstant, Nat.cast_nonneg (α:=ℝ) m]
  have htime (B : ℝ) (hB : B≤max 0 P.cycleConstant+max 0 P.qualityConstant)
      (i : ℕ) (hi : i≤3*(P.timeConstant*m)+1) : alg2TimeFactor B (47/48) i≤W := by
    let b := max 0 P.cycleConstant+max 0 P.qualityConstant
    have hb : 0≤b := add_nonneg (le_max_left _ _) (le_max_left _ _)
    refine (scalingTimeFactor_mono hB i).trans
      ((scalingTimeFactor_rescale hA hb m i (hscaled i hi)).trans ?_)
    apply scalingTimeFactor_mono
    unfold DataStructurePrograms.rateExponent
    exact le_add_of_nonneg_right (by positivity)
  have hj' : j≤3*(P.timeConstant*m)+1 := by omega
  have hn' : n+1≤3*(P.timeConstant*m)+1 := by omega
  have hjlog := log_le_scaled hA hx (by positivity) (hscaled j hj')
  have hnlog := log_le_scaled hA hx (by positivity) (hscaled (n+1) hn')
  have hcoef1 : 430*a≤P.rateCoefficient := by
    unfold DataStructurePrograms.rateCoefficient
    have hp := mul_nonneg (le_max_left 0 P.forestConstant) (pow_nonneg (show 0≤a by linarith) P.forestLogDegree)
    linarith
  have hcoef2 : max 0 P.forestConstant*a^P.forestLogDegree≤P.rateCoefficient := by
    unfold DataStructurePrograms.rateCoefficient
    linarith
  refine ⟨hH, ?_, ?_, ?_, ?_⟩
  · have hlog : Real.log x≤W := by
      have he : L≤W := by simpa only [pow_one] using hpadded 1 (by omega)
      dsimp [L] at he
      linarith
    calc
      _ ≤ 430*(a*Real.log x) := mul_le_mul_of_nonneg_left hjlog (by norm_num)
      _ = (430*a)*Real.log x := by ring
      _ ≤ H := mul_le_mul hcoef1 hlog (Real.log_nonneg (by linarith)) (by linarith [P.rateCoefficient_ge_one])
  · have hnLog : Real.log ((↑(n+1):ℝ)+2) ≤ a*L := hnlog.trans (by
      unfold L
      have h := mul_nonneg (show 0≤a by linarith) (show (0:ℝ)≤2 by norm_num)
      rw [mul_add]
      linarith)
    have hpow : Real.log ((↑(n+1):ℝ)+2)^P.forestLogDegree ≤
        a^P.forestLogDegree*L^P.forestLogDegree := by
      rw [←mul_pow]
      exact pow_le_pow_left₀ (Real.log_nonneg (by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) n])) hnLog _
    calc
      _ ≤ P.forestConstant * Real.log ((↑(n+1):ℝ)+2)^P.forestLogDegree := P.forestRate (n+1)
      _ ≤ max 0 P.forestConstant * (a^P.forestLogDegree*L^P.forestLogDegree) :=
        mul_le_mul (le_max_right _ _) hpow (pow_nonneg (Real.log_nonneg (by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) n])) _) (le_max_left _ _)
      _ = (max 0 P.forestConstant*a^P.forestLogDegree)*L^P.forestLogDegree := by ring
      _ ≤ H := mul_le_mul hcoef2 (hpadded _ (by omega)) (pow_nonneg (by linarith) _) (by linarith [P.rateCoefficient_ge_one])
  · let s := Finset.Icc j (3*j)
    have hs : s.Nonempty := ⟨j, Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩⟩
    obtain ⟨i,hi,heq⟩ := Finset.exists_mem_eq_sup s hs P.resources.cycleRate
    obtain ⟨_,hi'⟩ := Finset.mem_Icc.mp hi
    change ((s.sup P.resources.cycleRate : ℕ):ℝ) ≤ H
    rw [heq]
    exact (P.cycleRate i).trans ((htime _ ((le_max_right _ _).trans
      (le_add_of_nonneg_right (le_max_left _ _))) i (by omega)).trans hW_H)
  · exact (P.quality M).trans ((htime _ ((le_max_right _ _).trans
      (le_add_of_nonneg_left (le_max_left _ _))) M (by omega)).trans hW_H)

/-- The fixed coefficient in the edge-linear linked solver estimate. -/
def DataStructurePrograms.solverRateCoefficient (P : DataStructurePrograms) : ℝ :=
  (10^48+2*((solverTimeAt (P.runtimeResources.forSize 0) 0 0 0:ℝ)+500)+100)*P.rateScale*P.rateCoefficient^12

theorem DataStructurePrograms.solverRateCoefficient_pos (P : DataStructurePrograms) :
    0 < P.solverRateCoefficient := by
  have hA := rateScale_ge_one P
  have hC := P.rateCoefficient_ge_one
  unfold DataStructurePrograms.solverRateCoefficient
  positivity

/-- Every pair in the compressed comparison rectangle has an edge-linear
solver bound times the explicit subpolynomial factor. -/
theorem DataStructurePrograms.linkedSolverLogCost_le (P : DataStructurePrograms) (m n j M : ℕ)
    (hn : n ≤ P.timeConstant*m) (hj : j ≤ P.timeConstant*m) (hM : M ≤ 3*j) :
    linkedRuntimeLogCost P.runtimeResources n j M ≤ P.solverRateCoefficient*((m:ℝ)+2)*
      alg2TimeFactor (12*P.rateExponent) (47/48) m := by
  let x := (m:ℝ)+2
  let W := alg2TimeFactor P.rateExponent (47/48) m
  let H := P.rateCoefficient*W
  let y := P.rateScale*x
  let E := (solverTimeAt (P.runtimeResources.forSize 0) 0 0 0:ℝ)+500
  obtain ⟨hH,hb,hF,hC,hK⟩ := rateEnvelope P m n j M hn hj hM
  change 1≤H at hH
  change (P.resources.forestRate (n+1):ℝ)≤H at hF
  have hn' : (n:ℝ) ≤ (P.timeConstant:ℝ)*m := by exact_mod_cast hn
  have hj' : (j:ℝ) ≤ (P.timeConstant:ℝ)*m := by exact_mod_cast hj
  have hA := rateScale_ge_one P
  have hx : 2≤x := by dsimp [x]; linarith [Nat.cast_nonneg (α:=ℝ) m]
  have hy : 1≤y := by
    have h := one_le_mul_of_one_le_of_one_le hA (show 1≤x by linarith)
    exact h
  have hny : (n:ℝ)+2≤y := by
    change _ ≤ (3*(P.timeConstant:ℝ)+3)*((m:ℝ)+2)
    nlinarith only [hn', Nat.cast_nonneg (α:=ℝ) P.timeConstant, Nat.cast_nonneg (α:=ℝ) m,
      mul_nonneg (Nat.cast_nonneg (α:=ℝ) P.timeConstant) (Nat.cast_nonneg (α:=ℝ) m)]
  have hjy : (j:ℝ)≤y := by
    change _ ≤ (3*(P.timeConstant:ℝ)+3)*((m:ℝ)+2)
    nlinarith only [hj', Nat.cast_nonneg (α:=ℝ) P.timeConstant, Nat.cast_nonneg (α:=ℝ) m,
      mul_nonneg (Nat.cast_nonneg (α:=ℝ) P.timeConstant) (Nat.cast_nonneg (α:=ℝ) m)]
  have hE : 0≤E := by dsimp [E]; positivity
  have hbound : linkedSolverLogCost (P.runtimeResources.forSize M) n j ≤ (10^48+2*E)*y*H^12 := by
    by_cases hz : j=0
    · subst j
      have hMz : M = 0 := by omega
      subst M
      rw [linkedSolverLogCost, ite_eq_left rfl]
      have hz : (solverTime (P.runtimeResources.forSize 0) n 0:ℝ) ≤ E*((n:ℝ)+2)*((P.resources.forestRate (n+1):ℝ)+1) := by
        dsimp [E]
        exact_mod_cast solverTime_zero_edge_bound (P.runtimeResources.forSize 0) n
      have hHpow : H≤H^12 := by simpa only [pow_one] using pow_le_pow_right₀ hH (show 1≤12 by decide)
      calc
        _ ≤ E*((n:ℝ)+2)*((P.resources.forestRate (n+1):ℝ)+1) := hz
        _ ≤ (E*y)*(2*H^12) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hny hE)
          · linarith
          · positivity
          · exact mul_nonneg hE (by linarith)
        _ = (2*E)*y*H^12 := by ring
        _ ≤ _ := by gcongr; linarith
    · have h := linkedSolverLogCost_positive_bound (P.runtimeResources.forSize M) n j (Nat.pos_of_ne_zero hz)
        y H hy hH (by linarith) hjy hb hF hC hK
      exact h.trans (by gcongr; linarith)
  have hQualitySize : (M:ℝ)+1 ≤ y := by
    have hM' : (M:ℝ) ≤ 3*(j:ℝ) := by exact_mod_cast hM
    change _ ≤ (3*(P.timeConstant:ℝ)+3)*((m:ℝ)+2)
    nlinarith only [hM',hj',Nat.cast_nonneg (α:=ℝ) P.timeConstant,Nat.cast_nonneg (α:=ℝ) m]
  have hCost : (P.runtimeResources.qualityCost M:ℝ) ≤ 100*y*H^12 := by
    have hLocal : (P.runtimeResources.qualityCost M:ℝ) ≤ 100*((M:ℝ)+1) := by
      change (integerQualityCost M:ℝ) ≤ _
      exact_mod_cast integerQualityCost_le M
    refine hLocal.trans ((mul_le_mul_of_nonneg_left hQualitySize (by norm_num)).trans ?_)
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hH)
  have hTotal : linkedRuntimeLogCost P.runtimeResources n j M ≤ (10^48+2*E+100)*y*H^12 := by
    unfold linkedRuntimeLogCost
    exact (add_le_add hbound hCost).trans_eq (by ring)
  have hw : W^12 = alg2TimeFactor (12*P.rateExponent) (47/48) m := by
    simpa only [Nat.cast_ofNat] using scalingTimeFactor_pow P.rateExponent 12 m
  calc
    _ ≤ (10^48+2*E+100)*y*H^12 := hTotal
    _ = P.solverRateCoefficient*x*W^12 := by
      dsimp only [DataStructurePrograms.solverRateCoefficient, E, y, H]
      rw [mul_pow]
      ring
    _ = _ := by rw [hw]

end MinCostFlow.Final
