module

public import MinCostFlow.Final.ConnectedLinkedProgram
import MinCostFlow.IPM.Machine.ConnectedSolverCost
import MinCostFlow.IPM.Machine.TargetTestCost
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

/-- One scale covers the two solver dimensions and all augmented edge counts. -/
def ConnectedDataStructurePrograms.rateScale (P : ConnectedDataStructurePrograms) : ℝ :=
  7*(P.timeConstant:ℝ)+3

private theorem rateScale_ge_one (P : ConnectedDataStructurePrograms) : 1 ≤ P.rateScale := by
  unfold ConnectedDataStructurePrograms.rateScale
  linarith [Nat.cast_nonneg (α:=ℝ) P.timeConstant]

/-- Coefficient for the shared rate and logarithm bound. -/
def ConnectedDataStructurePrograms.rateCoefficient (P : ConnectedDataStructurePrograms) : ℝ :=
  1+435*logScale P.rateScale+max 0 P.forestConstant*(logScale P.rateScale)^P.forestLogDegree

/-- Exponent large enough for both subpolynomial rates and the forest logarithm. -/
def ConnectedDataStructurePrograms.rateExponent (P : ConnectedDataStructurePrograms) : ℝ :=
  (max 0 P.cycleConstant + max 0 P.qualityConstant) *
      (logScale P.rateScale)^(47/48:ℝ) * logScale (logScale P.rateScale) +
    (P.forestLogDegree+1:ℕ) / (Real.log 2)^(47/48:ℝ)

theorem ConnectedDataStructurePrograms.rateCoefficient_ge_one (P : ConnectedDataStructurePrograms) :
    1 ≤ P.rateCoefficient := by
  have h := logScale_one_le (rateScale_ge_one P)
  have hterm := mul_nonneg (le_max_left 0 P.forestConstant)
    (pow_nonneg (show 0≤logScale P.rateScale by linarith) P.forestLogDegree)
  unfold ConnectedDataStructurePrograms.rateCoefficient
  linarith

theorem ConnectedDataStructurePrograms.rateExponent_nonneg (P : ConnectedDataStructurePrograms) :
    0 ≤ P.rateExponent := by
  have h := logScale_one_le (rateScale_ge_one P)
  have hh := logScale_one_le h
  unfold ConnectedDataStructurePrograms.rateExponent
  positivity

private theorem rateEnvelope (P : ConnectedDataStructurePrograms) (m n j M : ℕ)
    (hn : n ≤ P.timeConstant*m) (hj : j ≤ P.timeConstant*m) (hM : M≤7*j) :
    let W := alg2TimeFactor P.rateExponent (47/48) m
    let H := P.rateCoefficient*W
    1 ≤ H ∧ 435*Real.log ((j:ℝ)+2) ≤ H ∧
    (P.resources.forestRate (n+1):ℝ) ≤ H ∧
    (((Finset.Icc j (7*j)).sup P.resources.cycleRate : ℕ):ℝ) ≤ H ∧
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
      unfold ConnectedDataStructurePrograms.rateExponent
      have h := div_le_div_of_nonneg_right (show (q:ℝ) ≤ (↑(P.forestLogDegree+1):ℝ) by exact_mod_cast hq)
        (Real.rpow_nonneg (Real.log_nonneg (show (1:ℝ)≤2 by norm_num)) (47/48:ℝ))
      have hp : 0 ≤ (max 0 P.cycleConstant + max 0 P.qualityConstant) *
          a^(47/48:ℝ)*logScale a := by positivity
      exact h.trans (le_add_of_nonneg_left hp)
    exact (paddedLog_pow_le_timeFactor q m).trans (scalingTimeFactor_mono hc m)
  have hscaled (i : ℕ) (hi : i≤7*(P.timeConstant*m)+1) : (i:ℝ)+2≤A*x := by
    have hi' : (i:ℝ)≤7*((P.timeConstant:ℝ)*m)+1 := by exact_mod_cast hi
    change (i:ℝ)+2≤(7*(P.timeConstant:ℝ)+3)*x
    dsimp only [x]
    nlinarith only [hi', Nat.cast_nonneg (α:=ℝ) P.timeConstant, Nat.cast_nonneg (α:=ℝ) m]
  have htime (B : ℝ) (hB : B≤max 0 P.cycleConstant+max 0 P.qualityConstant)
      (i : ℕ) (hi : i≤7*(P.timeConstant*m)+1) : alg2TimeFactor B (47/48) i≤W := by
    let b := max 0 P.cycleConstant+max 0 P.qualityConstant
    have hb : 0≤b := add_nonneg (le_max_left _ _) (le_max_left _ _)
    refine (scalingTimeFactor_mono hB i).trans
      ((scalingTimeFactor_rescale hA hb m i (hscaled i hi)).trans ?_)
    apply scalingTimeFactor_mono
    unfold ConnectedDataStructurePrograms.rateExponent
    exact le_add_of_nonneg_right (by positivity)
  have hj' : j≤7*(P.timeConstant*m)+1 := by omega
  have hn' : n+1≤7*(P.timeConstant*m)+1 := by omega
  have hjlog := log_le_scaled hA hx (by positivity) (hscaled j hj')
  have hnlog := log_le_scaled hA hx (by positivity) (hscaled (n+1) hn')
  have hcoef1 : 435*a≤P.rateCoefficient := by
    unfold ConnectedDataStructurePrograms.rateCoefficient
    have hp := mul_nonneg (le_max_left 0 P.forestConstant) (pow_nonneg (show 0≤a by linarith) P.forestLogDegree)
    linarith
  have hcoef2 : max 0 P.forestConstant*a^P.forestLogDegree≤P.rateCoefficient := by
    unfold ConnectedDataStructurePrograms.rateCoefficient
    linarith
  refine ⟨hH, ?_, ?_, ?_, ?_⟩
  · have hlog : Real.log x≤W := by
      have he : L≤W := by simpa only [pow_one] using hpadded 1 (by omega)
      dsimp [L] at he
      linarith
    calc
      _ ≤ 435*(a*Real.log x) := mul_le_mul_of_nonneg_left hjlog (by norm_num)
      _ = (435*a)*Real.log x := by ring
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
  · let s := Finset.Icc j (7*j)
    have hs : s.Nonempty := ⟨j, Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩⟩
    obtain ⟨i,hi,heq⟩ := Finset.exists_mem_eq_sup s hs P.resources.cycleRate
    obtain ⟨_,hi'⟩ := Finset.mem_Icc.mp hi
    change ((s.sup P.resources.cycleRate : ℕ):ℝ) ≤ H
    rw [heq]
    exact (P.cycleRate i).trans ((htime _ ((le_max_right _ _).trans
      (le_add_of_nonneg_right (le_max_left _ _))) i (by omega)).trans hW_H)
  · exact (P.quality M).trans ((htime _ ((le_max_right _ _).trans
      (le_add_of_nonneg_left (le_max_left _ _))) M (by omega)).trans hW_H)

private def widenedCostPolynomial (n m M b W epochs forest cycle quality : ℝ) : ℝ :=
  1000*n+100000*m*(W+3*b+3)+forest*(n+2+70*m)+
    (2+2*b)*(epochs*(M*(100000000*W^3)+(30*M+1)*cycle)+100*W+419)+50+2*quality

private theorem widenedCostPolynomial_mono
    {n m M b W d f c k n' m' M' b' W' d' f' c' k' : ℝ}
    (hn : 0≤n) (hm : 0≤m) (hM : 0≤M) (hb : 0≤b) (hW : 0≤W)
    (hd : 0≤d) (hf : 0≤f) (hc : 0≤c) (_hk : 0≤k)
    (hn' : n≤n') (hm' : m≤m') (hM' : M≤M') (hb' : b≤b') (hW' : W≤W')
    (hd' : d≤d') (hf' : f≤f') (hc' : c≤c') (hk' : k≤k') :
    widenedCostPolynomial n m M b W d f c k ≤ widenedCostPolynomial n' m' M' b' W' d' f' c' k' := by
  have hm₀ := hm.trans hm'
  have hf₀ := hf.trans hf'
  have hb₀ := hb.trans hb'
  have hd₀ := hd.trans hd'
  have hM₀ := hM.trans hM'
  unfold widenedCostPolynomial
  gcongr

private theorem widenedCostPolynomial_bound {x H : ℝ} (hx : 1≤x) (hH : 1≤H) :
    widenedCostPolynomial x x x H (30000116*H^2) (3276800000000001*H^5) H H (200*x) ≤
      10^50*x*H^12 := by
  have hx0 : 0≤x := by linarith
  have hH0 : 0≤H := by linarith
  have hp (a : ℕ) (ha : a≤12) : x*H^a≤x*H^12 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH ha) hx0
  have hp0 := hp 0 (by decide)
  have hp1 := hp 1 (by decide)
  have hp2 := hp 2 (by decide)
  have hp6 := hp 6 (by decide)
  have hp7 := hp 7 (by decide)
  have hp11 := hp 11 (by decide)
  have hpure (a : ℕ) (ha : a≤12) : H^a≤x*H^12 :=
    (pow_le_pow_right₀ hH ha).trans (le_mul_of_one_le_left (pow_nonneg hH0 _) hx)
  have hpure0 := hpure 0 (by decide)
  have hpure1 := hpure 1 (by decide)
  have hpure2 := hpure 2 (by decide)
  have hpure3 := hpure 3 (by decide)
  have hpure6 := hpure 6 (by decide)
  have hpure7 := hpure 7 (by decide)
  unfold widenedCostPolynomial
  nlinarith only [hp0,hp1,hp2,hp6,hp7,hp11,hpure0,hpure1,hpure2,hpure3,hpure6,hpure7,
    mul_nonneg hx0 (pow_nonneg hH0 12)]

private theorem widenedSolver_bound_positive (r : SolverRuntimeResources) (n m : ℕ)
    (hm : 0<m) (x H : ℝ) (hx : 1≤x) (hH : 1≤H)
    (hn : (n:ℝ)≤x) (he : (m:ℝ)≤x) (hAug : ∀ M∈Finset.Icc m (7*m), (M:ℝ)≤x)
    (hB : 435*Real.log ((m:ℝ)+2)≤H)
    (hF : (r.template.forestRate (n+1):ℝ)≤H)
    (hR : ∀ M∈Finset.Icc m (7*m), (r.template.cycleRate M:ℝ)≤H)
    (hK : ∀ M∈Finset.Icc m (7*m), (2:ℝ)^r.qualityExponent M≤H)
    (hC : ∀ M∈Finset.Icc m (7*m), (r.qualityCost M:ℝ)≤200*x) :
    (connectedSolverRuntimeTime r n m:ℝ) ≤ 10^50*x*H^12 := by
  obtain ⟨M,hMem,hCost⟩ := connectedSolverRuntimeTime_width_bound r n m hm
  obtain ⟨hSmall,hLarge⟩ := Finset.mem_Icc.mp hMem
  obtain ⟨hSize,hBits⟩ := connectedSolverInputBits_log_bound m M hm hSmall hLarge
  let V := solverPenalty m
  let B := M.size+V.size
  let k := r.qualityExponent M
  let W := 30000000*B^2+116*k
  let D := targetTestLimit M V k
  have hb : (B:ℝ)≤H := hBits.trans hB
  have hk : (k:ℝ)≤H := by
    have hk' : (k:ℝ)≤(2:ℝ)^k := by exact_mod_cast (Nat.lt_two_pow_self (n:=k)).le
    exact hk'.trans (hK M hMem)
  have hW : (W:ℝ)≤30000116*H^2 := by
    have hSq := pow_le_pow_left₀ (Nat.cast_nonneg B) hb 2
    have hH2 : H≤H^2 := by nlinarith only [hH,sq_nonneg (H-1)]
    unfold W
    push_cast
    linarith only [hSq,hk,hH2]
  have hd : (D:ℝ)≤3276800000000001*H^5 := by
    have hLimit := targetTest_limit_bit_bound M V k hSize
    change (D:ℝ)≤3276800000000001*(B:ℝ)^3*((2:ℝ)^k)^2 at hLimit
    refine hLimit.trans ?_
    rw [show (5:ℕ) = 3+2 by decide,pow_add,←mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg B) hb 3) (by norm_num))
      (pow_le_pow_left₀ (by positivity) (hK M hMem) 2) (by positivity) (by positivity)
  have hCast : (connectedSolverRuntimeTime r n m:ℝ) ≤ widenedCostPolynomial n m M B W D
      (r.template.forestRate (n+1)) (r.template.cycleRate M) (r.qualityCost M) := by
    unfold widenedCostPolynomial
    exact_mod_cast hCost
  refine hCast.trans ((widenedCostPolynomial_mono (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hn he (hAug M hMem)
    hb hW hd hF (hR M hMem) (hC M hMem)).trans (widenedCostPolynomial_bound hx hH))

private theorem widenedSolver_zero (r : SolverRuntimeResources) (n : ℕ) :
    connectedSolverRuntimeTime r n 0 ≤
      (connectedSolverTimeAt (r.forSize 0) 0 0 0+2*r.qualityCost 0+1000)*(n+2)*(r.template.forestRate (n+1)+1) := by
  have hIcc : Finset.Icc (0:ℕ) (7*0) = {0} := by ext x; simp
  unfold connectedSolverRuntimeTime
  rw [hIcc, Finset.sup_singleton]
  let E := connectedSolverTimeAt (r.forSize 0) 0 0 0+2*r.qualityCost 0
  let f := r.template.forestRate (n+1)
  have hBase : connectedSolverTimeAt (r.forSize 0) n 0 0 + 2*r.qualityCost 0 ≤ E+930*n+f*(n+2) := by
    simp only [E, f, connectedSolverTimeAt, roundMachineCost, Nat.zero_mul, Nat.mul_zero,
      Nat.zero_add, Nat.add_zero, SolverRuntimeResources.forSize]
    rw [show n+1+1=n+2 by rfl]
    omega
  have hE : E+930*n≤(E+1000)*(n+2) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    simp only [Nat.mul_comm 930, Nat.mul_comm 1000]
    have hn := Nat.mul_le_mul_left n (show 930≤1000 by decide)
    omega
  have hF : f*(n+2)≤(E+1000)*(n+2)*f := by
    rw [Nat.mul_comm f]
    have h := Nat.mul_le_mul_right ((n+2)*f) (show 1≤E+1000 by omega)
    simpa only [Nat.one_mul,←Nat.mul_assoc] using h
  have hfixed : 30≤(E+1000)*(n+2) :=
    (by omega : 30≤E+1000).trans (Nat.le_mul_of_pos_right _ (by omega))
  change max 30 _≤(E+1000)*(n+2)*(f+1)
  rw [Nat.mul_add, Nat.mul_one]
  exact max_le (hfixed.trans (Nat.le_add_left _ _))
    (hBase.trans (by linarith [hE,hF]))

/-- The coefficient in the edge-linear bound, including the empty input case. -/
def ConnectedDataStructurePrograms.solverRateCoefficient (P : ConnectedDataStructurePrograms) : ℝ :=
  let r := P.runtimeResources
  (10^50+2*((connectedSolverTimeAt (r.forSize 0) 0 0 0:ℝ)+2*r.qualityCost 0+1000))*
    P.rateScale*P.rateCoefficient^12

theorem ConnectedDataStructurePrograms.solverRateCoefficient_pos (P : ConnectedDataStructurePrograms) :
    0<P.solverRateCoefficient := by
  have hScale := rateScale_ge_one P
  have hCoeff := P.rateCoefficient_ge_one
  unfold ConnectedDataStructurePrograms.solverRateCoefficient
  positivity

private theorem widenedRuntimeTime_le (P : ConnectedDataStructurePrograms) (m n j : ℕ)
    (hn : n≤P.timeConstant*m) (hj : j≤P.timeConstant*m) :
    (connectedSolverRuntimeTime P.runtimeResources n j:ℝ) ≤
      P.solverRateCoefficient*((m:ℝ)+2)*alg2TimeFactor (12*P.rateExponent) (47/48) m := by
  let r := P.runtimeResources
  let x := (m:ℝ)+2
  let X := P.rateScale*x
  let W := alg2TimeFactor P.rateExponent (47/48) m
  let H := P.rateCoefficient*W
  let E := (connectedSolverTimeAt (r.forSize 0) 0 0 0:ℝ)+2*r.qualityCost 0+1000
  have hx : (2:ℝ)≤x := by dsimp [x]; linarith [Nat.cast_nonneg (α:=ℝ) m]
  have hScale := rateScale_ge_one P
  have hX : 1≤X := le_trans (by linarith : (1:ℝ)≤x) (le_mul_of_one_le_left (by linarith) hScale)
  have hs (a : ℕ) (ha : a≤7*(P.timeConstant*m)) : (a:ℝ)+2≤X := by
    have ha' : (a:ℝ)≤7*((P.timeConstant:ℝ)*m) := by exact_mod_cast ha
    unfold X x ConnectedDataStructurePrograms.rateScale
    nlinarith only [ha',Nat.cast_nonneg (α:=ℝ) m,Nat.cast_nonneg (α:=ℝ) P.timeConstant]
  have hn' : (n:ℝ)+2≤X := hs n (by omega)
  have hj' : (j:ℝ)+2≤X := hs j (by omega)
  have ⟨hH,hB,hF,hR,_⟩ := rateEnvelope P m n j 0 hn hj (by omega)
  have hE : 0≤E := by
    exact add_nonneg (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
      (by norm_num)
  have hWork : (connectedSolverRuntimeTime r n j:ℝ) ≤ (10^50+2*E)*X*H^12 := by
    by_cases hzero : j=0
    · subst j
      have hz := widenedSolver_zero r n
      have hz' : (connectedSolverRuntimeTime r n 0:ℝ)≤E*(n+2)*((r.template.forestRate (n+1):ℝ)+1) := by
        unfold E
        exact_mod_cast hz
      have hH12 : H≤H^12 := by
        simpa only [pow_one] using pow_le_pow_right₀ hH (show 1≤12 by decide)
      have hF' : (r.template.forestRate (n+1):ℝ)+1≤2*H^12 := by
        change (r.template.forestRate (n+1):ℝ)≤H at hF
        linarith only [hH,hF,hH12]
      refine hz'.trans ?_
      calc
        _ ≤ E*X*(2*H^12) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hn' hE) hF'
          · positivity
          · exact mul_nonneg hE (by linarith)
        _ ≤ _ := by
          have hNum := mul_nonneg (by linarith : 0≤X) (pow_nonneg (show 0≤H by linarith) 12)
          nlinarith only [hNum]
    · have hp := widenedSolver_bound_positive r n j (Nat.pos_of_ne_zero hzero) X H hX hH
        (by linarith only [hn']) (by linarith only [hj'])
        (fun M hM => by
          have hm' := hs M ((Finset.mem_Icc.mp hM).2.trans (Nat.mul_le_mul_left 7 hj))
          linarith only [hm'])
        hB hF
        (fun M hM => (show (r.template.cycleRate M:ℝ) ≤
          ((Finset.Icc j (7*j)).sup P.resources.cycleRate:ℕ) by
          exact_mod_cast Finset.le_sup (f := P.resources.cycleRate) hM).trans hR)
        (fun M hM => (rateEnvelope P m n j M hn hj (Finset.mem_Icc.mp hM).2).2.2.2.2)
        (fun M hM => by
          have hm' := hs M ((Finset.mem_Icc.mp hM).2.trans (Nat.mul_le_mul_left 7 hj))
          have hq : (r.qualityCost M:ℝ)≤100*((M:ℝ)+1) := by
            change (integerQualityCost M:ℝ)≤_
            exact_mod_cast integerQualityCost_le M
          linarith only [hm',hq,hX])
      exact hp.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (mul_nonneg (by norm_num) hE)) (by linarith)) (pow_nonneg (by linarith) _))
  refine hWork.trans_eq ?_
  change (10^50+2*E)*X*H^12 =
    (10^50+2*E)*P.rateScale*P.rateCoefficient^12*x*alg2TimeFactor (12*P.rateExponent) (47/48) m
  dsimp only [X,H,x]
  rw [mul_pow, scalingTimeFactor_pow]
  simp only [show (↑(12:ℕ):ℝ)=12 from rfl]
  ring

/-- The maximum over the dimensions used by scaling keeps the same
edge-linear bound with a subpolynomial factor. -/
theorem ConnectedDataStructurePrograms.linkedSolverTime_le (P : ConnectedDataStructurePrograms)
    (m N M : ℕ) (hN : N≤P.timeConstant*m) (hM : M≤P.timeConstant*m) :
    (linkedConnectedSolverTime P.runtimeResources N M:ℝ) ≤
      P.solverRateCoefficient*((m:ℝ)+2)*alg2TimeFactor (12*P.rateExponent) (47/48) m := by
  let rect := Finset.range (N+1) ×ˢ Finset.range (M+1)
  have hne : rect.Nonempty := ⟨(N,M), by simp [rect]⟩
  obtain ⟨⟨n,j⟩,hmem,hmax⟩ := Finset.exists_mem_eq_sup rect hne
    (fun nm => connectedSolverRuntimeTime P.runtimeResources nm.1 nm.2)
  have hnm : n≤N ∧ j≤M := by simpa [rect, Nat.lt_succ_iff] using hmem
  change linkedConnectedSolverTime P.runtimeResources N M =
    connectedSolverRuntimeTime P.runtimeResources n j at hmax
  rw [hmax]
  exact widenedRuntimeTime_le P m n j (hnm.1.trans hN) (hnm.2.trans hM)

end MinCostFlow.Final
