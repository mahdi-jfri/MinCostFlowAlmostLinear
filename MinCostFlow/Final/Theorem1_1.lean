module

public import MinCostFlow.Final.LinkedSolverRate
public import MinCostFlow.Final.WidenedSolverRate
public import MinCostFlow.Final.ConnectedSolverRate
public import MinCostFlow.Final.ConcreteSolverRate
public import MinCostFlow.Final.ForestConcreteSolverRate
public import MinCostFlow.Statement.Main
import Mathlib.Tactic

/-!
# Theorem 1.1 from the two data structure programs

The linked scaling program gives an exact answer. The two edge
logarithms are absorbed into the subpolynomial solver factor, leaving
one logarithm each for capacities and costs and a linear vertex term.
-/

public noncomputable section
namespace MinCostFlow.Final
open Chain WordRAM Filter Topology

private def binaryLogCoefficient : ℝ := 3 / Real.log 2

private theorem binaryLogCoefficient_pos : 0 < binaryLogCoefficient :=
  div_pos (by norm_num) (Real.log_pos (by norm_num))

private theorem padded_clog_le (m : ℕ) :
    (Nat.clog 2 (m+2):ℝ)+1 ≤ binaryLogCoefficient*Real.log ((m:ℝ)+2) := by
  let k := Nat.clog 2 (m+2)
  let x := (m:ℝ)+2
  have hx : 2≤x := by dsimp [x]; linarith [Nat.cast_nonneg (α:=ℝ) m]
  have hlog : Real.log 2≤Real.log x := Real.log_le_log (by norm_num) hx
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hk : 0<k := Nat.clog_pos (by decide) (by omega)
  have he : k.pred+1=k := Nat.succ_pred_eq_of_pos hk
  have h := Nat.pow_pred_clog_lt_self (by decide : 1<2) (by omega : 1<m+2)
  have hcast : (2:ℝ)^k.pred<x := by
    dsimp only [k,x]
    exact_mod_cast h
  have hp := (Real.log_lt_log (by positivity) hcast).le
  rw [Real.log_pow] at hp
  have hcast' : (k.pred:ℝ)+1=k := by exact_mod_cast he
  change (k:ℝ)+1 ≤ (3 / Real.log 2)*Real.log x
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hl).mpr
  rw [←hcast']
  linarith only [hp,hlog]

private theorem padded_clog_succ_le (m : ℕ) :
    (Nat.clog 2 (m+1):ℝ)+1 ≤ binaryLogCoefficient*Real.log ((m:ℝ)+2) := by
  have h : Nat.clog 2 (m+1) ≤ Nat.clog 2 (m+2) := Nat.clog_mono_right 2 (by omega)
  exact (add_le_add_left (by exact_mod_cast h) 1).trans (padded_clog_le m)

private def scalingLogCoefficient : ℝ := 2*binaryLogCoefficient^3 / Real.log 2

private theorem scalingLogCoefficient_pos : 0 < scalingLogCoefficient := by
  unfold scalingLogCoefficient
  exact div_pos (mul_pos (by norm_num) (pow_pos binaryLogCoefficient_pos _))
    (Real.log_pos (by norm_num))

private theorem scalingLogs_le (m U C : ℕ) :
    ((Nat.clog 2 (m+1)+1)*(Nat.clog 2 (m+1)+Nat.clog 2 (U+1)+1)*Nat.clog 2 (C+2):ℕ) ≤
      scalingLogCoefficient*(Real.log ((m:ℝ)+2))^2*
        Real.log ((U:ℝ)+2)*Real.log ((C:ℝ)+2) := by
  let l := Real.log 2
  let x := Real.log ((m:ℝ)+2)
  let y := Real.log ((U:ℝ)+2)
  let z := Real.log ((C:ℝ)+2)
  let B := binaryLogCoefficient
  have hl : 0<l := Real.log_pos (by norm_num)
  have hx : l≤x := Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) m])
  have hy : l≤y := Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) U])
  have hz : l≤z := Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) C])
  have hB : 0<B := binaryLogCoefficient_pos
  have ha : (Nat.clog 2 (m+1):ℝ)+1 ≤ B*x := padded_clog_succ_le m
  have hu : (Nat.clog 2 (U+1):ℝ) ≤ B*y := by
    have h := padded_clog_succ_le U
    change (Nat.clog 2 (U+1):ℝ)+1 ≤ B*y at h
    linarith
  have hc : (Nat.clog 2 (C+2):ℝ) ≤ B*z := by
    have h := padded_clog_le C
    change (Nat.clog 2 (C+2):ℝ)+1 ≤ B*z at h
    linarith
  have hxy : x+y≤(2/l)*x*y := by
    have h₁ := mul_le_mul_of_nonneg_left hy (show 0≤x by linarith)
    have h₂ := mul_le_mul_of_nonneg_right hx (show 0≤y by linarith)
    have he : (2/l)*x*y=(2*x*y)/l := by ring
    rw [he]
    apply (le_div_iff₀ hl).mpr
    nlinarith only [h₁,h₂]
  have hb : (Nat.clog 2 (m+1):ℝ)+(Nat.clog 2 (U+1):ℝ)+1 ≤ B*((2/l)*x*y) := by
    calc
      _ ≤ B*x+B*y := by linarith
      _ = B*(x+y) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hxy hB.le
  push_cast
  calc
    _ ≤ (B*x)*(B*((2/l)*x*y))*(B*z) := by
      have hx0 : 0≤x := by linarith
      have hy0 : 0≤y := by linarith
      have hz0 : 0≤z := by linarith
      gcongr
    _ = _ := by
      change _ = (2*B^3/l)*x^2*y*z
      ring

private def finalExponentConstant (P : DataStructurePrograms) : ℝ :=
  12*P.rateExponent + 2/(Real.log 2)^(47/48:ℝ)

private theorem finalExponentConstant_nonneg (P : DataStructurePrograms) :
    0 ≤ finalExponentConstant P := by
  unfold finalExponentConstant
  have h := P.rateExponent_nonneg
  positivity

private def finalTimeCoefficient (P : DataStructurePrograms) : ℝ :=
  max 1 (P.timeConstant:ℝ)*scalingLogCoefficient*(P.solverRateCoefficient+1)

private theorem finalTimeCoefficient_pos (P : DataStructurePrograms) :
    0 < finalTimeCoefficient P := by
  unfold finalTimeCoefficient
  have h := P.solverRateCoefficient_pos
  exact mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) scalingLogCoefficient_pos)
    (by linarith)

private theorem product_timeFactor (B D : ℝ) (m : ℕ) :
    alg2TimeFactor B (47/48) m * alg2TimeFactor D (47/48) m =
      alg2TimeFactor (B+D) (47/48) m := by
  rw [scalingTimeFactor_eq, scalingTimeFactor_eq, scalingTimeFactor_eq, ←Real.exp_add, add_mul]

/-- The explicit exponent used by the linked program tends to zero. -/
def linkedTimeExponent (P : DataStructurePrograms) : ℕ → ℝ :=
  scalingTimeExponent (finalTimeCoefficient P) (finalExponentConstant P)

/-- The scaled cost bound has the paper's two logarithms and vanishing
edge exponent, with a separate linear term for the original vertices. -/
theorem DataStructurePrograms.program_runsTo_timeBound (P : DataStructurePrograms)
    (I : Instance) (hv : I.IsValid) (ω : ℕ → Bool) :
    ∃ out cost, RunsTo (wordSize (scratchOuterMultiplier 1 P.scratchDegree) I.encode) P.program I.encode ω out cost ∧
      I.IsCorrectAnswer out ∧ (cost:ℝ) ≤ timeBound P.timeConstant (linkedTimeExponent P) I := by
  obtain ⟨out,cost,n,j,M,hM,hn,hj,hr,hcorrect,hcost⟩ := P.program_runsTo_log_bound I hv ω
  let m := I.m
  let U := I.maxCapacity
  let C := I.maxCost
  let K := (P.timeConstant:ℝ)
  let x := (m:ℝ)+2
  let l := Real.log x
  let u := Real.log ((U:ℝ)+2)
  let c := Real.log ((C:ℝ)+2)
  let W := alg2TimeFactor (12*P.rateExponent) (47/48) m
  let V := alg2TimeFactor (2/(Real.log 2)^(47/48:ℝ)) (47/48) m
  have hn' : n≤P.timeConstant*m := hn.trans (Nat.mul_le_mul_left _ (min_le_right _ _))
  have hs := P.linkedSolverLogCost_le m n j M hn' hj (Finset.mem_Icc.mp hM).2
  have hW : 1≤W := scalingTimeFactor_one_le (mul_nonneg (by norm_num) P.rateExponent_nonneg) m
  have hx : 2≤x := by dsimp only [x]; linarith [Nat.cast_nonneg (α:=ℝ) m]
  have hl : 0≤l := Real.log_nonneg (by linarith)
  have hu : 0≤u := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) U])
  have hc : 0≤c := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) C])
  have hpower : l^2≤V := by
    apply le_trans (pow_le_pow_left₀ hl (show l≤l+2 by linarith) 2)
    simpa only [Nat.cast_ofNat] using paddedLog_pow_le_timeFactor 2 m
  have hlogs := scalingLogs_le m U C
  have hs' : linkedRuntimeLogCost P.runtimeResources n j M + m ≤ (P.solverRateCoefficient+1)*x*W := by
    have hm : (m:ℝ)≤x*W := by
      have h := mul_le_mul_of_nonneg_left hW (show 0≤x by linarith)
      change (m:ℝ)≤x*W
      dsimp only [x] at h ⊢
      linarith
    change linkedRuntimeLogCost P.runtimeResources n j M ≤ P.solverRateCoefficient*x*W at hs
    linarith only [hs,hm,show (P.solverRateCoefficient+1)*x*W=P.solverRateCoefficient*x*W+x*W by ring]
  let L : ℝ := (((Nat.clog 2 (m+1)+1)*
    (Nat.clog 2 (m+1)+Nat.clog 2 (U+1)+1)*Nat.clog 2 (C+2)):ℕ)
  have hL : 0≤L := Nat.cast_nonneg _
  have hL' : L≤scalingLogCoefficient*l^2*u*c := hlogs
  have hcoef := scalingLogCoefficient_pos
  have hrateCoef := P.solverRateCoefficient_pos
  have hK : 0≤K := Nat.cast_nonneg _
  have hterm : K*L*(linkedRuntimeLogCost P.runtimeResources n j M + m) ≤
      max 1 K*(scalingLogCoefficient*l^2*u*c)*((P.solverRateCoefficient+1)*x*W) := by
    have hbound : 0≤(P.solverRateCoefficient+1)*x*W := by positivity
    apply le_trans (mul_le_mul_of_nonneg_left hs' (mul_nonneg hK hL))
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (le_max_right _ _) hL' hL (le_trans zero_le_one (le_max_left _ _))) hbound
  refine ⟨out,cost,hr,hcorrect,?_⟩
  apply cost_le_timeBound_of_timeFactor _ _ _ _ (finalTimeCoefficient_pos P)
  have hcast : (cost:ℝ)≤K*L*(linkedRuntimeLogCost P.runtimeResources n j M + m)+K*I.n := by
    dsimp only [K,L,m,U,C]
    push_cast at hcost ⊢
    simpa only [mul_assoc] using hcost
  calc
    _ ≤ K*L*(linkedRuntimeLogCost P.runtimeResources n j M + m)+K*I.n := hcast
    _ ≤ max 1 K*(scalingLogCoefficient*l^2*u*c)*((P.solverRateCoefficient+1)*x*W)+K*I.n :=
      add_le_add_left hterm _
    _ = K*I.n + (x*finalTimeCoefficient P*(W*l^2))*u*c := by
      unfold finalTimeCoefficient
      change _ = K*I.n + (x*(max 1 K*scalingLogCoefficient*(P.solverRateCoefficient+1))*(W*l^2))*u*c
      ring
    _ ≤ K*I.n + (x*finalTimeCoefficient P*(W*V))*u*c := by
      have hfinal := finalTimeCoefficient_pos P
      have hx0 : 0≤x := by linarith
      have hW0 : 0≤W := by linarith
      gcongr
    _ = _ := by
      dsimp only [W,V,finalExponentConstant]
      rw [product_timeFactor]

/-- Theorem 1.1 (page 2), conditional on the min-ratio and forest machine
modules, the supported chain model and their stated resource bounds. -/
theorem theorem_1_1_of_fixed_precision_programs : DataStructurePrograms → MinCostFlowStatement := by
  intro P
  refine ⟨P.program, scratchOuterMultiplier 1 P.scratchDegree, P.timeConstant,
    linkedTimeExponent P, P.program_deterministic, ?_, P.program_runsTo_timeBound⟩
  exact scalingTimeExponent_tendsto _ _ (finalExponentConstant_nonneg P)

private def widenedFinalExponentConstant (P : WidenedDataStructurePrograms) : ℝ :=
  12*P.rateExponent + 2/(Real.log 2)^(47/48:ℝ)

private theorem widenedFinalExponentConstant_nonneg (P : WidenedDataStructurePrograms) :
    0 ≤ widenedFinalExponentConstant P := by
  unfold widenedFinalExponentConstant
  have h := P.rateExponent_nonneg
  positivity

private def widenedFinalTimeCoefficient (P : WidenedDataStructurePrograms) : ℝ :=
  max 1 (P.timeConstant:ℝ)*scalingLogCoefficient*(P.solverRateCoefficient+1)

private theorem widenedFinalTimeCoefficient_pos (P : WidenedDataStructurePrograms) :
    0 < widenedFinalTimeCoefficient P := by
  unfold widenedFinalTimeCoefficient
  have h := P.solverRateCoefficient_pos
  exact mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) scalingLogCoefficient_pos)
    (by linarith)

/-- The explicit exponent used by the linked program tends to zero. -/
def widenedLinkedTimeExponent (P : WidenedDataStructurePrograms) : ℕ → ℝ :=
  scalingTimeExponent (widenedFinalTimeCoefficient P) (widenedFinalExponentConstant P)

/-- The scaled cost bound has the paper's two logarithms and vanishing
edge exponent, with a separate linear term for the original vertices. -/
theorem WidenedDataStructurePrograms.program_runsTo_timeBound (P : WidenedDataStructurePrograms)
    (I : Instance) (hv : I.IsValid) (ω : ℕ → Bool) :
    ∃ out cost, RunsTo (wordSize (scratchOuterMultiplier 1 P.scratchDegree) I.encode) P.program I.encode ω out cost ∧
      I.IsCorrectAnswer out ∧ (cost:ℝ) ≤ timeBound P.timeConstant (widenedLinkedTimeExponent P) I := by
  obtain ⟨out,cost,hr,hcorrect,hcost⟩ := P.program_runsTo I hv ω
  let S : ℝ := linkedWidenedSolverTime P.runtimeResources
    (P.timeConstant*min I.n I.m) (P.timeConstant*I.m)
  let m := I.m
  let U := I.maxCapacity
  let C := I.maxCost
  let K := (P.timeConstant:ℝ)
  let x := (m:ℝ)+2
  let l := Real.log x
  let u := Real.log ((U:ℝ)+2)
  let c := Real.log ((C:ℝ)+2)
  let W := alg2TimeFactor (12*P.rateExponent) (47/48) m
  let V := alg2TimeFactor (2/(Real.log 2)^(47/48:ℝ)) (47/48) m
  have hs := P.linkedSolverTime_le m (P.timeConstant*min I.n I.m) (P.timeConstant*I.m)
    (Nat.mul_le_mul_left _ (min_le_right _ _)) le_rfl
  have hW : 1≤W := scalingTimeFactor_one_le (mul_nonneg (by norm_num) P.rateExponent_nonneg) m
  have hx : 2≤x := by dsimp only [x]; linarith [Nat.cast_nonneg (α:=ℝ) m]
  have hl : 0≤l := Real.log_nonneg (by linarith)
  have hu : 0≤u := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) U])
  have hc : 0≤c := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) C])
  have hpower : l^2≤V := by
    apply le_trans (pow_le_pow_left₀ hl (show l≤l+2 by linarith) 2)
    simpa only [Nat.cast_ofNat] using paddedLog_pow_le_timeFactor 2 m
  have hlogs := scalingLogs_le m U C
  have hs' : S + m ≤ (P.solverRateCoefficient+1)*x*W := by
    have hm : (m:ℝ)≤x*W := by
      have h := mul_le_mul_of_nonneg_left hW (show 0≤x by linarith)
      change (m:ℝ)≤x*W
      dsimp only [x] at h ⊢
      linarith
    change S ≤ P.solverRateCoefficient*x*W at hs
    linarith only [hs,hm,show (P.solverRateCoefficient+1)*x*W=P.solverRateCoefficient*x*W+x*W by ring]
  let L : ℝ := (((Nat.clog 2 (m+1)+1)*
    (Nat.clog 2 (m+1)+Nat.clog 2 (U+1)+1)*Nat.clog 2 (C+2)):ℕ)
  have hL : 0≤L := Nat.cast_nonneg _
  have hL' : L≤scalingLogCoefficient*l^2*u*c := hlogs
  have hcoef := scalingLogCoefficient_pos
  have hrateCoef := P.solverRateCoefficient_pos
  have hK : 0≤K := Nat.cast_nonneg _
  have hterm : K*L*(S + m) ≤
      max 1 K*(scalingLogCoefficient*l^2*u*c)*((P.solverRateCoefficient+1)*x*W) := by
    have hbound : 0≤(P.solverRateCoefficient+1)*x*W := by positivity
    apply le_trans (mul_le_mul_of_nonneg_left hs' (mul_nonneg hK hL))
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (le_max_right _ _) hL' hL (le_trans zero_le_one (le_max_left _ _))) hbound
  refine ⟨out,cost,hr,hcorrect,?_⟩
  apply cost_le_timeBound_of_timeFactor _ _ _ _ (widenedFinalTimeCoefficient_pos P)
  have hcast : (cost:ℝ)≤K*L*(S + m)+K*I.n := by
    dsimp only [K,L,m,U,C,S]
    have hc' : (cost:ℝ)≤((_ : ℕ):ℝ) := (Nat.cast_le (α:=ℝ)).mpr hcost
    push_cast at hc' ⊢
    simpa only [mul_assoc] using hc'
  calc
    _ ≤ K*L*(S + m)+K*I.n := hcast
    _ ≤ max 1 K*(scalingLogCoefficient*l^2*u*c)*((P.solverRateCoefficient+1)*x*W)+K*I.n :=
      add_le_add_left hterm _
    _ = K*I.n + (x*widenedFinalTimeCoefficient P*(W*l^2))*u*c := by
      unfold widenedFinalTimeCoefficient
      change _ = K*I.n + (x*(max 1 K*scalingLogCoefficient*(P.solverRateCoefficient+1))*(W*l^2))*u*c
      ring
    _ ≤ K*I.n + (x*widenedFinalTimeCoefficient P*(W*V))*u*c := by
      have hfinal := widenedFinalTimeCoefficient_pos P
      have hx0 : 0≤x := by linarith
      have hW0 : 0≤W := by linarith
      gcongr
    _ = _ := by
      dsimp only [W,V,widenedFinalExponentConstant]
      rw [product_timeFactor]

/-- Theorem 1.1 (page 2), conditional on the min-ratio and forest machine
modules and the quantitative certificates of the two tree-chain tools. -/
theorem theorem_1_1_of_programs : WidenedDataStructurePrograms → MinCostFlowStatement := by
  intro P
  refine ⟨P.program, scratchOuterMultiplier 1 P.scratchDegree, P.timeConstant,
    widenedLinkedTimeExponent P, P.program_deterministic, ?_, P.program_runsTo_timeBound⟩
  exact scalingTimeExponent_tendsto _ _ (widenedFinalExponentConstant_nonneg P)

private def connectedFinalExponentConstant (P : ConnectedDataStructurePrograms) : ℝ :=
  12*P.rateExponent + 2/(Real.log 2)^(47/48:ℝ)

private theorem connectedFinalExponentConstant_nonneg (P : ConnectedDataStructurePrograms) :
    0 ≤ connectedFinalExponentConstant P := by
  unfold connectedFinalExponentConstant
  have h := P.rateExponent_nonneg
  positivity

private def connectedFinalTimeCoefficient (P : ConnectedDataStructurePrograms) : ℝ :=
  max 1 (P.timeConstant:ℝ)*scalingLogCoefficient*(P.solverRateCoefficient+1)

private theorem connectedFinalTimeCoefficient_pos (P : ConnectedDataStructurePrograms) :
    0 < connectedFinalTimeCoefficient P := by
  unfold connectedFinalTimeCoefficient
  have h := P.solverRateCoefficient_pos
  exact mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) scalingLogCoefficient_pos)
    (by linarith)

/-- The explicit exponent used by the linked program tends to zero. -/
def connectedLinkedTimeExponent (P : ConnectedDataStructurePrograms) : ℕ → ℝ :=
  scalingTimeExponent (connectedFinalTimeCoefficient P) (connectedFinalExponentConstant P)

/-- The scaled cost bound has the paper's two logarithms and vanishing
edge exponent, with a separate linear term for the original vertices. -/
theorem ConnectedDataStructurePrograms.program_runsTo_timeBound (P : ConnectedDataStructurePrograms)
    (I : Instance) (hv : I.IsValid) (ω : ℕ → Bool) :
    ∃ out cost, RunsTo (wordSize (scratchOuterMultiplier 1 P.scratchDegree) I.encode) P.program I.encode ω out cost ∧
      I.IsCorrectAnswer out ∧ (cost:ℝ) ≤ timeBound P.timeConstant (connectedLinkedTimeExponent P) I := by
  obtain ⟨out,cost,hr,hcorrect,hcost⟩ := P.program_runsTo I hv ω
  let S : ℝ := linkedConnectedSolverTime P.runtimeResources
    (P.timeConstant*min I.n I.m) (P.timeConstant*I.m)
  let m := I.m
  let U := I.maxCapacity
  let C := I.maxCost
  let K := (P.timeConstant:ℝ)
  let x := (m:ℝ)+2
  let l := Real.log x
  let u := Real.log ((U:ℝ)+2)
  let c := Real.log ((C:ℝ)+2)
  let W := alg2TimeFactor (12*P.rateExponent) (47/48) m
  let V := alg2TimeFactor (2/(Real.log 2)^(47/48:ℝ)) (47/48) m
  have hs := P.linkedSolverTime_le m (P.timeConstant*min I.n I.m) (P.timeConstant*I.m)
    (Nat.mul_le_mul_left _ (min_le_right _ _)) le_rfl
  have hW : 1≤W := scalingTimeFactor_one_le (mul_nonneg (by norm_num) P.rateExponent_nonneg) m
  have hx : 2≤x := by dsimp only [x]; linarith [Nat.cast_nonneg (α:=ℝ) m]
  have hl : 0≤l := Real.log_nonneg (by linarith)
  have hu : 0≤u := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) U])
  have hc : 0≤c := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) C])
  have hpower : l^2≤V := by
    apply le_trans (pow_le_pow_left₀ hl (show l≤l+2 by linarith) 2)
    simpa only [Nat.cast_ofNat] using paddedLog_pow_le_timeFactor 2 m
  have hlogs := scalingLogs_le m U C
  have hs' : S + m ≤ (P.solverRateCoefficient+1)*x*W := by
    have hm : (m:ℝ)≤x*W := by
      have h := mul_le_mul_of_nonneg_left hW (show 0≤x by linarith)
      change (m:ℝ)≤x*W
      dsimp only [x] at h ⊢
      linarith
    change S ≤ P.solverRateCoefficient*x*W at hs
    linarith only [hs,hm,show (P.solverRateCoefficient+1)*x*W=P.solverRateCoefficient*x*W+x*W by ring]
  let L : ℝ := (((Nat.clog 2 (m+1)+1)*
    (Nat.clog 2 (m+1)+Nat.clog 2 (U+1)+1)*Nat.clog 2 (C+2)):ℕ)
  have hL : 0≤L := Nat.cast_nonneg _
  have hL' : L≤scalingLogCoefficient*l^2*u*c := hlogs
  have hcoef := scalingLogCoefficient_pos
  have hrateCoef := P.solverRateCoefficient_pos
  have hK : 0≤K := Nat.cast_nonneg _
  have hterm : K*L*(S + m) ≤
      max 1 K*(scalingLogCoefficient*l^2*u*c)*((P.solverRateCoefficient+1)*x*W) := by
    have hbound : 0≤(P.solverRateCoefficient+1)*x*W := by positivity
    apply le_trans (mul_le_mul_of_nonneg_left hs' (mul_nonneg hK hL))
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (le_max_right _ _) hL' hL (le_trans zero_le_one (le_max_left _ _))) hbound
  refine ⟨out,cost,hr,hcorrect,?_⟩
  apply cost_le_timeBound_of_timeFactor _ _ _ _ (connectedFinalTimeCoefficient_pos P)
  have hcast : (cost:ℝ)≤K*L*(S + m)+K*I.n := by
    dsimp only [K,L,m,U,C,S]
    have hc' : (cost:ℝ)≤((_ : ℕ):ℝ) := (Nat.cast_le (α:=ℝ)).mpr hcost
    push_cast at hc' ⊢
    simpa only [mul_assoc] using hc'
  calc
    _ ≤ K*L*(S + m)+K*I.n := hcast
    _ ≤ max 1 K*(scalingLogCoefficient*l^2*u*c)*((P.solverRateCoefficient+1)*x*W)+K*I.n :=
      add_le_add_left hterm _
    _ = K*I.n + (x*connectedFinalTimeCoefficient P*(W*l^2))*u*c := by
      unfold connectedFinalTimeCoefficient
      change _ = K*I.n + (x*(max 1 K*scalingLogCoefficient*(P.solverRateCoefficient+1))*(W*l^2))*u*c
      ring
    _ ≤ K*I.n + (x*connectedFinalTimeCoefficient P*(W*V))*u*c := by
      have hfinal := connectedFinalTimeCoefficient_pos P
      have hx0 : 0≤x := by linarith
      have hW0 : 0≤W := by linarith
      gcongr
    _ = _ := by
      dsimp only [W,V,connectedFinalExponentConstant]
      rw [product_timeFactor]

/-- Theorem 1.1 (page 2), conditional on the min-ratio and forest machine
modules and the quantitative certificates of the two tree-chain tools. -/
theorem theorem_1_1_of_connected_programs : ConnectedDataStructurePrograms → MinCostFlowStatement := by
  intro P
  refine ⟨P.program, scratchOuterMultiplier 1 P.scratchDegree, P.timeConstant,
    connectedLinkedTimeExponent P, P.program_deterministic, ?_, P.program_runsTo_timeBound⟩
  exact scalingTimeExponent_tendsto _ _ (connectedFinalExponentConstant_nonneg P)

private theorem scaling_cost_le_timeBound
    (K : ℕ) (S_val cost : ℕ) (rateCoef rateExp finalCoef : ℝ) (I : Instance)
    (hRateExp : 0 ≤ rateExp) (hRateCoef : 0 < rateCoef)
    (hFinalCoef : finalCoef = max 1 (K : ℝ) * scalingLogCoefficient * (rateCoef + 1))
    (hFinalPos : 0 < finalCoef)
    (hs : (S_val : ℝ) ≤ rateCoef * ((I.m : ℝ) + 2) * alg2TimeFactor (12 * rateExp) (47 / 48) I.m)
    (hcost : cost ≤ K * (Nat.clog 2 (I.m + 1) + 1) *
      (Nat.clog 2 (I.m + 1) + Nat.clog 2 (I.maxCapacity + 1) + 1) * Nat.clog 2 (I.maxCost + 2) *
      (S_val + I.m) + K * I.n) :
    (cost : ℝ) ≤ timeBound K
      (scalingTimeExponent finalCoef (12 * rateExp + 2 / (Real.log 2) ^ (47 / 48 : ℝ))) I := by
  let S : ℝ := (S_val : ℝ)
  let m := I.m
  let U := I.maxCapacity
  let C := I.maxCost
  let KR := (K : ℝ)
  let x := (m : ℝ) + 2
  let l := Real.log x
  let u := Real.log ((U : ℝ) + 2)
  let c := Real.log ((C : ℝ) + 2)
  let W := alg2TimeFactor (12 * rateExp) (47 / 48) m
  let V := alg2TimeFactor (2 / (Real.log 2) ^ (47 / 48 : ℝ)) (47 / 48) m
  have hW : 1 ≤ W := scalingTimeFactor_one_le (mul_nonneg (by norm_num) hRateExp) m
  have hx : 2 ≤ x := by dsimp only [x]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hl : 0 ≤ l := Real.log_nonneg (by linarith)
  have hu : 0 ≤ u := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) U])
  have hc : 0 ≤ c := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) C])
  have hpower : l ^ 2 ≤ V := by
    apply le_trans (pow_le_pow_left₀ hl (show l ≤ l + 2 by linarith) 2)
    simpa only [Nat.cast_ofNat] using paddedLog_pow_le_timeFactor 2 m
  have hlogs := scalingLogs_le m U C
  have hs' : S + m ≤ (rateCoef + 1) * x * W := by
    have hm : (m : ℝ) ≤ x * W := by
      have h := mul_le_mul_of_nonneg_left hW (show 0 ≤ x by linarith)
      change (m : ℝ) ≤ x * W
      dsimp only [x] at h ⊢
      linarith
    change S ≤ rateCoef * x * W at hs
    linarith only [hs, hm, show (rateCoef + 1) * x * W = rateCoef * x * W + x * W by ring]
  let L : ℝ := (((Nat.clog 2 (m + 1) + 1) *
    (Nat.clog 2 (m + 1) + Nat.clog 2 (U + 1) + 1) * Nat.clog 2 (C + 2) : ℕ))
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hL' : L ≤ scalingLogCoefficient * l ^ 2 * u * c := hlogs
  have hcoef := scalingLogCoefficient_pos
  have hK : 0 ≤ KR := Nat.cast_nonneg _
  have hterm : KR * L * (S + m) ≤
      max 1 KR * (scalingLogCoefficient * l ^ 2 * u * c) * ((rateCoef + 1) * x * W) := by
    have hbound : 0 ≤ (rateCoef + 1) * x * W := by positivity
    apply le_trans (mul_le_mul_of_nonneg_left hs' (mul_nonneg hK hL))
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (le_max_right _ _) hL' hL (le_trans zero_le_one (le_max_left _ _))) hbound
  apply cost_le_timeBound_of_timeFactor _ _ _ _ hFinalPos
  have hcast : (cost : ℝ) ≤ KR * L * (S + m) + KR * I.n := by
    dsimp only [KR, L, m, U, C, S]
    have hc' : (cost : ℝ) ≤ ((_ : ℕ) : ℝ) := (Nat.cast_le (α := ℝ)).mpr hcost
    push_cast at hc' ⊢
    simpa only [mul_assoc] using hc'
  calc
    _ ≤ KR * L * (S + m) + KR * I.n := hcast
    _ ≤ max 1 KR * (scalingLogCoefficient * l ^ 2 * u * c) * ((rateCoef + 1) * x * W) + KR * I.n :=
      add_le_add_left hterm _
    _ = KR * I.n + (x * finalCoef * (W * l ^ 2)) * u * c := by
      rw [hFinalCoef]
      ring
    _ ≤ KR * I.n + (x * finalCoef * (W * V)) * u * c := by
      have hx0 : 0 ≤ x := by linarith
      have hW0 : 0 ≤ W := by linarith
      gcongr
    _ = _ := by
      dsimp only [W, V]
      rw [product_timeFactor]

private def concreteFinalExponentConstant (P : ConcreteDataStructurePrograms) : ℝ :=
  12 * P.rateExponent + 2 / (Real.log 2) ^ (47 / 48 : ℝ)

private theorem concreteFinalExponentConstant_nonneg (P : ConcreteDataStructurePrograms) :
    0 ≤ concreteFinalExponentConstant P := by
  unfold concreteFinalExponentConstant
  have h := P.rateExponent_nonneg
  positivity

private def concreteFinalTimeCoefficient (P : ConcreteDataStructurePrograms) : ℝ :=
  max 1 (P.timeConstant : ℝ) * scalingLogCoefficient * (P.solverRateCoefficient + 1)

private theorem concreteFinalTimeCoefficient_pos (P : ConcreteDataStructurePrograms) :
    0 < concreteFinalTimeCoefficient P := by
  unfold concreteFinalTimeCoefficient
  have h := P.solverRateCoefficient_pos
  exact mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) scalingLogCoefficient_pos)
    (by linarith)

/-- The explicit exponent used by the concrete linked program tends to zero. -/
def concreteLinkedTimeExponent (P : ConcreteDataStructurePrograms) : ℕ → ℝ :=
  scalingTimeExponent (concreteFinalTimeCoefficient P) (concreteFinalExponentConstant P)

/-- The concrete linked program meets the Theorem 1.1 runtime bound. -/
theorem ConcreteDataStructurePrograms.program_runsTo_timeBound
    (P : ConcreteDataStructurePrograms) (I : Instance) (hv : I.IsValid) (ω : ℕ → Bool) :
    ∃ out cost, RunsTo (wordSize (scratchOuterMultiplier 1 P.scratchDegree) I.encode) P.program I.encode ω out cost ∧
      I.IsCorrectAnswer out ∧ (cost : ℝ) ≤ timeBound P.timeConstant (concreteLinkedTimeExponent P) I := by
  obtain ⟨out, cost, hr, hcorrect, hcost⟩ := P.program_runsTo I hv ω
  refine ⟨out, cost, hr, hcorrect, ?_⟩
  exact scaling_cost_le_timeBound P.timeConstant _ cost P.solverRateCoefficient P.rateExponent
    (concreteFinalTimeCoefficient P) I P.rateExponent_nonneg P.solverRateCoefficient_pos rfl
    (concreteFinalTimeCoefficient_pos P)
    (P.linkedSolverTime_le I.m (P.timeConstant * min I.n I.m) (P.timeConstant * I.m)
      (Nat.mul_le_mul_left _ (min_le_right _ _)) le_rfl) hcost

/-- Theorem 1.1 (page 2), instantiated with the degree-free ordered bundle chain
(`Chain.Ordered.concrete_theorem_5_1`). It takes no cited hypotheses and no restart obligations,
only the min-ratio (`cycle`) and dynamic-forest (`forest`) machine programs with their polynomial
space and subpolynomial/polylogarithmic rate bounds. -/
theorem theorem_1_1_of_concrete_programs : ConcreteDataStructurePrograms → MinCostFlowStatement := by
  intro P
  refine ⟨P.program, scratchOuterMultiplier 1 P.scratchDegree, P.timeConstant,
    concreteLinkedTimeExponent P, P.program_deterministic, ?_, P.program_runsTo_timeBound⟩
  exact scalingTimeExponent_tendsto _ _ (concreteFinalExponentConstant_nonneg P)

private def forestCoreFinalExponentConstant (P : ForestConcreteProgramCore) : ℝ :=
  12 * P.rateExponent + 2 / (Real.log 2) ^ (47 / 48 : ℝ)

private theorem forestCoreFinalExponentConstant_nonneg (P : ForestConcreteProgramCore) :
    0 ≤ forestCoreFinalExponentConstant P := by
  unfold forestCoreFinalExponentConstant
  have h := P.rateExponent_nonneg
  positivity

private def forestCoreFinalTimeCoefficient (P : ForestConcreteProgramCore) : ℝ :=
  max 1 (P.timeConstant : ℝ) * scalingLogCoefficient * (P.solverRateCoefficient + 1)

private theorem forestCoreFinalTimeCoefficient_pos (P : ForestConcreteProgramCore) :
    0 < forestCoreFinalTimeCoefficient P := by
  unfold forestCoreFinalTimeCoefficient
  have h := P.solverRateCoefficient_pos
  exact mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) scalingLogCoefficient_pos)
    (by linarith)

private def forestBaseFinalExponentConstant (P : ForestConcreteProgramBase) : ℝ :=
  forestCoreFinalExponentConstant P.toCore

private theorem forestBaseFinalExponentConstant_nonneg (P : ForestConcreteProgramBase) :
    0 ≤ forestBaseFinalExponentConstant P :=
  forestCoreFinalExponentConstant_nonneg P.toCore

private def forestBaseFinalTimeCoefficient (P : ForestConcreteProgramBase) : ℝ :=
  forestCoreFinalTimeCoefficient P.toCore

private theorem forestBaseFinalTimeCoefficient_pos (P : ForestConcreteProgramBase) :
    0 < forestBaseFinalTimeCoefficient P :=
  forestCoreFinalTimeCoefficient_pos P.toCore

/-- The explicit exponent used by the linked program with only the min-ratio cycle module tends to zero. -/
def forestConcreteLinkedTimeExponent (P : ForestConcretePrograms) : ℕ → ℝ :=
  scalingTimeExponent (forestBaseFinalTimeCoefficient P.toBase) (forestBaseFinalExponentConstant P.toBase)

/-- The linked program with only the min-ratio cycle module and the dynamic link-cut forest meets the Theorem 1.1 runtime bound. -/
theorem ForestConcretePrograms.program_runsTo_timeBound
    (P : ForestConcretePrograms) (I : Instance) (hv : I.IsValid) (ω : ℕ → Bool) :
    ∃ out cost, RunsTo (wordSize (scratchOuterMultiplier 1 P.scratchDegree) I.encode) P.program I.encode ω out cost ∧
      I.IsCorrectAnswer out ∧ (cost : ℝ) ≤ timeBound P.timeConstant (forestConcreteLinkedTimeExponent P) I := by
  obtain ⟨out, cost, hr, hcorrect, hcost⟩ := P.program_runsTo I hv ω
  refine ⟨out, cost, hr, hcorrect, ?_⟩
  exact scaling_cost_le_timeBound P.timeConstant _ cost P.solverRateCoefficient P.rateExponent
    (forestBaseFinalTimeCoefficient P.toBase) I P.rateExponent_nonneg P.solverRateCoefficient_pos rfl
    (forestBaseFinalTimeCoefficient_pos P.toBase)
    (P.linkedSolverTime_le I.m (P.timeConstant * min I.n I.m) (P.timeConstant * I.m)
      (Nat.mul_le_mul_left _ (min_le_right _ _)) le_rfl) hcost

/-- Theorem 1.1 (page 2), discharging the dynamic link-cut forest internally via
`dynLctForestBodies` on the degree-free ordered bundle chain (`Chain.Ordered.concrete_theorem_5_1`)
It takes no cited hypotheses and no restart obligations, only the min-ratio data structure
machine program with its bounds. -/
theorem theorem_1_1_of_mrds_programs : ForestConcretePrograms → MinCostFlowStatement := by
  intro P
  refine ⟨P.program, scratchOuterMultiplier 1 P.scratchDegree, P.timeConstant,
    forestConcreteLinkedTimeExponent P, P.program_deterministic, ?_, P.program_runsTo_timeBound⟩
  exact scalingTimeExponent_tendsto _ _ (forestBaseFinalExponentConstant_nonneg P.toBase)

/-- The explicit exponent used by the dyadic-`κ` linked program with only the min-ratio cycle module tends to zero. -/
def dyadicForestConcreteLinkedTimeExponent (P : DyadicForestConcretePrograms) : ℕ → ℝ :=
  scalingTimeExponent (forestBaseFinalTimeCoefficient P.toBase) (forestBaseFinalExponentConstant P.toBase)

/-- The dyadic-`κ` linked program with only the min-ratio cycle module with dynamic link-cut forest meets the Theorem 1.1
runtime bound. -/
theorem DyadicForestConcretePrograms.program_runsTo_timeBound
    (P : DyadicForestConcretePrograms) (I : Instance) (hv : I.IsValid) (ω : ℕ → Bool) :
    ∃ out cost, RunsTo (wordSize (scratchOuterMultiplier 1 P.scratchDegree) I.encode) P.program I.encode ω out cost ∧
      I.IsCorrectAnswer out ∧ (cost : ℝ) ≤ timeBound P.timeConstant (dyadicForestConcreteLinkedTimeExponent P) I := by
  obtain ⟨out, cost, hr, hcorrect, hcost⟩ := P.program_runsTo I hv ω
  refine ⟨out, cost, hr, hcorrect, ?_⟩
  exact scaling_cost_le_timeBound P.timeConstant _ cost P.solverRateCoefficient P.rateExponent
    (forestBaseFinalTimeCoefficient P.toBase) I P.rateExponent_nonneg P.solverRateCoefficient_pos rfl
    (forestBaseFinalTimeCoefficient_pos P.toBase)
    (P.linkedSolverTime_le I.m (P.timeConstant * min I.n I.m) (P.timeConstant * I.m)
      (Nat.mul_le_mul_left _ (min_le_right _ _)) le_rfl) hcost

/-- Theorem 1.1 (page 2) for `DyadicForestConcretePrograms`: same statement and runtime bound as
`theorem_1_1_of_mrds_programs`, with `supported` requiring
`Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / 2 ^ k)` (testing an exact dyadic ratio
threshold) in place of `Chain.Ordered.algorithm2_dsWithFailureOwn cfg`. -/
theorem theorem_1_1_of_dyadic_mrds_programs : DyadicForestConcretePrograms → MinCostFlowStatement := by
  intro P
  refine ⟨P.program, scratchOuterMultiplier 1 P.scratchDegree, P.timeConstant,
    dyadicForestConcreteLinkedTimeExponent P, P.program_deterministic, ?_, P.program_runsTo_timeBound⟩
  exact scalingTimeExponent_tendsto _ _ (forestBaseFinalExponentConstant_nonneg P.toBase)

/-- The explicit exponent used by the `V`-passing, arbitrary-`LastLevelTool`, dyadic-`κ` linked
program tends to zero. -/
def dyadicWithVConcreteLinkedTimeExponent (P : DyadicWithVConcretePrograms) : ℕ → ℝ :=
  scalingTimeExponent (forestCoreFinalTimeCoefficient P.toCore) (forestCoreFinalExponentConstant P.toCore)

/-- The `V`-passing, arbitrary-`LastLevelTool`, dyadic-`κ` linked program meets the Theorem 1.1
runtime bound. -/
theorem DyadicWithVConcretePrograms.program_runsTo_timeBound
    (P : DyadicWithVConcretePrograms) (I : Instance) (hv : I.IsValid) (ω : ℕ → Bool) :
    ∃ out cost, RunsTo (wordSize (scratchOuterMultiplier 1 P.scratchDegree) I.encode) P.program I.encode ω out cost ∧
      I.IsCorrectAnswer out ∧ (cost : ℝ) ≤ timeBound P.timeConstant (dyadicWithVConcreteLinkedTimeExponent P) I := by
  obtain ⟨out, cost, hr, hcorrect, hcost⟩ := P.program_runsTo I hv ω
  refine ⟨out, cost, hr, hcorrect, ?_⟩
  exact scaling_cost_le_timeBound P.timeConstant _ cost P.solverRateCoefficient P.rateExponent
    (forestCoreFinalTimeCoefficient P.toCore) I P.rateExponent_nonneg P.solverRateCoefficient_pos rfl
    (forestCoreFinalTimeCoefficient_pos P.toCore)
    (P.linkedSolverTime_le I.m (P.timeConstant * min I.n I.m) (P.timeConstant * I.m)
      (Nat.mul_le_mul_left _ (min_le_right _ _)) le_rfl) hcost

/-- Theorem 1.1 (page 2) for `DyadicWithVConcretePrograms` on the degree-free ordered bundle chain:
passes `V = solverPenalty J.m` into `minRatioMachineContractWithV` (`[graph, g, l, limbs,
precision, V, heap]`), accepts an arbitrary `lastTool : LastLevelTool` satisfying
`LastLevelTool.IsSpec (lastLevelParams lastConstant)`, discharges `ToolEmbedsSurvivingOrdRestart`
and `ToolNoReinsertOrdRestart`, and has no cited-result hypotheses or degree cap. -/
theorem theorem_1_1_of_dyadic_withV_mrds_programs : DyadicWithVConcretePrograms → MinCostFlowStatement := by
  intro P
  refine ⟨P.program, scratchOuterMultiplier 1 P.scratchDegree, P.timeConstant,
    dyadicWithVConcreteLinkedTimeExponent P, P.program_deterministic, ?_, P.program_runsTo_timeBound⟩
  exact scalingTimeExponent_tendsto _ _ (forestCoreFinalExponentConstant_nonneg P.toCore)

end MinCostFlow.Final
