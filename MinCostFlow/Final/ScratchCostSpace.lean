module

public import MinCostFlow.Final.ScratchCostStep
public import MinCostFlow.Scaling.CostStepSpace
public import MinCostFlow.Scaling.CapacityGraphSpaceBounds
import MinCostFlow.Scaling.CostStepWords
import MinCostFlow.Scaling.CostStepNumericFacts
import MinCostFlow.Scaling.CostStepInputFacts
import MinCostFlow.Scaling.BottleneckGuestSpace
import MinCostFlow.Scaling.CostRoundedScalarWords
import WordRAM.LinkDefs

/-!
# A uniform reserve for measured cost rounds

Both positive capacity calls fit polynomial reserves in their own graph
dimensions. The rounded primal graph and the routing residual have
polynomial size in the same numerical base. This gives one reservation
for the whole cost round and all of its word-size premises.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- Every positive capacity-model invocation has the same fixed polynomial
reserve bound, without assuming any property of a selected optimum. -/
theorem scratchCapacityPositiveSpace_le (c d : ℕ) (J : Circulation) (C U : ℕ) :
    let f := scratchWidthFactor c d
    scratchCapacityPositiveSpace c d J C U≤(capacityGraphSpaceBase J C U)^(260*f) := by
  let f := scratchWidthFactor c d
  have hf : 1≤f := scratchWidthFactor_pos c d
  let D := capacityGraphSpaceBase J C U
  let fuel := capacityRounds J.m U
  let N := (capacityStepNumberBase J.positiveInstance C U)^(256*f)
  have hD : J.n+2*J.m+C+U+8=D := rfl
  have hD8 : 8≤D := by omega
  have hDpos : 0<D := by omega
  have hbase : capacityStepNumberBase J.positiveInstance C U≤D := by
    change J.n+1+2*J.m+C+U+4≤D
    omega
  have hN : N≤D^(256*f) := Nat.pow_le_pow_left hbase (256*f)
  have hmLog : Nat.clog 2 (J.m+1)≤J.m+1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have huLog : Nat.clog 2 (U+1)≤U+1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hfuelLinear : fuel+1≤14*D := by
    change 1+11*Nat.clog 2 (J.m+1)+Nat.clog 2 (U+1)+1≤14*D
    omega
  have h64 : 64≤D^2 := Nat.pow_le_pow_left hD8 2
  have hD3 : 16*D≤D^3 := by
    simpa only [←pow_succ] using Nat.mul_le_mul (show 16≤D^2 by omega) (le_refl D)
  have hfuel : fuel+1≤D^3 := hfuelLinear.trans (by omega)
  have hcells : (fuel+1)*N≤D^(259*f) := by
    have h := Nat.mul_le_mul hfuel hN
    rw [←pow_add] at h
    exact h.trans (Nat.pow_le_pow_right hDpos (by omega))
  have hlinear : J.n+13*J.m+11≤D^2 := by
    have h : J.n+13*J.m+11≤7*D := by omega
    exact h.trans (by simpa only [pow_two] using Nat.mul_le_mul_right D (show 7≤D by omega))
  have h2_259 : D^2≤D^(259*f) := Nat.pow_le_pow_right hDpos (by omega)
  have hlast : 2*D^(259*f)≤D^(260*f) := by
    exact (Nat.mul_le_mul_right (D^(259*f)) (show 2≤D by omega)).trans ((pow_succ' D (259*f)).symm.le.trans (Nat.pow_le_pow_right hDpos (by omega)))
  change 2+5*J.m+scratchCapacityScalingSpace c d J.positiveInstance C U+J.m+2≤D^(260*f)
  unfold scratchCapacityScalingSpace scratchCapacityExponent
  rw [J.positiveInstance.solverWords_length]
  change 2+5*J.m+(2+5*J.m+(J.n+1)+2+J.m+2+(fuel+1)*N+J.m)+J.m+2≤D^(260*f)
  omega

/-- The non-adapted capacity wrapper needs no more reserve than its
positive-adapter invocation on the same original dimensions and bounds. -/
theorem scratchCapacityScalingSpace_le_positiveSpace (c d : ℕ) (J : Circulation) (C U : ℕ) :
    scratchCapacityScalingSpace c d J C U≤scratchCapacityPositiveSpace c d J C U := by
  let f := scratchWidthFactor c d
  have hp : (capacityStepNumberBase J C U)^(256*f)≤(capacityStepNumberBase J.positiveInstance C U)^(256*f) := by
    apply Nat.pow_le_pow_left
    change J.n+2*J.m+C+U+4≤J.n+1+2*J.m+C+U+4
    omega
  have hmul := Nat.mul_le_mul_left (capacityRounds J.m U+1) hp
  unfold scratchCapacityPositiveSpace scratchCapacityScalingSpace scratchCapacityExponent
  rw [J.solverWords_length,J.positiveInstance.solverWords_length]
  change 2+5*J.m+J.n+2+J.m+2+(capacityRounds J.m U+1)*(capacityStepNumberBase J C U)^(256*f)+J.m≤
    2+5*J.m+(2+5*J.m+(J.n+1)+2+J.m+2+
      (capacityRounds J.m U+1)*(capacityStepNumberBase J.positiveInstance C U)^(256*f)+J.m)+J.m+2
  omega

/-- The complete capacity wrapper also fits the fixed power-260 reserve. -/
theorem scratchCapacityScalingSpace_le (c d : ℕ) (J : Circulation) (C U : ℕ) :
    scratchCapacityScalingSpace c d J C U≤(capacityGraphSpaceBase J C U)^(260*scratchWidthFactor c d) :=
  (scratchCapacityScalingSpace_le_positiveSpace c d J C U).trans (scratchCapacityPositiveSpace_le c d J C U)

private theorem routed_reserve_bound (D base reserve extra f : ℕ) (hf : 1≤f) (hD8 : 8≤D)
    (hbase : base≤5*D) (hreserve : reserve≤base^(260*f)) (hextra : extra≤28*D) :
    extra+reserve≤D^(522*f) := by
  have hDpos : 0<D := by omega
  have h64 : 64≤D^2 := Nat.pow_le_pow_left hD8 2
  have hbase2 : base≤D^2 := hbase.trans
    (by simpa only [pow_two] using Nat.mul_le_mul_right D (show 5≤D by omega))
  have hN : reserve≤D^(520*f) := hreserve.trans (by
    rw [show 520*f=2*(260*f) by omega, pow_mul D]
    exact Nat.pow_le_pow_left hbase2 (260*f))
  have hsmall : 28*D≤D^3 :=
    (Nat.mul_le_mul_right D (show 28≤D^2 by omega)).trans_eq (pow_succ D 2).symm
  have h3_520 : D^3≤D^(520*f) := Nat.pow_le_pow_right hDpos (by omega)
  have hlast : 2*D^(520*f)≤D^(521*f) :=
    (Nat.mul_le_mul_right (D^(520*f)) (show 2≤D by omega)).trans ((pow_succ' D (520*f)).symm.le.trans (Nat.pow_le_pow_right hDpos (by omega)))
  have h521_522 : D^(521*f)≤D^(522*f) := Nat.pow_le_pow_right hDpos (by omega)
  omega

/-- Full capacity-backed source-routing label production has a uniform
polynomial reserve in the input dimensions and supplied bounds. -/
theorem scratchCapacityRoutingLabelsSpace_le (c d : ℕ) (J : Circulation) (C U : ℕ) :
    let f := scratchWidthFactor c d
    scratchCapacityRoutingLabelsSpace c d J C U≤(capacityGraphSpaceBase J C U)^(522*f) := by
  let f := scratchWidthFactor c d
  have hf : 1≤f := scratchWidthFactor_pos c d
  let D := capacityGraphSpaceBase J C U
  let M := J.m+J.n
  let Q := J.shortestRoutingGraph.residual J.shortestRoutingStart
  let extra := 4+16*M+M+5+5*(J.n+1)+6*M+2
  have hD : J.n+2*J.m+C+U+8=D := rfl
  have hD8 : 8≤D := by omega
  have hbase : capacityGraphSpaceBase Q C U≤5*D := by
    change (J.n+1)+2*((J.m+J.n)+(J.m+J.n))+C+U+8≤5*D
    omega
  have he : extra≤28*D := by dsimp only [extra,M]; omega
  have hres := routed_reserve_bound D _ _ extra f hf hD8 hbase (scratchCapacityPositiveSpace_le c d Q C U) he
  calc
    _ = extra+scratchCapacityPositiveSpace c d Q C U := by
      change 4+16*M+scratchCapacityPositiveSpace c d Q C U+M+5+5*(J.n+1)+6*M+2=extra+scratchCapacityPositiveSpace c d Q C U
      dsimp only [extra]
      omega
    _ ≤ _ := hres

/-- Including the primal residual does not increase the fixed power-522
bound for measured dual extraction, for every integral source flow. -/
theorem scratchCapacityExtractDualSpace_le (c d : ℕ) (J : Circulation) (flow : Fin J.m → ℤ) (C U : ℕ) :
    let f := scratchWidthFactor c d
    scratchCapacityExtractDualSpace c d J flow C U≤(capacityGraphSpaceBase J C U)^(522*f) := by
  let f := scratchWidthFactor c d
  have hf : 1≤f := scratchWidthFactor_pos c d
  let D := capacityGraphSpaceBase J C U
  let R := J.residual flow
  let M := R.m+R.n
  let Q := R.shortestRoutingGraph.residual R.shortestRoutingStart
  let extra := 2+10*J.m+(4+16*M+M+5+5*(J.n+1)+6*M+2)
  have hD : J.n+2*J.m+C+U+8=D := rfl
  have hD8 : 8≤D := by omega
  have hbase : capacityGraphSpaceBase Q C U≤5*D := by
    change (J.n+1)+2*(((J.m+J.m)+J.n)+((J.m+J.m)+J.n))+C+U+8≤5*D
    omega
  have he : extra≤28*D := by
    change 2+10*J.m+(4+16*(J.m+J.m+J.n)+(J.m+J.m+J.n)+5+5*(J.n+1)+6*(J.m+J.m+J.n)+2)≤28*D
    omega
  have hres := routed_reserve_bound D _ _ extra f hf hD8 hbase (scratchCapacityPositiveSpace_le c d Q C U) he
  calc
    _ = extra+scratchCapacityPositiveSpace c d Q C U := by
      change 2+10*J.m+(4+16*M+scratchCapacityPositiveSpace c d Q C U+M+5+5*(J.n+1)+6*M+2)=extra+scratchCapacityPositiveSpace c d Q C U
      dsimp only [extra]
      omega
    _ ≤ _ := hres

/-- Every state uses the same full cost-round workspace bound, including
both exact capacity-backed model calls and the final state arrays. -/
theorem scratchCostStepSpace_le (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    {J : Circulation} (s : CostState J) (C U : ℕ) :
    let f := scratchWidthFactor c d
    scratchCostStepSpace solver entry T S c d hproc s C U≤(costStepNumberBase J C U)^(524*f) := by
  let f := scratchWidthFactor c d
  have hf : 1≤f := scratchWidthFactor_pos c d
  let D := costStepNumberBase J C U
  let B := J.m+J.m
  let K := s.roundedInstance C
  let delta := (K.invokePositive (fun L => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) L U)).value
  have hD : J.n+4*J.m+B^10+C+U+8=D := rfl
  have hD8 : 8≤D := by omega
  have hDpos : 0<D := by omega
  have hbase : capacityGraphSpaceBase K (B^10) U≤D := by
    change J.n+2*B+B^10+U+8≤D
    dsimp only [B] at hD ⊢
    omega
  have hP : scratchCapacityPositiveSpace c d K (B^10) U≤D^(260*scratchWidthFactor c d) :=
    (scratchCapacityPositiveSpace_le c d K (B^10) U).trans (Nat.pow_le_pow_left hbase (260*f))
  have hQ : scratchCapacityExtractDualSpace c d K delta (B^10) U≤D^(522*f) :=
    (scratchCapacityExtractDualSpace_le c d K delta (B^10) U).trans (Nat.pow_le_pow_left hbase (522*f))
  change _ ≤ D^(260*f) at hP
  have h260_522 : D^(260*f)≤D^(522*f) := Nat.pow_le_pow_right hDpos (by omega)
  have h64 : 64≤D^2 := Nat.pow_le_pow_left hD8 2
  have hlin : 9+45*J.m+2*J.n≤D^3 := by
    have h : 9+45*J.m+2*J.n≤12*D := by omega
    exact h.trans ((Nat.mul_le_mul_right D (show 12≤D^2 by omega)).trans_eq (pow_succ D 2).symm)
  have h3_522 : D^3≤D^(522*f) := Nat.pow_le_pow_right hDpos (by omega)
  have hlast : 3*D^(522*f)≤D^(523*f) :=
    (Nat.mul_le_mul_right (D^(522*f)) (show 3≤D by omega)).trans ((pow_succ' D (522*f)).symm.le.trans (Nat.pow_le_pow_right hDpos (by omega)))
  have h523_524 : D^(523*f)≤D^(524*f) := Nat.pow_le_pow_right hDpos (by omega)
  change 2+10*J.m+(4+17*B)+scratchCapacityPositiveSpace c d K (B^10) U+
    scratchCapacityExtractDualSpace c d K delta (B^10) U+J.m+2*J.n+3≤D^(524*f)
  have hB : B=J.m+J.m := rfl
  omega

set_option exponentiation.threshold 1024 in
/-- Current data, uniform power and potential bounds, and the single
polynomial space reserve supply the full measured cost-round precondition. -/
theorem scratchCostStep_pre_of_space {w : ℕ} (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    {J : Circulation} (s : CostState J) (C U a state heap : ℕ) (mem : ℕ → ℕ)
    (hgraph : ListAt mem a J.solverWords) (hgraphEnd : a+J.solverWords.length≤heap)
    (hstateEnd : state+3=heap) (hstate : CostStateAt mem state heap s)
    (hf : ∀ e,0≤s.flow e ∧ s.flow e≤J.capacity e) (hC : J.CostsBounded C)
    (hu : ∀ e,J.capacity e≤U) (hm : 0<J.m) (hnU : J.n+1≤U)
    (hpower : s.power≤(costStepNumberBase J C U)^3)
    (hpot : ∀ v,(s.potential v).natAbs≤(costStepNumberBase J C U)^6)
    (hz : ZeroFrom mem heap)
    (hs : heap+(costStepNumberBase J C U)^(524*scratchWidthFactor c d)<2^w) :
    (scratchCostStepContract w solver entry T S c d hproc s C U).pre [a,state,C,U,heap] mem := by
  let f := scratchWidthFactor c d
  have hfactor : 1≤f := scratchWidthFactor_pos c d
  let D := costStepNumberBase J C U
  let B := J.m+J.m
  let N := D^(524*f)
  let Q := (4*J.m+J.n)*B^10
  have hD : J.n+4*J.m+B^10+C+U+8=D := rfl
  have hB : B=J.m+J.m := rfl
  have hD8 : 8≤D := by omega
  have hDpos : 0<D := by omega
  have h1N : D≤N := Nat.le_pow (by omega)
  have h2N : D^2≤N := Nat.pow_le_pow_right hDpos (by omega)
  have h4N : D^4≤N := Nat.pow_le_pow_right hDpos (by omega)
  have h7N : D^7≤N := Nat.pow_le_pow_right hDpos (by omega)
  have hNword : N<2^w := by change heap+N<2^w at hs; omega
  have hmax : J.solverWords.foldr max 0≤D := solverWords_max_le_of_bounds J D (by omega) (by omega)
    (fun e => (hu e).trans (by omega)) (fun e => (hC e).trans (by omega)) (by omega)
  have hfields : J.n+B+U+B^10+2≤D := by omega
  have hC1 : C+1≤D := by omega
  have hU2 : 2*U≤D^2 := by
    have huD : U≤D := by omega
    exact (Nat.mul_le_mul_left 2 huD).trans
      (by simpa only [pow_two] using Nat.mul_le_mul_right D (show 2≤D by omega))
  have hpower2 : 2*s.power≤D^4 := by
    have hp : s.power≤D^3 := hpower
    exact (Nat.mul_le_mul_left 2 hp).trans
      ((Nat.mul_le_mul_right (D^3) (show 2≤D by omega)).trans_eq (pow_succ' D 3).symm)
  have hlabel : (4*J.m+J.n+1)*B^10≤D^2 := by
    simpa only [pow_two] using Nat.mul_le_mul (show 4*J.m+J.n+1≤D by omega) (show B^10≤D by omega)
  have hQ : Q≤D^2 := by
    simpa only [pow_two] using Nat.mul_le_mul (show 4*J.m+J.n≤D by omega) (show B^10≤D by omega)
  have h2_6 : D^2≤D^6 := Nat.pow_le_pow_right hDpos (by omega)
  have hpotBudget : ∀ v,2*((s.potential v).natAbs+Q)≤D^7 := by
    intro v
    have hp : (s.potential v).natAbs≤D^6 := hpot v
    have hlast : 4*D^6≤D^7 :=
      (Nat.mul_le_mul_right (D^6) (show 4≤D by omega)).trans_eq (pow_succ' D 6).symm
    omega
  have hscalar := roundedCost_pre_of_cost_bounds s C U heap mem hC hpower hpot hz (by
    apply lt_of_le_of_lt _ hs
    apply Nat.add_le_add_left
    exact Nat.pow_le_pow_right hDpos (by change 524≤524*f; omega))
  have hspace := scratchCostStepSpace_le solver entry T S c d hproc s C U
  refine ⟨a,state,heap,rfl,hgraph,hgraphEnd,hstateEnd,hstate,hf,hC,hu,hm,hnU,?_,
    (hfields.trans h1N).trans_lt hNword,(hC1.trans h1N).trans_lt hNword,
    (hpower2.trans h4N).trans_lt hNword,(hU2.trans h2N).trans_lt hNword,
    (hlabel.trans h2N).trans_lt hNword,(fun v => ((hpotBudget v).trans h7N).trans_lt hNword),hscalar,hz,?_⟩
  · intro x hx
    exact ((Link.elem_le_foldr_max hx).trans hmax |>.trans h1N).trans_lt hNword
  · exact (Nat.add_le_add_left hspace heap).trans_lt hs

end MinCostFlow.Final
