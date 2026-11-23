module

public import MinCostFlow.IPM.Machine.SolverFinish
public import MinCostFlow.IPM.Machine.ConnectedSolverInitialize
public import MinCostFlow.IPM.Machine.ConnectedRoundLink
import MinCostFlow.IPM.Machine.ConnectedRefresh
import MinCostFlow.IPM.EdgeOnlyMachine
import Mathlib.Tactic

/-!
# Searching and rounding on the connected graph

The same target search runs on the connected augmentation. The
rounding call then extracts the original circulation prefix.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling Rounding

/-- The common numeric bound is the machine's exact penalty word. -/
theorem connectedSolverAugmented_numbers (J : Circulation) (hm : 0 < J.m)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e, J.capacity e ≤ J.m^40) :
    let U := solverCapacityBound J.m
    let V := solverPenalty J.m
    NumbersBounded J.toInstance (U:ℝ) ∧ NumbersBounded (solverConnectedAugmented J) (V:ℝ) ∧
      2*J.toInstance.m*(U:ℝ) < (V:ℝ) ∧
      2*J.toInstance.m*(U:ℝ)^2 < (V:ℝ) := by
  dsimp only
  let U := solverCapacityBound J.m
  let V := solverPenalty J.m
  have hU : 2 ≤ U := le_max_left _ _
  have hUreal : (2:ℝ) ≤ U := by exact_mod_cast hU
  have hEq : (V:ℝ) = 4*J.toInstance.m*(U:ℝ)^2 := by
    simp [U,V,solverPenalty,Circulation.toInstance_m]
  obtain ⟨hCap,hCost⟩ := solverCapacityBound_input J hm hc hu
  have hNums := circulation_numbersBounded J U hCap hCost
  have hVn : (0:ℝ) ≤ V := Nat.cast_nonneg _
  have hPen : |((V:ℤ):ℝ)| ≤ 4*J.toInstance.m*(U:ℝ)^2 := by
    rw [Int.cast_natCast,abs_of_nonneg hVn,hEq]
  have hM : 0 < J.toInstance.m := by simpa only [Circulation.toInstance_m] using hm
  have hMreal : 0 < (J.toInstance.m:ℝ) := Nat.cast_pos.mpr hM
  have hU1 : (1 : ℝ) ≤ U := by linarith only [hUreal]
  have h := connectedInitialInstance_numbers J.toInstance U (V:ℤ) hM hU1 hNums hPen
  have hU0 : (0 : ℝ) ≤ U := by positivity
  have hpow : (U : ℝ) ≤ (U : ℝ)^2 := by
    simpa only [one_mul, pow_two] using mul_le_mul_of_nonneg_right hU1 hU0
  have hmul := mul_le_mul_of_nonneg_left hpow (show (0 : ℝ) ≤ 2*J.toInstance.m by positivity)
  have hsq : 0 < (J.toInstance.m : ℝ)*(U : ℝ)^2 := by positivity
  refine ⟨hNums, ⟨fun v => (h.1 v).trans ?_, fun e => ?_⟩, ?_, ?_⟩
  · nlinarith only [hmul, hsq, hEq]
  · rw [hEq]
    exact h.2 e
  · nlinarith only [hmul, hsq, hEq]
  · nlinarith only [hsq, hEq]

set_option maxHeartbeats 650000 in
set_option maxRecDepth 4096 in
/-- With initialized inputs and `SolverForestResources` (`L`-dependent rate and
space, `(w, L)`-dependent allocation), the linked solver's last two calls write the
exact bounded-circulation optimum. -/
theorem connectedForestSolverFinish_runs_on {w search recover : ℕ} {p : Program}
    (resources : SolverForestResources) (entry : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : DynForest) (hD : D.IsSpec)
    (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (hm : 0<J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) resources.qualityExponent≤w)
    (hDS : SolverQualityForestDataStructuresAt w p entry resources (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModule search entry.cycleInit entry.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entry.forestInit entry.forestOp))
    (old : EpochLayout) (qp source heap dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hReady : let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let F := ipmQualityMinRatioFormat I.m V resources.qualityExponent hw
      old.exponent=F.rangeExponent ∧
      TargetFixedInputs F I old qp qp heap (1/4)
        ((25/32:ℝ)*((1/(2:ℝ)^resources.qualityExponent)*Num.IPM.alphaPrime I.m V/32)^2/50)
        (Num.IPM.alphaPrime I.m V) mem ∧
      TargetStageFlow F I old.exponent source heap mem ∧
      (∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
        (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e) ∧
      ZeroLowerAt mem old.graph I ∧ ZeroFrom mem heap)
    (hn : (solverConnectedAugmented J).n<2^w) (hV : 2≤solverPenalty J.m)
    (hRadius : 2*((solverConnectedAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverConnectedAugmented J).m (solverPenalty J.m) resources.qualityExponent<2^w)
    (hCap : ∀ e,J.capacity e<2^w) (hDest : dest+J.m≤heap)
    (hSpace : let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      heap+solverQualityForestSearchReserve resources I V hw+solverQualityForestRecoveryReserve resources I V J.m<2^w) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let F := ipmQualityMinRatioFormat I.m V resources.qualityExponent hw
    let radius := I.m*V^2
    let limit := targetTestLimit I.m V resources.qualityExponent
    ∃ out final c, Runs w p ω (solverSearchRecoverBody search recover)
      (startState (targetOffsetPacket old F I 0 qp source heap limit radius++
        [targetSearchRounds radius,I.n,J.m,dest]) mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧
      heap≤out ∧ out≤heap+solverQualityForestSearchReserve resources I V hw+solverQualityForestRecoveryReserve resources I V J.m ∧
      ZeroFrom final.mem out ∧ (∀ a<dest,final.mem a=mem a) ∧
      c≤solverQualityForestSearchCharge resources I V hw+solverQualityForestRecoveryCharge resources I V J.m+50 := by
  dsimp only at hReady hSpace ⊢
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let F := ipmQualityMinRatioFormat I.m V resources.qualityExponent hw
  let k := resources.qualityExponent
  let K := (V:ℤ)
  let U := solverCapacityBound J.m
  let radius := I.m*V^2
  let limit := targetTestLimit I.m V k
  let searchSpace := solverQualityForestSearchReserve resources I V hw
  let roundSpace := solverQualityForestRecoveryReserve resources I V J.m
  let searchCost := solverQualityForestSearchCharge resources I V hw
  let roundCost := solverQualityForestRecoveryCharge resources I V J.m
  let L := F.limbs
  let A := resources.forestOpSpace L I.n I.m
  change heap+searchSpace+roundSpace<2^w at hSpace
  obtain ⟨hE,hFixed,hFlow,hHalf,hRows,hZero⟩ := hReady
  change TargetFixedInputs F I old qp qp heap (1/4)
    ((25/32:ℝ)*((1/(2:ℝ)^k)*Num.IPM.alphaPrime I.m V/32)^2/50) (Num.IPM.alphaPrime I.m V) mem at hFixed
  have hI : I.IsValid := connectedInitialInstance_valid J.toInstance K J.toInstance_valid
  obtain ⟨hNums,hBounds,hPenalty,hPenaltySq⟩ := connectedSolverAugmented_numbers J hm hc hu
  have hM : 0 < I.m := hm.trans_le (connectedInitial_circulation_m_ge J hp K)
  have hSize : 2≤I.m*V := hV.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right V (show 1≤I.m from hM))
  have hW := ipm_quality_parameter_words_fit I.m V resources.qualityExponent hw
  have hMw : I.m<2^w := (show I.m≤20*I.m by omega).trans_lt hW.2.2.2.2.2.1
  have hmw : J.m<2^w := (connectedInitial_circulation_m_ge J hp K).trans_lt hMw
  have hRadius' : 2*radius<2^w := hRadius
  have hRound : targetSearchRounds radius<2^w :=
    ((Nat.size_le).mpr hRadius').trans_lt Nat.lt_two_pow_self
  have hSource : source≤heap := (Nat.le_add_right _ _).trans hFlow.1
  have hsp : heap+searchSpace<2^w :=
    (Nat.le_add_right _ _).trans_lt hSpace
  have hAllocSearch : heap+targetSearchSpace F I.m V k old.exponent (resources.cycleSpace I.n I.m)<2^w := by
    rw [hE]
    exact hsp
  have hWord := solverTargetPacket_words I V k F.rangeExponent (resources.cycleSpace I.n I.m)
    F old qp source heap mem _ _ hFixed hSource hMw hE F.parameters_fit.2.2 hRadius hLimit hsp
  have hLower : ∀ e,0≤(I.edge e).lower := fun e => (hRows.1 e).1.ge
  have hSearchEntry : p.procs[search]?=some (targetSearchBody (search+1)) := hSearch.head
  have hRecoverEntry : p.procs[recover]?=some (roundExtractBody (recover+6) (recover+1) (recover+7)) := hRecover.head
  refine solverSearchRecover_runs hSearchEntry hRecoverEntry F J I old qp source heap limit radius dest mem pos ω
    searchSpace roundSpace searchCost roundCost hSpace ?_ ?_ (by omega)
  · have hConn : MinRatioGraphConnected (namedInstance I) :=
      (connectedInitial_refreshes J.toInstance K J.toInstance_valid [] (by simp)).2
    obtain ⟨out,final,c,z,fstar,hRun,hStar,hValue,hResult,hBit,hOut,hCost⟩ :=
      solverSearchModule_runs_widened_edgeOnly I V k hw C resources.cycleRate (resources.cycleAllocation I.n I.m) RC hSearch
        hDS.cycleModel hConn hDS.cycleMachine old qp source heap (resources.cycleSpace I.n I.m) mem pos ω hE hFixed hFlow
        hHalf hWord hRadius hRound hDS.cycleBound hLimit hAllocSearch hZero hM (by omega) hSize hI hBounds hLower
    rw [hE] at hOut hCost
    exact ⟨out,final,c,hRun,⟨z,fstar,hStar,hValue,hResult,hBit⟩,hOut,hCost⟩
  · intro out mid pos' hOut hResult'
    obtain ⟨z,fstar,hStar,hValue,hResult,hBit⟩ := hResult'
    have hLo : heap≤out := by have h := hResult.1; omega
    have hFrame : ∀ a<heap,mid a=mem a := hResult.2.2.2.1
    have hFixed' := hFixed.frozen hFrame hLo
    have hSource' : mid (out-2)<2^w := by
      have hs := (hResult.2.2.2.2.2.2 hBit).1.1
      have hOutW := hResult.2.1
      omega
    have hRows' : ZeroLowerAt mid old.graph I := ⟨hRows.1,hRows.2.1,hFixed'.rows⟩
    have hCost' : RoundCostsAt I mid old.cost 4 L := by
      intro e
      apply ScalarAt.rat
      rw [Rat.cast_intCast]
      exact hFixed'.cost e
    have hUnit : RatAt mid old.one 4 L F.fmt.precision 1 := by
      apply ScalarAt.rat
      rw [Rat.cast_one]
      exact hFixed'.one
    have hCostEnd := hFixed'.arrays old.cost (by simp)
    have hOneEnd := hFixed'.scalars old.one (by simp)
    have hOutW := hResult.2.1
    have hGraphW : old.graph<2^w := (Nat.le_add_right _ _).trans_lt (hFixed'.rowsEnd.trans_lt hOutW)
    have hCostW : old.cost<2^w := (Nat.le_add_right _ _).trans_lt (hCostEnd.trans_lt hOutW)
    have hOneW : old.one<2^w := (Nat.le_add_right _ _).trans_lt (hOneEnd.trans_lt hOutW)
    have hDestW : dest<2^w := by omega
    have hL : L<2^w := F.parameters_fit.1
    have hP : F.fmt.precision<2^w := F.parameters_fit.2.1
    have hWords : ∀ a∈[I.n,I.m,old.graph,old.cost,mid (out-2),L,F.fmt.precision,old.one,out,dest,J.m],a<2^w := by
      intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hn
      · exact hMw
      · exact hGraphW
      · exact hCostW
      · exact hSource'
      · exact hL
      · exact hP
      · exact hOneW
      · exact hOutW
      · exact hDestW
      · exact hmw
    have hAlloc j (hj : j<6) args := hDS.forestOpBound j hj args
    let r := out+I.m*L
    have hRes : r+roundMachineSpace (resources.forestAllocation w L I.n I.m 6 [I.n,L,F.fmt.precision,r]) A L I.m+
        recoverScanSpace L J.m≤out+roundSpace := by
      change _≤out+(I.m*L+roundMachineSpace (resources.forestInitSpace I.n I.m) A L I.m+
        recoverScanSpace L J.m)
      have hi : resources.forestAllocation w L I.n I.m 6 [I.n,L,F.fmt.precision,r]≤resources.forestInitSpace I.n I.m :=
        hDS.forestInitBound r
      have hr : roundMachineSpace (resources.forestAllocation w L I.n I.m 6 [I.n,L,F.fmt.precision,r]) A L I.m ≤
          roundMachineSpace (resources.forestInitSpace I.n I.m) A L I.m :=
        Nat.add_le_add_right hi _
      have he := Nat.add_le_add_right (Nat.add_le_add_left hr r) (recoverScanSpace L J.m)
      simpa only [r,Nat.add_assoc] using he
    have hRoom : r+roundMachineSpace (resources.forestAllocation w L I.n I.m 6 [I.n,L,F.fmt.precision,r]) A L I.m+
        recoverScanSpace L J.m<2^w := hRes.trans_lt ((Nat.add_le_add_right hOut roundSpace).trans_lt hSpace)
    have hLarge : 2*J.toInstance.m*(U:ℝ)<(K:ℝ) := by
      change 2*J.toInstance.m*(U:ℝ)<((V:ℤ):ℝ)
      rw [Int.cast_natCast]
      exact hPenalty
    obtain ⟨last,final,c,hRun,hOpt,hLast,hUpper,hZero',hFrame',hC⟩ :=
      connectedRoundModule_fromSearch D hD (fun n => resources.forestRate n L) (resources.forestAllocation w L I.n I.m) RD
        J K hp U V k hm (by omega) hNums (by simpa only [K, Int.cast_natCast] using hPenaltySq) hLarge
        hw hBounds hRecover hDS.forestMachine
        (fun b u v a endPtr => ⟨hAlloc 0 (by decide) _,hAlloc 4 (by decide) _,hAlloc 3 (by decide) _,
          hAlloc 2 (by decide) _,hAlloc 1 (by decide) _,hAlloc 5 (by decide) _⟩)
        old.exponent heap out old.graph old.cost old.one dest mem mid pos' ω z fstar hStar hValue
        hResult hBit hWords hRows' hCost' hUnit hCostEnd hFixed'.rowsEnd hOneEnd hCap (by omega) hRoom
    exact ⟨last,final,c,hRun,hOpt,hLast,hUpper.trans hRes,hZero',hFrame',hC⟩

/-- With the initialized inputs in memory, the linked solver's last
two calls write the exact bounded-circulation optimum. -/
theorem connectedSolverFinish_runs_on {w search recover : ℕ} {p : Program}
    (resources : SolverResources) (entry : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : DynForest) (hD : D.IsSpec)
    (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (hm : 0<J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) resources.qualityExponent≤w)
    (hDS : SolverQualityConnectedDataStructuresAt w p entry resources (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModule search entry.cycleInit entry.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entry.forestInit entry.forestOp))
    (old : EpochLayout) (qp source heap dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hReady : let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let F := ipmQualityMinRatioFormat I.m V resources.qualityExponent hw
      old.exponent=F.rangeExponent ∧
      TargetFixedInputs F I old qp qp heap (1/4)
        ((25/32:ℝ)*((1/(2:ℝ)^resources.qualityExponent)*Num.IPM.alphaPrime I.m V/32)^2/50)
        (Num.IPM.alphaPrime I.m V) mem ∧
      TargetStageFlow F I old.exponent source heap mem ∧
      (∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
        (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e) ∧
      ZeroLowerAt mem old.graph I ∧ ZeroFrom mem heap)
    (hn : (solverConnectedAugmented J).n<2^w) (hV : 2≤solverPenalty J.m)
    (hRadius : 2*((solverConnectedAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverConnectedAugmented J).m (solverPenalty J.m) resources.qualityExponent<2^w)
    (hCap : ∀ e,J.capacity e<2^w) (hDest : dest+J.m≤heap)
    (hSpace : let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      heap+solverQualitySearchReserve resources I V hw+solverQualityRecoveryReserve resources I V J.m<2^w) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let F := ipmQualityMinRatioFormat I.m V resources.qualityExponent hw
    let radius := I.m*V^2
    let limit := targetTestLimit I.m V resources.qualityExponent
    ∃ out final c, Runs w p ω (solverSearchRecoverBody search recover)
      (startState (targetOffsetPacket old F I 0 qp source heap limit radius++
        [targetSearchRounds radius,I.n,J.m,dest]) mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧
      heap≤out ∧ out≤heap+solverQualitySearchReserve resources I V hw+solverQualityRecoveryReserve resources I V J.m ∧
      ZeroFrom final.mem out ∧ (∀ a<dest,final.mem a=mem a) ∧
      c≤solverQualitySearchCharge resources I V hw+solverQualityRecoveryCharge resources I V J.m+50 :=
  connectedForestSolverFinish_runs_on resources.toForestResources entry C D hD RC RD J hm hp hc hu hw
    hDS.toForest hSearch hRecover old qp source heap dest mem pos ω hReady hn hV hRadius hLimit hCap
    hDest hSpace

/-- Run the search and rounding modules on the connected augmentation, returning the exact
minimum-cost circulation within the explicit time and workspace charges. -/
theorem connectedSolverFinish_runs {w search recover : ℕ} {p : Program}
    (resources : SolverResources) (entry : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : DynForest) (hD : D.IsSpec)
    (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (hm : 0<J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) resources.qualityExponent≤w)
    (hDS : SolverQualityDataStructuresAt w p entry resources (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModule search entry.cycleInit entry.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entry.forestInit entry.forestOp))
    (old : EpochLayout) (qp source heap dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hReady : let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let F := ipmQualityMinRatioFormat I.m V resources.qualityExponent hw
      old.exponent=F.rangeExponent ∧
      TargetFixedInputs F I old qp qp heap (1/4)
        ((25/32:ℝ)*((1/(2:ℝ)^resources.qualityExponent)*Num.IPM.alphaPrime I.m V/32)^2/50)
        (Num.IPM.alphaPrime I.m V) mem ∧
      TargetStageFlow F I old.exponent source heap mem ∧
      (∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
        (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e) ∧
      ZeroLowerAt mem old.graph I ∧ ZeroFrom mem heap)
    (hn : (solverConnectedAugmented J).n<2^w) (hV : 2≤solverPenalty J.m)
    (hRadius : 2*((solverConnectedAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverConnectedAugmented J).m (solverPenalty J.m) resources.qualityExponent<2^w)
    (hCap : ∀ e,J.capacity e<2^w) (hDest : dest+J.m≤heap)
    (hSpace : let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      heap+solverQualitySearchReserve resources I V hw+solverQualityRecoveryReserve resources I V J.m<2^w) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let F := ipmQualityMinRatioFormat I.m V resources.qualityExponent hw
    let radius := I.m*V^2
    let limit := targetTestLimit I.m V resources.qualityExponent
    ∃ out final c, Runs w p ω (solverSearchRecoverBody search recover)
      (startState (targetOffsetPacket old F I 0 qp source heap limit radius++
        [targetSearchRounds radius,I.n,J.m,dest]) mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧
      heap≤out ∧ out≤heap+solverQualitySearchReserve resources I V hw+solverQualityRecoveryReserve resources I V J.m ∧
      ZeroFrom final.mem out ∧ (∀ a<dest,final.mem a=mem a) ∧
      c≤solverQualitySearchCharge resources I V hw+solverQualityRecoveryCharge resources I V J.m+50 :=
  connectedSolverFinish_runs_on resources entry C D hD RC RD J hm hp hc hu hw hDS.toConnected
    hSearch hRecover old qp source heap dest mem pos ω hReady hn hV hRadius hLimit hCap hDest hSpace

/-- `V`-passing variant of `connectedForestSolverFinish_runs_on`. -/
theorem connectedForestSolverFinishWithV_runs_on {w search recover : ℕ} {p : Program}
    (resources : SolverForestResources) (entry : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : DynForest) (hD : D.IsSpec)
    (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (hm : 0<J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) resources.qualityExponent≤w)
    (hDS : SolverQualityForestDataStructuresWithVAt w p entry resources (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModuleWithV search entry.cycleInit entry.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entry.forestInit entry.forestOp))
    (old : EpochLayout) (qp source heap dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hReady : let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let F := ipmQualityMinRatioFormat I.m V resources.qualityExponent hw
      old.exponent=F.rangeExponent ∧
      TargetFixedInputs F I old qp qp heap (1/4)
        ((25/32:ℝ)*((1/(2:ℝ)^resources.qualityExponent)*Num.IPM.alphaPrime I.m V/32)^2/50)
        (Num.IPM.alphaPrime I.m V) mem ∧
      TargetStageFlow F I old.exponent source heap mem ∧
      (∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
        (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e) ∧
      ZeroLowerAt mem old.graph I ∧ ZeroFrom mem heap)
    (hn : (solverConnectedAugmented J).n<2^w) (hV : 2≤solverPenalty J.m)
    (hRadius : 2*((solverConnectedAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverConnectedAugmented J).m (solverPenalty J.m) resources.qualityExponent<2^w)
    (hCap : ∀ e,J.capacity e<2^w) (hDest : dest+J.m≤heap)
    (hSpace : let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      heap+solverQualityForestSearchReserve resources I V hw+solverQualityForestRecoveryReserve resources I V J.m<2^w) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let F := ipmQualityMinRatioFormat I.m V resources.qualityExponent hw
    let radius := I.m*V^2
    let limit := targetTestLimit I.m V resources.qualityExponent
    ∃ out final c, Runs w p ω (solverSearchRecoverBodyWithV search recover)
      (startState (targetOffsetPacket old F I 0 qp source heap limit radius++
        [targetSearchRounds radius,I.n,J.m,dest,V]) mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧
      heap≤out ∧ out≤heap+solverQualityForestSearchReserve resources I V hw+solverQualityForestRecoveryReserve resources I V J.m ∧
      ZeroFrom final.mem out ∧ (∀ a<dest,final.mem a=mem a) ∧
      c≤solverQualityForestSearchCharge resources I V hw+solverQualityForestRecoveryCharge resources I V J.m+50 := by
  dsimp only at hReady hSpace ⊢
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let F := ipmQualityMinRatioFormat I.m V resources.qualityExponent hw
  let k := resources.qualityExponent
  let K := (V:ℤ)
  let U := solverCapacityBound J.m
  let radius := I.m*V^2
  let limit := targetTestLimit I.m V k
  let searchSpace := solverQualityForestSearchReserve resources I V hw
  let roundSpace := solverQualityForestRecoveryReserve resources I V J.m
  let searchCost := solverQualityForestSearchCharge resources I V hw
  let roundCost := solverQualityForestRecoveryCharge resources I V J.m
  let L := F.limbs
  let A := resources.forestOpSpace L I.n I.m
  change heap+searchSpace+roundSpace<2^w at hSpace
  obtain ⟨hE,hFixed,hFlow,hHalf,hRows,hZero⟩ := hReady
  change TargetFixedInputs F I old qp qp heap (1/4)
    ((25/32:ℝ)*((1/(2:ℝ)^k)*Num.IPM.alphaPrime I.m V/32)^2/50) (Num.IPM.alphaPrime I.m V) mem at hFixed
  have hI : I.IsValid := connectedInitialInstance_valid J.toInstance K J.toInstance_valid
  obtain ⟨hNums,hBounds,hPenalty,hPenaltySq⟩ := connectedSolverAugmented_numbers J hm hc hu
  have hM : 0 < I.m := hm.trans_le (connectedInitial_circulation_m_ge J hp K)
  have hSize : 2≤I.m*V := hV.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right V (show 1≤I.m from hM))
  have hW := ipm_quality_parameter_words_fit I.m V resources.qualityExponent hw
  have hVw : V<2^w := hW.2.2.2.2.2.2.2
  have hMw : I.m<2^w := (show I.m≤20*I.m by omega).trans_lt hW.2.2.2.2.2.1
  have hmw : J.m<2^w := (connectedInitial_circulation_m_ge J hp K).trans_lt hMw
  have hRadius' : 2*radius<2^w := hRadius
  have hRound : targetSearchRounds radius<2^w :=
    ((Nat.size_le).mpr hRadius').trans_lt Nat.lt_two_pow_self
  have hSource : source≤heap := (Nat.le_add_right _ _).trans hFlow.1
  have hsp : heap+searchSpace<2^w :=
    (Nat.le_add_right _ _).trans_lt hSpace
  have hAllocSearch : heap+targetSearchSpace F I.m V k old.exponent (resources.cycleSpace I.n I.m)<2^w := by
    rw [hE]
    exact hsp
  have hWord := solverTargetPacket_words I V k F.rangeExponent (resources.cycleSpace I.n I.m)
    F old qp source heap mem _ _ hFixed hSource hMw hE F.parameters_fit.2.2 hRadius hLimit hsp
  have hLower : ∀ e,0≤(I.edge e).lower := fun e => (hRows.1 e).1.ge
  have hSearchEntry : p.procs[search]?=some (targetSearchBodyWithV (search+1)) := hSearch.head
  have hRecoverEntry : p.procs[recover]?=some (roundExtractBody (recover+6) (recover+1) (recover+7)) := hRecover.head
  refine solverSearchRecoverWithV_runs hSearchEntry hRecoverEntry F J I old qp source heap limit radius dest V mem pos ω
    searchSpace roundSpace searchCost roundCost hSpace hVw ?_ ?_ (by omega)
  · have hConn : MinRatioGraphConnected (namedInstance I) :=
      (connectedInitial_refreshes J.toInstance K J.toInstance_valid [] (by simp)).2
    obtain ⟨out,final,c,z,fstar,hRun,hStar,hValue,hResult,hBit,hOut,hCost⟩ :=
      solverSearchModuleWithV_runs_widened_edgeOnly I V k V hw C resources.cycleRate (resources.cycleAllocation I.n I.m) RC hSearch
        hDS.cycleModel hConn hDS.cycleMachine old qp source heap (resources.cycleSpace I.n I.m) mem pos ω hE hFixed hFlow
        hHalf hWord hVw hRadius hRound hDS.cycleBound hLimit hAllocSearch hZero hM (by omega) hSize hI hBounds hLower
    rw [hE] at hOut hCost
    exact ⟨out,final,c,hRun,⟨z,fstar,hStar,hValue,hResult,hBit⟩,hOut,hCost⟩
  · intro out mid pos' hOut hResult'
    obtain ⟨z,fstar,hStar,hValue,hResult,hBit⟩ := hResult'
    have hLo : heap≤out := by have h := hResult.1; omega
    have hFrame : ∀ a<heap,mid a=mem a := hResult.2.2.2.1
    have hFixed' := hFixed.frozen hFrame hLo
    have hSource' : mid (out-2)<2^w := by
      have hs := (hResult.2.2.2.2.2.2 hBit).1.1
      have hOutW := hResult.2.1
      omega
    have hRows' : ZeroLowerAt mid old.graph I := ⟨hRows.1,hRows.2.1,hFixed'.rows⟩
    have hCost' : RoundCostsAt I mid old.cost 4 L := by
      intro e
      apply ScalarAt.rat
      rw [Rat.cast_intCast]
      exact hFixed'.cost e
    have hUnit : RatAt mid old.one 4 L F.fmt.precision 1 := by
      apply ScalarAt.rat
      rw [Rat.cast_one]
      exact hFixed'.one
    have hCostEnd := hFixed'.arrays old.cost (by simp)
    have hOneEnd := hFixed'.scalars old.one (by simp)
    have hOutW := hResult.2.1
    have hGraphW : old.graph<2^w := (Nat.le_add_right _ _).trans_lt (hFixed'.rowsEnd.trans_lt hOutW)
    have hCostW : old.cost<2^w := (Nat.le_add_right _ _).trans_lt (hCostEnd.trans_lt hOutW)
    have hOneW : old.one<2^w := (Nat.le_add_right _ _).trans_lt (hOneEnd.trans_lt hOutW)
    have hDestW : dest<2^w := by omega
    have hL : L<2^w := F.parameters_fit.1
    have hP : F.fmt.precision<2^w := F.parameters_fit.2.1
    have hWords : ∀ a∈[I.n,I.m,old.graph,old.cost,mid (out-2),L,F.fmt.precision,old.one,out,dest,J.m],a<2^w := by
      intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hn
      · exact hMw
      · exact hGraphW
      · exact hCostW
      · exact hSource'
      · exact hL
      · exact hP
      · exact hOneW
      · exact hOutW
      · exact hDestW
      · exact hmw
    have hAlloc j (hj : j<6) args := hDS.forestOpBound j hj args
    let r := out+I.m*L
    have hRes : r+roundMachineSpace (resources.forestAllocation w L I.n I.m 6 [I.n,L,F.fmt.precision,r]) A L I.m+
        recoverScanSpace L J.m≤out+roundSpace := by
      change _≤out+(I.m*L+roundMachineSpace (resources.forestInitSpace I.n I.m) A L I.m+
        recoverScanSpace L J.m)
      have hi : resources.forestAllocation w L I.n I.m 6 [I.n,L,F.fmt.precision,r]≤resources.forestInitSpace I.n I.m :=
        hDS.forestInitBound r
      have hr : roundMachineSpace (resources.forestAllocation w L I.n I.m 6 [I.n,L,F.fmt.precision,r]) A L I.m ≤
          roundMachineSpace (resources.forestInitSpace I.n I.m) A L I.m :=
        Nat.add_le_add_right hi _
      have he := Nat.add_le_add_right (Nat.add_le_add_left hr r) (recoverScanSpace L J.m)
      simpa only [r,Nat.add_assoc] using he
    have hRoom : r+roundMachineSpace (resources.forestAllocation w L I.n I.m 6 [I.n,L,F.fmt.precision,r]) A L I.m+
        recoverScanSpace L J.m<2^w := hRes.trans_lt ((Nat.add_le_add_right hOut roundSpace).trans_lt hSpace)
    have hLarge : 2*J.toInstance.m*(U:ℝ)<(K:ℝ) := by
      change 2*J.toInstance.m*(U:ℝ)<((V:ℤ):ℝ)
      rw [Int.cast_natCast]
      exact hPenalty
    obtain ⟨last,final,c,hRun,hOpt,hLast,hUpper,hZero',hFrame',hC⟩ :=
      connectedRoundModule_fromSearch D hD (fun n => resources.forestRate n L) (resources.forestAllocation w L I.n I.m) RD
        J K hp U V k hm (by omega) hNums (by simpa only [K, Int.cast_natCast] using hPenaltySq) hLarge
        hw hBounds hRecover hDS.forestMachine
        (fun b u v a endPtr => ⟨hAlloc 0 (by decide) _,hAlloc 4 (by decide) _,hAlloc 3 (by decide) _,
          hAlloc 2 (by decide) _,hAlloc 1 (by decide) _,hAlloc 5 (by decide) _⟩)
        old.exponent heap out old.graph old.cost old.one dest mem mid pos' ω z fstar hStar hValue
        hResult hBit hWords hRows' hCost' hUnit hCostEnd hFixed'.rowsEnd hOneEnd hCap (by omega) hRoom
    exact ⟨last,final,c,hRun,hOpt,hLast,hUpper.trans hRes,hZero',hFrame',hC⟩

/-- `V`-passing variant of `connectedSolverFinish_runs_on`. -/
theorem connectedSolverFinishWithV_runs_on {w search recover : ℕ} {p : Program}
    (resources : SolverResources) (entry : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : DynForest) (hD : D.IsSpec)
    (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (hm : 0<J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) resources.qualityExponent≤w)
    (hDS : SolverQualityConnectedDataStructuresWithVAt w p entry resources (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModuleWithV search entry.cycleInit entry.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entry.forestInit entry.forestOp))
    (old : EpochLayout) (qp source heap dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hReady : let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let F := ipmQualityMinRatioFormat I.m V resources.qualityExponent hw
      old.exponent=F.rangeExponent ∧
      TargetFixedInputs F I old qp qp heap (1/4)
        ((25/32:ℝ)*((1/(2:ℝ)^resources.qualityExponent)*Num.IPM.alphaPrime I.m V/32)^2/50)
        (Num.IPM.alphaPrime I.m V) mem ∧
      TargetStageFlow F I old.exponent source heap mem ∧
      (∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
        (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e) ∧
      ZeroLowerAt mem old.graph I ∧ ZeroFrom mem heap)
    (hn : (solverConnectedAugmented J).n<2^w) (hV : 2≤solverPenalty J.m)
    (hRadius : 2*((solverConnectedAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverConnectedAugmented J).m (solverPenalty J.m) resources.qualityExponent<2^w)
    (hCap : ∀ e,J.capacity e<2^w) (hDest : dest+J.m≤heap)
    (hSpace : let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      heap+solverQualitySearchReserve resources I V hw+solverQualityRecoveryReserve resources I V J.m<2^w) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let F := ipmQualityMinRatioFormat I.m V resources.qualityExponent hw
    let radius := I.m*V^2
    let limit := targetTestLimit I.m V resources.qualityExponent
    ∃ out final c, Runs w p ω (solverSearchRecoverBodyWithV search recover)
      (startState (targetOffsetPacket old F I 0 qp source heap limit radius++
        [targetSearchRounds radius,I.n,J.m,dest,V]) mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧
      heap≤out ∧ out≤heap+solverQualitySearchReserve resources I V hw+solverQualityRecoveryReserve resources I V J.m ∧
      ZeroFrom final.mem out ∧ (∀ a<dest,final.mem a=mem a) ∧
      c≤solverQualitySearchCharge resources I V hw+solverQualityRecoveryCharge resources I V J.m+50 :=
  connectedForestSolverFinishWithV_runs_on resources.toForestResources entry C D hD RC RD J hm hp hc hu
    hw hDS.toForest hSearch hRecover old qp source heap dest mem pos ω hReady hn hV hRadius hLimit
    hCap hDest hSpace

/-- `V`-passing variant of `connectedSolverFinish_runs`. -/
theorem connectedSolverFinishWithV_runs {w search recover : ℕ} {p : Program}
    (resources : SolverResources) (entry : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : DynForest) (hD : D.IsSpec)
    (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (hm : 0<J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) resources.qualityExponent≤w)
    (hDS : SolverQualityDataStructuresWithVAt w p entry resources (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModuleWithV search entry.cycleInit entry.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entry.forestInit entry.forestOp))
    (old : EpochLayout) (qp source heap dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hReady : let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let F := ipmQualityMinRatioFormat I.m V resources.qualityExponent hw
      old.exponent=F.rangeExponent ∧
      TargetFixedInputs F I old qp qp heap (1/4)
        ((25/32:ℝ)*((1/(2:ℝ)^resources.qualityExponent)*Num.IPM.alphaPrime I.m V/32)^2/50)
        (Num.IPM.alphaPrime I.m V) mem ∧
      TargetStageFlow F I old.exponent source heap mem ∧
      (∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
        (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e) ∧
      ZeroLowerAt mem old.graph I ∧ ZeroFrom mem heap)
    (hn : (solverConnectedAugmented J).n<2^w) (hV : 2≤solverPenalty J.m)
    (hRadius : 2*((solverConnectedAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverConnectedAugmented J).m (solverPenalty J.m) resources.qualityExponent<2^w)
    (hCap : ∀ e,J.capacity e<2^w) (hDest : dest+J.m≤heap)
    (hSpace : let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      heap+solverQualitySearchReserve resources I V hw+solverQualityRecoveryReserve resources I V J.m<2^w) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let F := ipmQualityMinRatioFormat I.m V resources.qualityExponent hw
    let radius := I.m*V^2
    let limit := targetTestLimit I.m V resources.qualityExponent
    ∃ out final c, Runs w p ω (solverSearchRecoverBodyWithV search recover)
      (startState (targetOffsetPacket old F I 0 qp source heap limit radius++
        [targetSearchRounds radius,I.n,J.m,dest,V]) mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧
      heap≤out ∧ out≤heap+solverQualitySearchReserve resources I V hw+solverQualityRecoveryReserve resources I V J.m ∧
      ZeroFrom final.mem out ∧ (∀ a<dest,final.mem a=mem a) ∧
      c≤solverQualitySearchCharge resources I V hw+solverQualityRecoveryCharge resources I V J.m+50 :=
  connectedSolverFinishWithV_runs_on resources entry C D hD RC RD J hm hp hc hu hw hDS.toConnected
    hSearch hRecover old qp source heap dest mem pos ω hReady hn hV hRadius hLimit hCap hDest hSpace

end MinCostFlow.IPM.Machine
