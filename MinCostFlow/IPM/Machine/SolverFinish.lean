module

public import MinCostFlow.IPM.Machine.SolverSearchRecover
public import MinCostFlow.IPM.Machine.SolverDataStructures
public import MinCostFlow.IPM.Machine.SolverSearchHandoff
public import MinCostFlow.IPM.Machine.SolverSearchLinkWithV
import Mathlib.Tactic
import MinCostFlow.IPM.InitialDomain

/-!
# From the initial target packet to the integral output

The two linked data structures provide the only parameter
operations. The accepted target result freezes the original
coefficient tables and provides the exact dyadic flow for recovery.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding Scaling

/-- Width of every radius-independent and radius-dependent item in the
search packet. Its array reservations fit in the full search workspace. -/
theorem solverTargetPacket_words {w : ℕ} (I : Instance) (V k E B : ℕ)
    (F : MinRatioFormat w) (old : EpochLayout) (qp source heap : ℕ) (mem : ℕ → ℕ)
    (κ a : ℝ) (hFixed : TargetFixedInputs F I old qp qp heap (1/4) κ a mem)
    (hSource : source≤heap) (hM : I.m<2^w) (hE : old.exponent=E) (hEW : E<2^w)
    (hRadius : 2*(I.m*V^2)<2^w) (hLimit : targetTestLimit I.m V k<2^w)
    (hSpace : heap+targetSearchSpace F I.m V k E B<2^w) :
    ∀ z∈targetOffsetPacket old F I 0 qp source heap (targetTestLimit I.m V k) (I.m*V^2),z<2^w := by
  let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
  let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E
  let stage := targetStageSpace F I.m E B
  have harrays : la+ga≤stage := by unfold stage targetStageSpace; omega
  have hTest : 1≤targetTestLimit I.m V k := by unfold targetTestLimit; omega
  have hStage : stage≤targetSearchSpace F I.m V k E B := by
    have h₁ : stage≤targetTestLimit I.m V k*stage := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right stage hTest
    have h₂ : targetOffsetSpace F I.m V k E B≤targetSearchSpace F I.m V k E B := by
      unfold targetSearchSpace
      exact Nat.le_mul_of_pos_left _ (by omega)
    exact h₁.trans ((show targetTestLimit I.m V k*stage≤targetOffsetSpace F I.m V k E B by
      unfold targetOffsetSpace; dsimp only [stage]; omega).trans h₂)
  have hHeap : heap<2^w := by omega
  have hLa : la<2^w := by omega
  have hGa : ga<2^w := by omega
  have field {p d : ℕ} (hp : p+d≤heap) : p<2^w := by omega
  intro z hz
  rw [targetOffsetPacket,List.mem_append,targetEpochPacket,hE] at hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
  · exact hM
  · exact field (hFixed.arrays _ (by simp))
  · exact field (hFixed.arrays _ (by simp))
  · exact field (hFixed.arrays _ (by simp))
  · exact field (hFixed.scalars _ (by simp))
  · exact field (hFixed.scalars _ (by simp))
  · exact Nat.two_pow_pos _
  · exact field (hFixed.scalars _ (by simp))
  · exact field (hFixed.scalars _ (by simp))
  · exact field (hFixed.scalars _ (by simp))
  · exact field (hFixed.scalars _ (by simp))
  · exact field (hFixed.scalars _ (by simp))
  · exact field (hFixed.scalars _ (by simp))
  · exact field (hFixed.scalars _ (by simp))
  · exact field hFixed.rowsEnd
  · exact F.parameters_fit.1
  · exact F.parameters_fit.2.1
  · exact hEW
  · exact hLa
  · exact hGa
  · exact hSource.trans_lt hHeap
  · exact hHeap
  · exact field hFixed.graphEnd
  · exact hLimit
  · omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 490000 in
/-- With the initialized inputs in memory, the linked solver's last
two calls write the exact bounded-circulation optimum. -/
theorem solverFinish_runs {w search recover : ℕ} {p : Program}
    (resources : SolverResources) (entry : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : DynForest) (hD : D.IsSpec)
    (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (hm : 0<J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmParameterWordBits (solverAugmented J).m (solverPenalty J.m)≤w)
    (hDS : SolverDataStructuresAt w p entry resources (solverAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModule search entry.cycleInit entry.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entry.forestInit entry.forestOp))
    (old : EpochLayout) (qp source heap dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hReady : let I := solverAugmented J
      let V := solverPenalty J.m
      let F := ipmMinRatioFormat I.m V hw
      old.exponent=F.rangeExponent ∧
      TargetFixedInputs F I old qp qp heap (1/4)
        ((25/32:ℝ)*((1/(2:ℝ)^resources.qualityExponent)*Num.IPM.alphaPrime I.m V/32)^2/50)
        (Num.IPM.alphaPrime I.m V) mem ∧
      TargetStageFlow F I old.exponent source heap mem ∧
      (∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
        (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e) ∧
      ZeroLowerAt mem old.graph I ∧ ZeroFrom mem heap)
    (hn : (solverAugmented J).n<2^w) (hV : 2≤solverPenalty J.m)
    (hRadius : 2*((solverAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverAugmented J).m (solverPenalty J.m) resources.qualityExponent<2^w)
    (hk : resources.qualityExponent≤slackRangeExponent (solverAugmented J).m (solverPenalty J.m))
    (hCap : ∀ e,J.capacity e<2^w) (hDest : dest+J.m≤heap)
    (hSpace : let I := solverAugmented J
      let V := solverPenalty J.m
      heap+solverSearchReserve resources I V hw+solverRecoveryReserve resources I V J.m<2^w) :
    let I := solverAugmented J
    let V := solverPenalty J.m
    let F := ipmMinRatioFormat I.m V hw
    let radius := I.m*V^2
    let limit := targetTestLimit I.m V resources.qualityExponent
    ∃ out final c, Runs w p ω (solverSearchRecoverBody search recover)
      (startState (targetOffsetPacket old F I 0 qp source heap limit radius++
        [targetSearchRounds radius,I.n,J.m,dest]) mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧
      heap≤out ∧ out≤heap+solverSearchReserve resources I V hw+solverRecoveryReserve resources I V J.m ∧
      ZeroFrom final.mem out ∧ (∀ a<dest,final.mem a=mem a) ∧
      c≤solverSearchCharge resources I V hw+solverRecoveryCharge resources I V J.m+50 := by
  dsimp only at hReady hSpace ⊢
  let I := solverAugmented J
  let V := solverPenalty J.m
  let F := ipmMinRatioFormat I.m V hw
  let k := resources.qualityExponent
  let K := (V:ℤ)
  let U := solverCapacityBound J.m
  let radius := I.m*V^2
  let limit := targetTestLimit I.m V k
  let searchSpace := solverSearchReserve resources I V hw
  let roundSpace := solverRecoveryReserve resources I V J.m
  let searchCost := solverSearchCharge resources I V hw
  let roundCost := solverRecoveryCharge resources I V J.m
  let A := resources.forestOpSpace I.n I.m
  let L := F.limbs
  change heap+searchSpace+roundSpace<2^w at hSpace
  obtain ⟨hE,hFixed,hFlow,hHalf,hRows,hZero⟩ := hReady
  change TargetFixedInputs F I old qp qp heap (1/4)
    ((25/32:ℝ)*((1/(2:ℝ)^k)*Num.IPM.alphaPrime I.m V/32)^2/50) (Num.IPM.alphaPrime I.m V) mem at hFixed
  have hI : I.IsValid := initialInstance_valid J.toInstance K J.toInstance_valid
  obtain ⟨hNums,hBounds,hPenalty⟩ := solverAugmented_numbers J hm hc hu
  have hM : 0 < I.m := hm.trans_le (solverAugmented_size J hp).1
  have hSize : 2≤I.m*V := hV.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right V (show 1≤I.m from hM))
  have hW := ipm_parameter_words_fit I.m V hw
  have hMw : I.m<2^w := (show I.m≤20*I.m by omega).trans_lt hW.2.2.2.2.2.1
  have hmw : J.m<2^w := (solverAugmented_size J hp).1.trans_lt hMw
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
  · obtain ⟨out,final,c,z,fstar,hRun,hStar,hValue,hResult,hBit,hOut,hCost⟩ :=
      solverSearchModule_runs_upTo I V k hw C resources.cycleRate (resources.cycleAllocation I.n I.m) RC hSearch
        hDS.cycleModel hDS.cycleMachine old qp source heap (resources.cycleSpace I.n I.m) mem pos ω hE hFixed hFlow
        hHalf hWord hRadius hRound hDS.cycleBound hLimit hAllocSearch hZero hM (by omega) hSize hk hI hBounds hLower
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
    have hRes : r+roundMachineSpace (resources.forestAllocation I.n I.m 6 [I.n,L,F.fmt.precision,r]) A L I.m+
        recoverScanSpace L J.m≤out+roundSpace := by
      change _≤out+(I.m*L+roundMachineSpace (resources.forestInitSpace I.n I.m) A L I.m+
        recoverScanSpace L J.m)
      have hi : resources.forestAllocation I.n I.m 6 [I.n,L,F.fmt.precision,r]≤resources.forestInitSpace I.n I.m :=
        hDS.forestInitBound r
      have hr : roundMachineSpace (resources.forestAllocation I.n I.m 6 [I.n,L,F.fmt.precision,r]) A L I.m ≤
          roundMachineSpace (resources.forestInitSpace I.n I.m) A L I.m :=
        Nat.add_le_add_right hi _
      have he := Nat.add_le_add_right (Nat.add_le_add_left hr r) (recoverScanSpace L J.m)
      simpa only [r,Nat.add_assoc] using he
    have hRoom : r+roundMachineSpace (resources.forestAllocation I.n I.m 6 [I.n,L,F.fmt.precision,r]) A L I.m+
        recoverScanSpace L J.m<2^w := hRes.trans_lt ((Nat.add_le_add_right hOut roundSpace).trans_lt hSpace)
    have hLarge : 2*J.toInstance.m*(U:ℝ)<(K:ℝ) := by
      change 2*J.toInstance.m*(U:ℝ)<((V:ℤ):ℝ)
      rw [Int.cast_natCast]
      exact hPenalty
    obtain ⟨last,final,c,hRun,hOpt,hLast,hUpper,hZero',hFrame',hC⟩ :=
      solverRoundModule_fromSearch D hD resources.forestRate (resources.forestAllocation I.n I.m) RD
        J K hp U V hm (by omega) hNums (by positivity) hLarge
        hw hBounds hRecover hDS.forestMachine
        (fun b u v a endPtr => ⟨hAlloc 0 (by decide) _,hAlloc 4 (by decide) _,hAlloc 3 (by decide) _,
          hAlloc 2 (by decide) _,hAlloc 1 (by decide) _,hAlloc 5 (by decide) _⟩)
        old.exponent heap out old.graph old.cost old.one dest mem mid pos' ω z fstar hStar hValue
        hResult hBit hWords hRows' hCost' hUnit hCostEnd hFixed'.rowsEnd hOneEnd hCap (by omega) hRoom
    exact ⟨last,final,c,hRun,hOpt,hLast,hUpper.trans hRes,hZero',hFrame',hC⟩

set_option maxHeartbeats 650000 in
set_option maxRecDepth 4096 in
/-- With the initialized inputs in memory, the linked solver's last
two calls write the exact bounded-circulation optimum. -/
theorem solverQualityFinish_runs {w search recover : ℕ} {p : Program}
    (resources : SolverResources) (entry : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : DynForest) (hD : D.IsSpec)
    (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (hm : 0<J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmQualityParameterWordBits (solverAugmented J).m (solverPenalty J.m) resources.qualityExponent≤w)
    (hDS : SolverQualityDataStructuresAt w p entry resources (solverAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModule search entry.cycleInit entry.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entry.forestInit entry.forestOp))
    (old : EpochLayout) (qp source heap dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hReady : let I := solverAugmented J
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
    (hn : (solverAugmented J).n<2^w) (hV : 2≤solverPenalty J.m)
    (hRadius : 2*((solverAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverAugmented J).m (solverPenalty J.m) resources.qualityExponent<2^w)
    (hCap : ∀ e,J.capacity e<2^w) (hDest : dest+J.m≤heap)
    (hSpace : let I := solverAugmented J
      let V := solverPenalty J.m
      heap+solverQualitySearchReserve resources I V hw+solverQualityRecoveryReserve resources I V J.m<2^w) :
    let I := solverAugmented J
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
      c≤solverQualitySearchCharge resources I V hw+solverQualityRecoveryCharge resources I V J.m+50 := by
  dsimp only at hReady hSpace ⊢
  let I := solverAugmented J
  let V := solverPenalty J.m
  let F := ipmQualityMinRatioFormat I.m V resources.qualityExponent hw
  let k := resources.qualityExponent
  let K := (V:ℤ)
  let U := solverCapacityBound J.m
  let radius := I.m*V^2
  let limit := targetTestLimit I.m V k
  let searchSpace := solverQualitySearchReserve resources I V hw
  let roundSpace := solverQualityRecoveryReserve resources I V J.m
  let searchCost := solverQualitySearchCharge resources I V hw
  let roundCost := solverQualityRecoveryCharge resources I V J.m
  let A := resources.forestOpSpace I.n I.m
  let L := F.limbs
  change heap+searchSpace+roundSpace<2^w at hSpace
  obtain ⟨hE,hFixed,hFlow,hHalf,hRows,hZero⟩ := hReady
  change TargetFixedInputs F I old qp qp heap (1/4)
    ((25/32:ℝ)*((1/(2:ℝ)^k)*Num.IPM.alphaPrime I.m V/32)^2/50) (Num.IPM.alphaPrime I.m V) mem at hFixed
  have hI : I.IsValid := initialInstance_valid J.toInstance K J.toInstance_valid
  obtain ⟨hNums,hBounds,hPenalty⟩ := solverAugmented_numbers J hm hc hu
  have hM : 0 < I.m := hm.trans_le (solverAugmented_size J hp).1
  have hSize : 2≤I.m*V := hV.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right V (show 1≤I.m from hM))
  have hW := ipm_quality_parameter_words_fit I.m V resources.qualityExponent hw
  have hMw : I.m<2^w := (show I.m≤20*I.m by omega).trans_lt hW.2.2.2.2.2.1
  have hmw : J.m<2^w := (solverAugmented_size J hp).1.trans_lt hMw
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
  · obtain ⟨out,final,c,z,fstar,hRun,hStar,hValue,hResult,hBit,hOut,hCost⟩ :=
      solverSearchModule_runs_widened_upTo I V k hw C resources.cycleRate (resources.cycleAllocation I.n I.m) RC hSearch
        hDS.cycleModel hDS.cycleMachine old qp source heap (resources.cycleSpace I.n I.m) mem pos ω hE hFixed hFlow
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
    have hRes : r+roundMachineSpace (resources.forestAllocation I.n I.m 6 [I.n,L,F.fmt.precision,r]) A L I.m+
        recoverScanSpace L J.m≤out+roundSpace := by
      change _≤out+(I.m*L+roundMachineSpace (resources.forestInitSpace I.n I.m) A L I.m+
        recoverScanSpace L J.m)
      have hi : resources.forestAllocation I.n I.m 6 [I.n,L,F.fmt.precision,r]≤resources.forestInitSpace I.n I.m :=
        hDS.forestInitBound r
      have hr : roundMachineSpace (resources.forestAllocation I.n I.m 6 [I.n,L,F.fmt.precision,r]) A L I.m ≤
          roundMachineSpace (resources.forestInitSpace I.n I.m) A L I.m :=
        Nat.add_le_add_right hi _
      have he := Nat.add_le_add_right (Nat.add_le_add_left hr r) (recoverScanSpace L J.m)
      simpa only [r,Nat.add_assoc] using he
    have hRoom : r+roundMachineSpace (resources.forestAllocation I.n I.m 6 [I.n,L,F.fmt.precision,r]) A L I.m+
        recoverScanSpace L J.m<2^w := hRes.trans_lt ((Nat.add_le_add_right hOut roundSpace).trans_lt hSpace)
    have hLarge : 2*J.toInstance.m*(U:ℝ)<(K:ℝ) := by
      change 2*J.toInstance.m*(U:ℝ)<((V:ℤ):ℝ)
      rw [Int.cast_natCast]
      exact hPenalty
    obtain ⟨last,final,c,hRun,hOpt,hLast,hUpper,hZero',hFrame',hC⟩ :=
      solverRoundModule_fromSearch_widened D hD resources.forestRate (resources.forestAllocation I.n I.m) RD
        J K hp U V k hm (by omega) hNums (by positivity) hLarge
        hw hBounds hRecover hDS.forestMachine
        (fun b u v a endPtr => ⟨hAlloc 0 (by decide) _,hAlloc 4 (by decide) _,hAlloc 3 (by decide) _,
          hAlloc 2 (by decide) _,hAlloc 1 (by decide) _,hAlloc 5 (by decide) _⟩)
        old.exponent heap out old.graph old.cost old.one dest mem mid pos' ω z fstar hStar hValue
        hResult hBit hWords hRows' hCost' hUnit hCostEnd hFixed'.rowsEnd hOneEnd hCap (by omega) hRoom
    exact ⟨last,final,c,hRun,hOpt,hLast,hUpper.trans hRes,hZero',hFrame',hC⟩

/-- `V`-passing variant of `solverFinish_runs`. -/
theorem solverFinishWithV_runs {w search recover : ℕ} {p : Program}
    (resources : SolverResources) (entry : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : DynForest) (hD : D.IsSpec)
    (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (hm : 0<J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmParameterWordBits (solverAugmented J).m (solverPenalty J.m)≤w)
    (hDS : SolverDataStructuresWithVAt w p entry resources (solverAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModuleWithV search entry.cycleInit entry.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entry.forestInit entry.forestOp))
    (old : EpochLayout) (qp source heap dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hReady : let I := solverAugmented J
      let V := solverPenalty J.m
      let F := ipmMinRatioFormat I.m V hw
      old.exponent=F.rangeExponent ∧
      TargetFixedInputs F I old qp qp heap (1/4)
        ((25/32:ℝ)*((1/(2:ℝ)^resources.qualityExponent)*Num.IPM.alphaPrime I.m V/32)^2/50)
        (Num.IPM.alphaPrime I.m V) mem ∧
      TargetStageFlow F I old.exponent source heap mem ∧
      (∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
        (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e) ∧
      ZeroLowerAt mem old.graph I ∧ ZeroFrom mem heap)
    (hn : (solverAugmented J).n<2^w) (hV : 2≤solverPenalty J.m)
    (hRadius : 2*((solverAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverAugmented J).m (solverPenalty J.m) resources.qualityExponent<2^w)
    (hk : resources.qualityExponent≤slackRangeExponent (solverAugmented J).m (solverPenalty J.m))
    (hCap : ∀ e,J.capacity e<2^w) (hDest : dest+J.m≤heap)
    (hSpace : let I := solverAugmented J
      let V := solverPenalty J.m
      heap+solverSearchReserve resources I V hw+solverRecoveryReserve resources I V J.m<2^w) :
    let I := solverAugmented J
    let V := solverPenalty J.m
    let F := ipmMinRatioFormat I.m V hw
    let radius := I.m*V^2
    let limit := targetTestLimit I.m V resources.qualityExponent
    ∃ out final c, Runs w p ω (solverSearchRecoverBodyWithV search recover)
      (startState (targetOffsetPacket old F I 0 qp source heap limit radius++
        [targetSearchRounds radius,I.n,J.m,dest,V]) mem pos) (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧
      heap≤out ∧ out≤heap+solverSearchReserve resources I V hw+solverRecoveryReserve resources I V J.m ∧
      ZeroFrom final.mem out ∧ (∀ a<dest,final.mem a=mem a) ∧
      c≤solverSearchCharge resources I V hw+solverRecoveryCharge resources I V J.m+50 := by
  dsimp only at hReady hSpace ⊢
  let I := solverAugmented J
  let V := solverPenalty J.m
  let F := ipmMinRatioFormat I.m V hw
  let k := resources.qualityExponent
  let K := (V:ℤ)
  let U := solverCapacityBound J.m
  let radius := I.m*V^2
  let limit := targetTestLimit I.m V k
  let searchSpace := solverSearchReserve resources I V hw
  let roundSpace := solverRecoveryReserve resources I V J.m
  let searchCost := solverSearchCharge resources I V hw
  let roundCost := solverRecoveryCharge resources I V J.m
  let A := resources.forestOpSpace I.n I.m
  let L := F.limbs
  change heap+searchSpace+roundSpace<2^w at hSpace
  obtain ⟨hE,hFixed,hFlow,hHalf,hRows,hZero⟩ := hReady
  change TargetFixedInputs F I old qp qp heap (1/4)
    ((25/32:ℝ)*((1/(2:ℝ)^k)*Num.IPM.alphaPrime I.m V/32)^2/50) (Num.IPM.alphaPrime I.m V) mem at hFixed
  have hI : I.IsValid := initialInstance_valid J.toInstance K J.toInstance_valid
  obtain ⟨hNums,hBounds,hPenalty⟩ := solverAugmented_numbers J hm hc hu
  have hM : 0 < I.m := hm.trans_le (solverAugmented_size J hp).1
  have hSize : 2≤I.m*V := hV.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right V (show 1≤I.m from hM))
  have hW := ipm_parameter_words_fit I.m V hw
  have hVw : V<2^w := hW.2.2.2.2.2.2.2
  have hMw : I.m<2^w := (show I.m≤20*I.m by omega).trans_lt hW.2.2.2.2.2.1
  have hmw : J.m<2^w := (solverAugmented_size J hp).1.trans_lt hMw
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
  · obtain ⟨out,final,c,z,fstar,hRun,hStar,hValue,hResult,hBit,hOut,hCost⟩ :=
      solverSearchModuleWithV_runs_upTo I V k V hw C resources.cycleRate (resources.cycleAllocation I.n I.m) RC hSearch
        hDS.cycleModel hDS.cycleMachine old qp source heap (resources.cycleSpace I.n I.m) mem pos ω hE hFixed hFlow
        hHalf hWord hVw hRadius hRound hDS.cycleBound hLimit hAllocSearch hZero hM (by omega) hSize hk hI hBounds hLower
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
    have hRes : r+roundMachineSpace (resources.forestAllocation I.n I.m 6 [I.n,L,F.fmt.precision,r]) A L I.m+
        recoverScanSpace L J.m≤out+roundSpace := by
      change _≤out+(I.m*L+roundMachineSpace (resources.forestInitSpace I.n I.m) A L I.m+
        recoverScanSpace L J.m)
      have hi : resources.forestAllocation I.n I.m 6 [I.n,L,F.fmt.precision,r]≤resources.forestInitSpace I.n I.m :=
        hDS.forestInitBound r
      have hr : roundMachineSpace (resources.forestAllocation I.n I.m 6 [I.n,L,F.fmt.precision,r]) A L I.m ≤
          roundMachineSpace (resources.forestInitSpace I.n I.m) A L I.m :=
        Nat.add_le_add_right hi _
      have he := Nat.add_le_add_right (Nat.add_le_add_left hr r) (recoverScanSpace L J.m)
      simpa only [r,Nat.add_assoc] using he
    have hRoom : r+roundMachineSpace (resources.forestAllocation I.n I.m 6 [I.n,L,F.fmt.precision,r]) A L I.m+
        recoverScanSpace L J.m<2^w := hRes.trans_lt ((Nat.add_le_add_right hOut roundSpace).trans_lt hSpace)
    have hLarge : 2*J.toInstance.m*(U:ℝ)<(K:ℝ) := by
      change 2*J.toInstance.m*(U:ℝ)<((V:ℤ):ℝ)
      rw [Int.cast_natCast]
      exact hPenalty
    obtain ⟨last,final,c,hRun,hOpt,hLast,hUpper,hZero',hFrame',hC⟩ :=
      solverRoundModule_fromSearch D hD resources.forestRate (resources.forestAllocation I.n I.m) RD
        J K hp U V hm (by omega) hNums (by positivity) hLarge
        hw hBounds hRecover hDS.forestMachine
        (fun b u v a endPtr => ⟨hAlloc 0 (by decide) _,hAlloc 4 (by decide) _,hAlloc 3 (by decide) _,
          hAlloc 2 (by decide) _,hAlloc 1 (by decide) _,hAlloc 5 (by decide) _⟩)
        old.exponent heap out old.graph old.cost old.one dest mem mid pos' ω z fstar hStar hValue
        hResult hBit hWords hRows' hCost' hUnit hCostEnd hFixed'.rowsEnd hOneEnd hCap (by omega) hRoom
    exact ⟨last,final,c,hRun,hOpt,hLast,hUpper.trans hRes,hZero',hFrame',hC⟩

set_option maxHeartbeats 650000 in
set_option maxRecDepth 4096 in
/-- `V`-passing variant of `solverQualityFinish_runs`. -/
theorem solverQualityFinishWithV_runs {w search recover : ℕ} {p : Program}
    (resources : SolverResources) (entry : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : DynForest) (hD : D.IsSpec)
    (RC : DSRep C.State) (RD : DSRep D.State)
    (J : Circulation) (hm : 0<J.m) (hp : ∀ e,1≤J.capacity e)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e,J.capacity e≤J.m^40)
    (hw : ipmQualityParameterWordBits (solverAugmented J).m (solverPenalty J.m) resources.qualityExponent≤w)
    (hDS : SolverQualityDataStructuresWithVAt w p entry resources (solverAugmented J) (solverPenalty J.m) hw C D RC RD)
    (hSearch : p.HasAt search (solverSearchModuleWithV search entry.cycleInit entry.cycleOp))
    (hRecover : p.HasAt recover (solverRoundModule recover entry.forestInit entry.forestOp))
    (old : EpochLayout) (qp source heap dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hReady : let I := solverAugmented J
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
    (hn : (solverAugmented J).n<2^w) (hV : 2≤solverPenalty J.m)
    (hRadius : 2*((solverAugmented J).m*(solverPenalty J.m)^2)<2^w)
    (hLimit : targetTestLimit (solverAugmented J).m (solverPenalty J.m) resources.qualityExponent<2^w)
    (hCap : ∀ e,J.capacity e<2^w) (hDest : dest+J.m≤heap)
    (hSpace : let I := solverAugmented J
      let V := solverPenalty J.m
      heap+solverQualitySearchReserve resources I V hw+solverQualityRecoveryReserve resources I V J.m<2^w) :
    let I := solverAugmented J
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
      c≤solverQualitySearchCharge resources I V hw+solverQualityRecoveryCharge resources I V J.m+50 := by
  dsimp only at hReady hSpace ⊢
  let I := solverAugmented J
  let V := solverPenalty J.m
  let F := ipmQualityMinRatioFormat I.m V resources.qualityExponent hw
  let k := resources.qualityExponent
  let K := (V:ℤ)
  let U := solverCapacityBound J.m
  let radius := I.m*V^2
  let limit := targetTestLimit I.m V k
  let searchSpace := solverQualitySearchReserve resources I V hw
  let roundSpace := solverQualityRecoveryReserve resources I V J.m
  let searchCost := solverQualitySearchCharge resources I V hw
  let roundCost := solverQualityRecoveryCharge resources I V J.m
  let A := resources.forestOpSpace I.n I.m
  let L := F.limbs
  change heap+searchSpace+roundSpace<2^w at hSpace
  obtain ⟨hE,hFixed,hFlow,hHalf,hRows,hZero⟩ := hReady
  change TargetFixedInputs F I old qp qp heap (1/4)
    ((25/32:ℝ)*((1/(2:ℝ)^k)*Num.IPM.alphaPrime I.m V/32)^2/50) (Num.IPM.alphaPrime I.m V) mem at hFixed
  have hI : I.IsValid := initialInstance_valid J.toInstance K J.toInstance_valid
  obtain ⟨hNums,hBounds,hPenalty⟩ := solverAugmented_numbers J hm hc hu
  have hM : 0 < I.m := hm.trans_le (solverAugmented_size J hp).1
  have hSize : 2≤I.m*V := hV.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right V (show 1≤I.m from hM))
  have hW := ipm_quality_parameter_words_fit I.m V resources.qualityExponent hw
  have hVw : V<2^w := hW.2.2.2.2.2.2.2
  have hMw : I.m<2^w := (show I.m≤20*I.m by omega).trans_lt hW.2.2.2.2.2.1
  have hmw : J.m<2^w := (solverAugmented_size J hp).1.trans_lt hMw
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
  · obtain ⟨out,final,c,z,fstar,hRun,hStar,hValue,hResult,hBit,hOut,hCost⟩ :=
      solverSearchModuleWithV_runs_widened_upTo I V k V hw C resources.cycleRate (resources.cycleAllocation I.n I.m) RC hSearch
        hDS.cycleModel hDS.cycleMachine old qp source heap (resources.cycleSpace I.n I.m) mem pos ω hE hFixed hFlow
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
    have hRes : r+roundMachineSpace (resources.forestAllocation I.n I.m 6 [I.n,L,F.fmt.precision,r]) A L I.m+
        recoverScanSpace L J.m≤out+roundSpace := by
      change _≤out+(I.m*L+roundMachineSpace (resources.forestInitSpace I.n I.m) A L I.m+
        recoverScanSpace L J.m)
      have hi : resources.forestAllocation I.n I.m 6 [I.n,L,F.fmt.precision,r]≤resources.forestInitSpace I.n I.m :=
        hDS.forestInitBound r
      have hr : roundMachineSpace (resources.forestAllocation I.n I.m 6 [I.n,L,F.fmt.precision,r]) A L I.m ≤
          roundMachineSpace (resources.forestInitSpace I.n I.m) A L I.m :=
        Nat.add_le_add_right hi _
      have he := Nat.add_le_add_right (Nat.add_le_add_left hr r) (recoverScanSpace L J.m)
      simpa only [r,Nat.add_assoc] using he
    have hRoom : r+roundMachineSpace (resources.forestAllocation I.n I.m 6 [I.n,L,F.fmt.precision,r]) A L I.m+
        recoverScanSpace L J.m<2^w := hRes.trans_lt ((Nat.add_le_add_right hOut roundSpace).trans_lt hSpace)
    have hLarge : 2*J.toInstance.m*(U:ℝ)<(K:ℝ) := by
      change 2*J.toInstance.m*(U:ℝ)<((V:ℤ):ℝ)
      rw [Int.cast_natCast]
      exact hPenalty
    obtain ⟨last,final,c,hRun,hOpt,hLast,hUpper,hZero',hFrame',hC⟩ :=
      solverRoundModule_fromSearch_widened D hD resources.forestRate (resources.forestAllocation I.n I.m) RD
        J K hp U V k hm (by omega) hNums (by positivity) hLarge
        hw hBounds hRecover hDS.forestMachine
        (fun b u v a endPtr => ⟨hAlloc 0 (by decide) _,hAlloc 4 (by decide) _,hAlloc 3 (by decide) _,
          hAlloc 2 (by decide) _,hAlloc 1 (by decide) _,hAlloc 5 (by decide) _⟩)
        old.exponent heap out old.graph old.cost old.one dest mem mid pos' ω z fstar hStar hValue
        hResult hBit hWords hRows' hCost' hUnit hCostEnd hFixed'.rowsEnd hOneEnd hCap (by omega) hRoom
    exact ⟨last,final,c,hRun,hOpt,hLast,hUpper.trans hRes,hZero',hFrame',hC⟩

end MinCostFlow.IPM.Machine
