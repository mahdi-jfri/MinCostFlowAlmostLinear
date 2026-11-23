module

public import MinCostFlow.IPM.Machine.RoundExtract
public import MinCostFlow.IPM.Machine.RoundingInput
import MinCostFlow.IPM.Machine.PrecisionProducts
import MinCostFlow.IPM.InitialDomain
import Mathlib.Tactic

/-!
# Exact machine recovery from the successful search

The accepted table already represents a rational flow. Its
fixed-point coordinates supply Lemma 4.1 directly, and the cost
gap of one quarter gives an integral optimum. Lemma 4.12 then
recovers the bounded circulation's exact answer.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling Rounding

/-- An exact real scalar reading agrees with rational decoding on
the same fixed-point block. -/
theorem ScalarAt.rat {mem : ℕ → ℕ} {a h L P : ℕ} {q : ℚ}
    (hq : ScalarAt mem a h L P (q:ℝ)) : RatAt mem a h L P q := by
  refine ⟨hq.1,?_⟩
  have he : (readRat mem a h L P:ℝ)=(q:ℝ) := by
    simpa only [readRat,Num.fixVal,Rat.cast_div,Rat.cast_intCast,Rat.cast_pow,Rat.cast_ofNat]
      using hq.2
  exact_mod_cast he

/-- The selected accepted table is exact as a dyadic rational table. -/
theorem TargetStageFlow.rounding_at {w : ℕ} {F : MinRatioFormat w} {I : Instance}
    {E source heap : ℕ} {mem : ℕ → ℕ}
    (ht : TargetStageFlow F I E source heap mem) :
    RoundFlowAt I mem source F.fmt.limbBits F.limbs F.fmt.precision
      (roundingInput F I mem source) :=
  fun e => ⟨(ht.2.2 e).1,rfl⟩

set_option maxHeartbeats 520000 in
/-- The actual copy, rounder, and prefix scan on the successful
target result return an exact optimal circulation in the output
region. The numerical fit obligations follow from the selected IPM
precision and from the accepted flow's feasibility. -/
theorem roundExtract_fromSearch {w copy roundEntry extract loop edge fractional connected repairRelink A : ℕ}
    (D : DynForest) (hD : D.IsSpec) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep D.State)
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (J : Circulation) (K : ℤ) (hp : ∀ e,1≤J.capacity e)
    (U V : ℕ) (hm : 0 < J.m) (hV : 1≤V)
    (hNums : NumbersBounded J.toInstance (U:ℝ)) (hPenalty : 0≤(K:ℝ))
    (hLarge : 2*J.toInstance.m*(U:ℝ)<(K:ℝ))
    (hw : ipmParameterWordBits (initialInstance J.toInstance K).m V≤w)
    (hBounds : NumbersBounded (initialInstance J.toInstance K) (V:ℝ))
    (F : MinRatioFormat w) (hF : F=ipmMinRatioFormat (initialInstance J.toInstance K).m V hw)
    (himpl : R.Implements w p init op (forestMachineContract D w F.fmt.limbBits F.limbs F.fmt.precision rate allocation))
    (B : RoundProcedures) (hB : B.Linked w F.fmt.limbBits F.fmt.precision p op)
    (hCopy : MeetsContract w p copy (epochFlowCopyContract w))
    (hRound : p.procs[roundEntry]?=some (roundMachineBody init loop))
    (hLoop : p.procs[loop]?=some (roundLoopBody loop edge))
    (hEdge : p.procs[edge]?=some (roundEdgeBody B fractional))
    (hFrac : p.procs[fractional]?=some (roundFractionalBody B connected))
    (hConnect : p.procs[connected]?=some (roundConnectedBody B repairRelink))
    (hRL : p.procs[repairRelink]?=some (roundRepairRelinkBody B))
    (hExtract : MeetsContract w p extract (recoverScanContract w F.fmt.limbBits))
    (hAlloc : ∀ b u v a heap,allocation 0 [b,u,heap]≤A ∧ allocation 4 [b,u,v,heap]≤A ∧
      allocation 3 [b,u,v,a,heap]≤A ∧ allocation 2 [b,u,v,heap]≤A ∧
      allocation 1 [b,a,heap]≤A ∧ allocation 5 [b,u,v,heap]≤A)
    (E old heap graph cost one dest : ℕ) (before mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (z : ℤ)
    (fstar : Fin (initialInstance J.toInstance K).m → ℝ)
    (hstar : (initialInstance J.toInstance K).IsMinCostFlow fstar)
    (hz : (initialInstance J.toInstance K).cost fstar=(z:ℝ))
    (hResult : TargetOffsetResult F (initialInstance J.toInstance K) E old heap z z before mem)
    (hBit : mem (heap-1)=1)
    (hWords : let I := initialInstance J.toInstance K
      ∀ a∈[I.n,I.m,graph,cost,mem (heap-2),F.limbs,F.fmt.precision,one,heap,dest,J.m],a<2^w)
    (hRows : ZeroLowerAt mem graph (initialInstance J.toInstance K))
    (hCosts : RoundCostsAt (initialInstance J.toInstance K) mem cost F.fmt.limbBits F.limbs)
    (hUnit : RatAt mem one F.fmt.limbBits F.limbs F.fmt.precision 1)
    (hCost : cost+(initialInstance J.toInstance K).m*F.limbs≤heap)
    (hGraph : graph+(zeroLowerWords (initialInstance J.toInstance K)).length≤heap)
    (hOne : one+F.limbs≤heap)
    (hCap : ∀ e,J.capacity e<2^w) (hDest : dest+J.m≤heap)
    (hSpace : let I := initialInstance J.toInstance K
      let b := heap+I.m*F.limbs
      b+roundMachineSpace (allocation 6 [I.n,F.limbs,F.fmt.precision,b]) A F.limbs I.m+recoverScanSpace F.limbs J.m<2^w) :
    let I := initialInstance J.toInstance K
    let b := heap+I.m*F.limbs
    ∃ out final c,
      Runs w p ω (roundExtractBody copy roundEntry extract)
        (startState [I.n,I.m,graph,cost,mem (heap-2),F.limbs,F.fmt.precision,one,heap,dest,J.m] mem pos)
        (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧ heap≤out ∧
      out≤b+roundMachineSpace (allocation 6 [I.n,F.limbs,F.fmt.precision,b]) A F.limbs I.m+recoverScanSpace F.limbs J.m ∧
      ZeroFrom final.mem out ∧ (∀ a<dest,final.mem a=mem a) ∧
      c≤roundMachineCost (rate I.n) F.limbs I.n I.m+17*(I.m*F.limbs)+J.m*(100*F.limbs+240)+100 := by
  dsimp only at hWords hSpace ⊢
  let I := initialInstance J.toInstance K
  let source := mem (heap-2)
  let f := roundingInput F I mem source
  let b := heap+I.m*F.limbs
  have hI : I.IsValid := initialInstance_valid J.toInstance K J.toInstance_valid
  have hmI : 0<I.m := hm.trans_le (circulation_augmented_m_ge J K hp)
  obtain ⟨hTaken,_⟩ := hResult.2.2.2.2.2.2 hBit
  have hBound : ∀ e, |(f e:ℝ)|≤V := by
    have hf := feasible_abs_le I V hBounds (epochVector F I mem source) hTaken.2.1
    rw [← roundingInput_real F I mem source] at hf
    exact hf
  have hRoutes : I.Routes (fun e => (f e:ℝ)) := by
    have he := roundingInput_real F I mem source
    exact he.symm ▸ hTaken.2.1.1
  obtain ⟨hInt,hOpt,_,_,_⟩ := roundingInput_optimal F I D hD hI E old heap before mem z fstar hstar hz hResult hBit
  obtain ⟨q,hq,hJ,hqCap⟩ :=
    recoverPrefix_optimal J U K hp (Nat.cast_nonneg _) hNums hPenalty hLarge
      (roundFlow D I f).flowArr hOpt hInt
  have hf : RoundFlowAt I mem source F.fmt.limbBits F.limbs F.fmt.precision f := hTaken.rounding_at
  have hFP : ∀ e,IsFixedPoint F.fmt.precision (f e) := roundingInput_fixed F I mem source
  have hW := ipm_parameter_words_fit I.m V hw
  have hConst : 5<2^w := (by decide : 5<2^14).trans_le (Nat.pow_le_pow_right (by decide) hW.1)
  have hn : I.n<2^w := hWords _ (by simp [I])
  have hL : 0<F.limbs := by rw [hF]; change 0 < ipmLimbs I.m V; unfold ipmLimbs; omega
  have hML : I.m+1<2^w := by have h := hW.2.2.2.2.2.1; omega
  have hNumeric (j : Fin I.m) (s : RoundState D I)
      (hS : LoopInv D I f F.fmt.precision (maxAbsFlow I f+1) j.val s)
      (hQ : isIntRat (f j)=false) : RoundEdgeNumeric D I f j s F.fmt.limbBits F.limbs F.fmt.precision := by
    rw [hF] at hS hFP ⊢
    exact roundEdge_numeric hD V hmI hV hBounds hBound s j hS hFP hQ
  refine roundExtract_runs D rate allocation hCopy hRound hExtract J K hp f q hq hJ
    (fun e => (hqCap e).trans_lt (hCap e)) graph cost source one heap dest mem pos ω hWords
    (by omega) hResult.2.2.1 hTaken.1 hDest hf hSpace ?_
  dsimp only
  intro mid pos₁ hMem hZero hFlow
  have hR : ZeroLowerAt mid graph I :=
    ⟨hRows.1,hRows.2.1,hRows.2.2.of_agree_below hGraph hMem⟩
  have hC : RoundCostsAt I mid cost F.fmt.limbBits F.limbs := by
    intro e
    have he := Nat.mul_le_mul_right F.limbs (Nat.succ_le_of_lt e.isLt)
    rw [Nat.succ_mul] at he
    change cost+I.m*F.limbs≤heap at hCost
    exact (hCosts e).frozen hMem (by omega)
  have hS : b+roundMachineSpace (allocation 6 [I.n,F.limbs,F.fmt.precision,b]) A F.limbs I.m<2^w := by
    change b+roundMachineSpace (allocation 6 [I.n,F.limbs,F.fmt.precision,b]) A F.limbs I.m+recoverScanSpace F.limbs J.m<2^w at hSpace
    omega
  exact roundMachine_runs D hD rate allocation R himpl B hB hLoop hEdge hFrac hConnect hRL hAlloc
    I hI f (maxAbsFlow I f+1) hRoutes hFP graph cost heap one b mid pos₁ ω
    hL F.parameters_fit.1 F.fmt.precision_aligned (by rw [hF]; exact hW.2.2.1) hConst hML hn le_rfl hCost
    hGraph hOne hR hC (hUnit.frozen hMem hOne) hFlow hZero hS hNumeric

set_option maxHeartbeats 450000 in
/-- The actual copy, rounder, and prefix scan on the successful
target result return an exact optimal circulation in the output
region. The numerical fit obligations follow from the selected IPM
precision and from the accepted flow's feasibility. -/
theorem roundExtract_fromSearch_widened {w copy roundEntry extract loop edge fractional connected repairRelink A : ℕ}
    (D : DynForest) (hD : D.IsSpec) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep D.State)
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (J : Circulation) (K : ℤ) (hp : ∀ e,1≤J.capacity e)
    (U V k : ℕ) (hm : 0 < J.m) (hV : 1≤V)
    (hNums : NumbersBounded J.toInstance (U:ℝ)) (hPenalty : 0≤(K:ℝ))
    (hLarge : 2*J.toInstance.m*(U:ℝ)<(K:ℝ))
    (hw : ipmQualityParameterWordBits (initialInstance J.toInstance K).m V k≤w)
    (hBounds : NumbersBounded (initialInstance J.toInstance K) (V:ℝ))
    (F : MinRatioFormat w) (hF : F=ipmQualityMinRatioFormat (initialInstance J.toInstance K).m V k hw)
    (himpl : R.Implements w p init op (forestMachineContract D w F.fmt.limbBits F.limbs F.fmt.precision rate allocation))
    (B : RoundProcedures) (hB : B.Linked w F.fmt.limbBits F.fmt.precision p op)
    (hCopy : MeetsContract w p copy (epochFlowCopyContract w))
    (hRound : p.procs[roundEntry]?=some (roundMachineBody init loop))
    (hLoop : p.procs[loop]?=some (roundLoopBody loop edge))
    (hEdge : p.procs[edge]?=some (roundEdgeBody B fractional))
    (hFrac : p.procs[fractional]?=some (roundFractionalBody B connected))
    (hConnect : p.procs[connected]?=some (roundConnectedBody B repairRelink))
    (hRL : p.procs[repairRelink]?=some (roundRepairRelinkBody B))
    (hExtract : MeetsContract w p extract (recoverScanContract w F.fmt.limbBits))
    (hAlloc : ∀ b u v a heap,allocation 0 [b,u,heap]≤A ∧ allocation 4 [b,u,v,heap]≤A ∧
      allocation 3 [b,u,v,a,heap]≤A ∧ allocation 2 [b,u,v,heap]≤A ∧
      allocation 1 [b,a,heap]≤A ∧ allocation 5 [b,u,v,heap]≤A)
    (E old heap graph cost one dest : ℕ) (before mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (z : ℤ)
    (fstar : Fin (initialInstance J.toInstance K).m → ℝ)
    (hstar : (initialInstance J.toInstance K).IsMinCostFlow fstar)
    (hz : (initialInstance J.toInstance K).cost fstar=(z:ℝ))
    (hResult : TargetOffsetResult F (initialInstance J.toInstance K) E old heap z z before mem)
    (hBit : mem (heap-1)=1)
    (hWords : let I := initialInstance J.toInstance K
      ∀ a∈[I.n,I.m,graph,cost,mem (heap-2),F.limbs,F.fmt.precision,one,heap,dest,J.m],a<2^w)
    (hRows : ZeroLowerAt mem graph (initialInstance J.toInstance K))
    (hCosts : RoundCostsAt (initialInstance J.toInstance K) mem cost F.fmt.limbBits F.limbs)
    (hUnit : RatAt mem one F.fmt.limbBits F.limbs F.fmt.precision 1)
    (hCost : cost+(initialInstance J.toInstance K).m*F.limbs≤heap)
    (hGraph : graph+(zeroLowerWords (initialInstance J.toInstance K)).length≤heap)
    (hOne : one+F.limbs≤heap)
    (hCap : ∀ e,J.capacity e<2^w) (hDest : dest+J.m≤heap)
    (hSpace : let I := initialInstance J.toInstance K
      let b := heap+I.m*F.limbs
      b+roundMachineSpace (allocation 6 [I.n,F.limbs,F.fmt.precision,b]) A F.limbs I.m+recoverScanSpace F.limbs J.m<2^w) :
    let I := initialInstance J.toInstance K
    let b := heap+I.m*F.limbs
    ∃ out final c,
      Runs w p ω (roundExtractBody copy roundEntry extract)
        (startState [I.n,I.m,graph,cost,mem (heap-2),F.limbs,F.fmt.precision,one,heap,dest,J.m] mem pos)
        (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧ heap≤out ∧
      out≤b+roundMachineSpace (allocation 6 [I.n,F.limbs,F.fmt.precision,b]) A F.limbs I.m+recoverScanSpace F.limbs J.m ∧
      ZeroFrom final.mem out ∧ (∀ a<dest,final.mem a=mem a) ∧
      c≤roundMachineCost (rate I.n) F.limbs I.n I.m+17*(I.m*F.limbs)+J.m*(100*F.limbs+240)+100 := by
  dsimp only at hWords hSpace ⊢
  let I := initialInstance J.toInstance K
  let source := mem (heap-2)
  let f := roundingInput F I mem source
  let b := heap+I.m*F.limbs
  have hI : I.IsValid := initialInstance_valid J.toInstance K J.toInstance_valid
  have hmI : 0<I.m := hm.trans_le (circulation_augmented_m_ge J K hp)
  obtain ⟨hTaken,_⟩ := hResult.2.2.2.2.2.2 hBit
  have hBound : ∀ e, |(f e:ℝ)|≤V := by
    have hf := feasible_abs_le I V hBounds (epochVector F I mem source) hTaken.2.1
    rw [← roundingInput_real F I mem source] at hf
    exact hf
  have hRoutes : I.Routes (fun e => (f e:ℝ)) := by
    have he := roundingInput_real F I mem source
    exact he.symm ▸ hTaken.2.1.1
  obtain ⟨hInt,hOpt,_,_,_⟩ := roundingInput_optimal F I D hD hI E old heap before mem z fstar hstar hz hResult hBit
  obtain ⟨q,hq,hJ,hqCap⟩ :=
    recoverPrefix_optimal J U K hp (Nat.cast_nonneg _) hNums hPenalty hLarge
      (roundFlow D I f).flowArr hOpt hInt
  have hf : RoundFlowAt I mem source F.fmt.limbBits F.limbs F.fmt.precision f := hTaken.rounding_at
  have hFP : ∀ e,IsFixedPoint F.fmt.precision (f e) := roundingInput_fixed F I mem source
  have hW := ipm_quality_parameter_words_fit I.m V k hw
  have hConst : 5<2^w := (by decide : 5<2^14).trans_le (Nat.pow_le_pow_right (by decide) hW.1)
  have hn : I.n<2^w := hWords _ (by simp [I])
  have hL : 0<F.limbs := by rw [hF]; change 0 < ipmQualityLimbs I.m V k; unfold ipmQualityLimbs; omega
  have hML : I.m+1<2^w := by have h := hW.2.2.2.2.2.1; omega
  have hNumeric (j : Fin I.m) (s : RoundState D I)
      (hS : LoopInv D I f F.fmt.precision (maxAbsFlow I f+1) j.val s)
      (hQ : isIntRat (f j)=false) : RoundEdgeNumeric D I f j s F.fmt.limbBits F.limbs F.fmt.precision := by
    rw [hF] at hS hFP ⊢
    exact roundEdge_numeric_widened hD V k hmI hV hBounds hBound s j hS hFP hQ
  refine roundExtract_runs D rate allocation hCopy hRound hExtract J K hp f q hq hJ
    (fun e => (hqCap e).trans_lt (hCap e)) graph cost source one heap dest mem pos ω hWords
    (by omega) hResult.2.2.1 hTaken.1 hDest hf hSpace ?_
  dsimp only
  intro mid pos₁ hMem hZero hFlow
  have hR : ZeroLowerAt mid graph I :=
    ⟨hRows.1,hRows.2.1,hRows.2.2.of_agree_below hGraph hMem⟩
  have hC : RoundCostsAt I mid cost F.fmt.limbBits F.limbs := by
    intro e
    have he := Nat.mul_le_mul_right F.limbs (Nat.succ_le_of_lt e.isLt)
    rw [Nat.succ_mul] at he
    change cost+I.m*F.limbs≤heap at hCost
    exact (hCosts e).frozen hMem (by omega)
  have hS : b+roundMachineSpace (allocation 6 [I.n,F.limbs,F.fmt.precision,b]) A F.limbs I.m<2^w := by
    change b+roundMachineSpace (allocation 6 [I.n,F.limbs,F.fmt.precision,b]) A F.limbs I.m+recoverScanSpace F.limbs J.m<2^w at hSpace
    omega
  exact roundMachine_runs D hD rate allocation R himpl B hB hLoop hEdge hFrac hConnect hRL hAlloc
    I hI f (maxAbsFlow I f+1) hRoutes hFP graph cost heap one b mid pos₁ ω
    hL F.parameters_fit.1 F.fmt.precision_aligned (by rw [hF]; exact hW.2.2.1) hConst hML hn le_rfl hCost
    hGraph hOne hR hC (hUnit.frozen hMem hOne) hFlow hZero hS hNumeric

end MinCostFlow.IPM.Machine
