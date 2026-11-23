module

public import MinCostFlow.IPM.Machine.RoundExtractFromSearch
public import MinCostFlow.IPM.Machine.ConnectedRecoverPrefix
import MinCostFlow.IPM.Machine.PrecisionProducts
import Mathlib.Tactic

/-!
# Recovering from a connected target search

The accepted flow is rounded on the connected graph using Lemma 4.1.
The connected recovery for Lemma 4.12 then certifies that the rounded
prefix is optimal for the original circulation.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling Rounding

set_option maxHeartbeats 450000 in
/-- The actual copy, rounder, and prefix scan on the successful
target result return an exact optimal circulation in the output
region. The numerical fit obligations follow from the selected IPM
precision and from the accepted flow's feasibility. -/
theorem roundExtract_connected_fromSearch {w copy roundEntry extract loop edge fractional connected repairRelink A : ℕ}
    (D : DynForest) (hD : D.IsSpec) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep D.State)
    {p : Program} {init : ℕ} {op : ℕ → ℕ}
    (J : Circulation) (K : ℤ) (hp : ∀ e,1≤J.capacity e)
    (U V k : ℕ) (hm : 0 < J.m) (hV : 1≤V)
    (hNums : NumbersBounded J.toInstance (U:ℝ)) (hLargeSq : 2*J.toInstance.m*(U:ℝ)^2<(K:ℝ))
    (hLarge : 2*J.toInstance.m*(U:ℝ)<(K:ℝ))
    (hw : ipmQualityParameterWordBits (connectedInitialInstance J.toInstance K).m V k≤w)
    (hBounds : NumbersBounded (connectedInitialInstance J.toInstance K) (V:ℝ))
    (F : MinRatioFormat w) (hF : F=ipmQualityMinRatioFormat (connectedInitialInstance J.toInstance K).m V k hw)
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
    (fstar : Fin (connectedInitialInstance J.toInstance K).m → ℝ)
    (hstar : (connectedInitialInstance J.toInstance K).IsMinCostFlow fstar)
    (hz : (connectedInitialInstance J.toInstance K).cost fstar=(z:ℝ))
    (hResult : TargetOffsetResult F (connectedInitialInstance J.toInstance K) E old heap z z before mem)
    (hBit : mem (heap-1)=1)
    (hWords : let I := connectedInitialInstance J.toInstance K
      ∀ a∈[I.n,I.m,graph,cost,mem (heap-2),F.limbs,F.fmt.precision,one,heap,dest,J.m],a<2^w)
    (hRows : ZeroLowerAt mem graph (connectedInitialInstance J.toInstance K))
    (hCosts : RoundCostsAt (connectedInitialInstance J.toInstance K) mem cost F.fmt.limbBits F.limbs)
    (hUnit : RatAt mem one F.fmt.limbBits F.limbs F.fmt.precision 1)
    (hCost : cost+(connectedInitialInstance J.toInstance K).m*F.limbs≤heap)
    (hGraph : graph+(zeroLowerWords (connectedInitialInstance J.toInstance K)).length≤heap)
    (hOne : one+F.limbs≤heap)
    (hCap : ∀ e,J.capacity e<2^w) (hDest : dest+J.m≤heap)
    (hSpace : let I := connectedInitialInstance J.toInstance K
      let b := heap+I.m*F.limbs
      b+roundMachineSpace (allocation 6 [I.n,F.limbs,F.fmt.precision,b]) A F.limbs I.m+recoverScanSpace F.limbs J.m<2^w) :
    let I := connectedInitialInstance J.toInstance K
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
  let I := connectedInitialInstance J.toInstance K
  let source := mem (heap-2)
  let f := roundingInput F I mem source
  let b := heap+I.m*F.limbs
  have hI : I.IsValid := connectedInitialInstance_valid J.toInstance K J.toInstance_valid
  have hmI : 0<I.m := hm.trans_le (connectedInitial_circulation_m_ge J hp K)
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
    connectedRecoverPrefix_optimal J U K hp (Nat.cast_nonneg _) hNums hLargeSq hLarge
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
  refine roundExtract_prefix_runs D rate allocation hCopy hRound hExtract J I
    (connectedInitial_circulation_m_ge J hp K) f q hq hJ
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
