module

public import MinCostFlow.IPM.Machine.SolverRoundLink
public import MinCostFlow.IPM.Machine.ConnectedExtractFromSearch
import MinCostFlow.Num.ModulePlacement
import Mathlib.Tactic

/-!
# Linked rounding for the connected solver

The existing rounder and output scan load the connected search result.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling Rounding

set_option maxHeartbeats 450000 in
/-- The recovery module uses the forest contract at the chosen precision.
Everything else, including the numeric calls and final output scan,
is verified by the linked code. -/
theorem connectedRoundModule_fromSearch {w b init A : ℕ} {p : Program} {op : ℕ → ℕ}
    (D : DynForest) (hD : D.IsSpec) (rate : ℕ → ℕ)
    (allocation : ℕ → List ℕ → ℕ) (R : DSRep D.State)
    (J : Circulation) (K : ℤ) (hp : ∀ e,1≤J.capacity e)
    (U V k : ℕ) (hm : 0 < J.m) (hV : 1≤V)
    (hNums : NumbersBounded J.toInstance (U:ℝ)) (hLargeSq : 2*J.toInstance.m*(U:ℝ)^2<(K:ℝ))
    (hLarge : 2*J.toInstance.m*(U:ℝ)<(K:ℝ))
    (hw : ipmQualityParameterWordBits (connectedInitialInstance J.toInstance K).m V k≤w)
    (hBounds : NumbersBounded (connectedInitialInstance J.toInstance K) (V:ℝ))
    (hModule : p.HasAt b (solverRoundModule b init op))
    (himpl : R.Implements w p init op (forestMachineContract D w 4
      (ipmQualityLimbs (connectedInitialInstance J.toInstance K).m V k)
      (ipmQualityPrecision (connectedInitialInstance J.toInstance K).m V k) rate allocation))
    (hAlloc : ∀ b u v a heap,allocation 0 [b,u,heap]≤A ∧ allocation 4 [b,u,v,heap]≤A ∧
      allocation 3 [b,u,v,a,heap]≤A ∧ allocation 2 [b,u,v,heap]≤A ∧
      allocation 1 [b,a,heap]≤A ∧ allocation 5 [b,u,v,heap]≤A)
    (E old heap graph cost one dest : ℕ) (before mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (z : ℤ)
    (fstar : Fin (connectedInitialInstance J.toInstance K).m → ℝ)
    (hstar : (connectedInitialInstance J.toInstance K).IsMinCostFlow fstar)
    (hz : (connectedInitialInstance J.toInstance K).cost fstar=(z:ℝ))
    (hResult : TargetOffsetResult (ipmQualityMinRatioFormat (connectedInitialInstance J.toInstance K).m V k hw)
      (connectedInitialInstance J.toInstance K) E old heap z z before mem)
    (hBit : mem (heap-1)=1)
    (hWords : let I := connectedInitialInstance J.toInstance K
      ∀ a∈[I.n,I.m,graph,cost,mem (heap-2),ipmQualityLimbs I.m V k,ipmQualityPrecision I.m V k,one,heap,dest,J.m],a<2^w)
    (hRows : ZeroLowerAt mem graph (connectedInitialInstance J.toInstance K))
    (hCosts : let I := connectedInitialInstance J.toInstance K
      RoundCostsAt I mem cost 4 (ipmQualityLimbs I.m V k))
    (hUnit : let I := connectedInitialInstance J.toInstance K
      RatAt mem one 4 (ipmQualityLimbs I.m V k) (ipmQualityPrecision I.m V k) 1)
    (hCost : cost+(connectedInitialInstance J.toInstance K).m*ipmQualityLimbs (connectedInitialInstance J.toInstance K).m V k≤heap)
    (hGraph : graph+(zeroLowerWords (connectedInitialInstance J.toInstance K)).length≤heap)
    (hOne : one+ipmQualityLimbs (connectedInitialInstance J.toInstance K).m V k≤heap)
    (hCap : ∀ e,J.capacity e<2^w) (hDest : dest+J.m≤heap)
    (hSpace : let I := connectedInitialInstance J.toInstance K
      let L := ipmQualityLimbs I.m V k
      let P := ipmQualityPrecision I.m V k
      let r := heap+I.m*L
      r+roundMachineSpace (allocation 6 [I.n,L,P,r]) A L I.m+recoverScanSpace L J.m<2^w) :
    let I := connectedInitialInstance J.toInstance K
    let L := ipmQualityLimbs I.m V k
    let P := ipmQualityPrecision I.m V k
    let r := heap+I.m*L
    ∃ out final c,
      Runs w p ω (roundExtractBody (b+6) (b+1) (b+7))
        (startState [I.n,I.m,graph,cost,mem (heap-2),L,P,one,heap,dest,J.m] mem pos)
        (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧ heap≤out ∧
      out≤r+roundMachineSpace (allocation 6 [I.n,L,P,r]) A L I.m+recoverScanSpace L J.m ∧
      ZeroFrom final.mem out ∧ (∀ a<dest,final.mem a=mem a) ∧
      c≤roundMachineCost (rate I.n) L I.n I.m+17*(I.m*L)+J.m*(100*L+240)+100 := by
  let I := connectedInitialInstance J.toInstance K
  let P := ipmQualityPrecision I.m V k
  let F := ipmQualityMinRatioFormat I.m V k hw
  let B := solverRoundProcedures b
  have hCtl := Num.hasAt_append_left hModule
  have atCtl (j : Fin 29) : p.procs[b+j.val]?=
      some ((solverRoundControl b init op)[j.val]'(by change j.val<29; exact j.isLt)) :=
    hCtl _ _
  let integer := b+29
  let less := integer+(Num.isIntegerModule integer 4).length
  let floor := less+(Num.lessModule less 4).length
  let shift := floor+(Num.floorModule floor 4).length
  let subtract := shift+(Num.shiftLeftModule shift 4).length
  let add := subtract+(Num.subtractModule subtract 4).length
  let zeroEntry := add+(Num.addModule add 4).length
  let packWord := zeroEntry+(Num.isZeroModule zeroEntry).length
  have hAux := Num.hasAt_append_right hModule
  change p.HasAt integer (solverRoundAux b) at hAux
  unfold solverRoundAux at hAux
  have hAux1 := Num.hasAt_append_right hAux
  have hAux2 := Num.hasAt_append_right hAux1
  have hAux3 := Num.hasAt_append_right hAux2
  have hAux4 := Num.hasAt_append_right hAux3
  have hAux5 := Num.hasAt_append_right hAux4
  have hAux6 := Num.hasAt_append_right hAux5
  have hAux7 := Num.hasAt_append_right hAux6
  have hAtinteger : p.HasAt integer (Num.isIntegerModule integer 4) := Num.hasAt_append_left hAux
  have hAtless : p.HasAt less (Num.lessModule less 4) := Num.hasAt_append_left hAux1
  have hAtfloor : p.HasAt floor (Num.floorModule floor 4) := Num.hasAt_append_left hAux2
  have hAtshift : p.HasAt shift (Num.shiftLeftModule shift 4) := Num.hasAt_append_left hAux3
  have hAtsubtract : p.HasAt subtract (Num.subtractModule subtract 4) := Num.hasAt_append_left hAux4
  have hAtadd : p.HasAt add (Num.addModule add 4) := Num.hasAt_append_left hAux5
  have hAtzero : p.HasAt zeroEntry (Num.isZeroModule zeroEntry) := Num.hasAt_append_left hAux6
  have hAtpackWord : p.HasAt packWord (Num.packWordModule packWord 4) := hAux7
  have h14 := (ipm_quality_parameter_words_fit I.m V k hw).1
  have h16 : 16<2^w := (by decide : 16<2^14).trans_le (Nat.pow_le_pow_right (by decide) h14)
  have h1 : 1<2^w := by omega
  have h4 : 0 < (4:ℕ) := by decide
  have h10 : 2*4+2≤w := by omega
  have hBase : Num.base 4<2^w := h16
  have hInteger := Num.isInteger_meetsContract h4 h1 (by omega) hAtinteger
  have hLess := Num.less_meetsContract h4 h1 hBase hAtless
  have hFloor := Num.floor_meetsContract h4 h1 hBase hAtfloor
  have hShift := Num.shiftLeft_meetsContract h4 h10 hAtshift
  have hSub := Num.subtract_meetsContract h4 h10 hAtsubtract
  have hAdd := Num.add_meetsContract h4 h10 hAtadd
  have hZero := Num.isZero_meetsContract (h:=4) h1 hAtzero
  have hPackWord := Num.packWord_meetsContract h1 hBase hAtpackWord
  have hCopyAt : p.HasAt B.copy [copyWords] := by
    intro j hj
    change j<1 at hj
    have he : j=0 := by omega
    subst j
    change p.procs[b+28]?=some copyWords
    exact atCtl ⟨28,by decide⟩
  have hCopy := copyWords_meetsContract (w:=w) hCopyAt
  have hAppend := roundAppendBlock_meetsContract (atCtl 26) hCopy
  have hLink : B.Linked w 4 P p op :=
    ⟨atCtl 10,atCtl 11,atCtl 12,atCtl 13,atCtl 14,atCtl 15,
      fun e => roundLinkRecord_meetsContract (atCtl 16) hAppend e,atCtl 17,hInteger,hLess,
      roundAvailability_meetsContract (atCtl 18) hFloor hShift hSub,
      roundPathZero_meetsContract (atCtl 19) hZero h1,
      fun q hit => roundDelta_meetsContract (atCtl 20) hLess q hit,
      fun q δ backward => roundStoreCoordinate_meetsContract (atCtl 21)
        (roundFlowArithmetic_meetsContract (atCtl 27) hAdd hSub) hCopy h1 q δ backward,
      hCopy,atCtl 22,atCtl 23,atCtl 24,atCtl 25⟩
  have hCopyFlow := epochFlowCopy_meetsContract (atCtl 6) hCopy
  have hScan := recoverScan_meetsContract (atCtl 7) (recoverWord_meetsContract (atCtl 8) hFloor hPackWord)
  exact roundExtract_connected_fromSearch D hD rate allocation R J K hp U V k hm hV hNums hLargeSq hLarge hw hBounds
    F rfl himpl B hLink hCopyFlow (atCtl 1) (atCtl 2) (atCtl 3) (atCtl 4) (atCtl 5)
    (atCtl 9) hScan hAlloc E old heap graph cost one dest before mem pos ω z fstar hstar hz
    hResult hBit hWords hRows hCosts hUnit hCost hGraph hOne hCap hDest hSpace

end MinCostFlow.IPM.Machine
