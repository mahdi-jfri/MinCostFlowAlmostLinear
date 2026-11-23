module

public import MinCostFlow.IPM.Machine.RoundExtractFromSearch
public import MinCostFlow.Num.Floor
public import MinCostFlow.Num.PackWord
public import MinCostFlow.Num.Add
public import MinCostFlow.Num.Subtract
public import MinCostFlow.Num.ShiftLeft
public import MinCostFlow.Num.IsInteger
import MinCostFlow.Num.ModulePlacement
import Mathlib.Tactic

/-!
# The linked exact rounder and recovery

The bounded solver rounds the accepted dyadic flow with the shared
dynamic forest. Its own procedures are linked here. Only the forest
Init and six operation addresses are parameters.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding Scaling

/-- Rounding entries below the shared arithmetic modules. -/
def solverRoundProcedures (b : ℕ) : RoundProcedures :=
  let integer := b+29
  let less := integer+(Num.isIntegerModule integer 4).length
  { findRoot := b+10,
    pathSum := b+11,
    pathMin := b+12,
    pathAdd := b+13,
    link := b+14,
    cut := b+15,
    pack := b+16,
    packLink := b+17,
    availability := b+18,
    pathZero := b+19,
    delta := b+20,
    coordinate := b+21,
    cleanup := b+22,
    push := b+23,
    repair := b+24,
    relink := b+25,
    integer := integer, less := less, copy := b+28 }

/-- The control block includes the extraction entry, rounder and scan. -/
def solverRoundControl (b init : ℕ) (op : ℕ → ℕ) : List Stmt :=
  let B := solverRoundProcedures b
  let integer := b+29
  let less := integer+(Num.isIntegerModule integer 4).length
  let floor := less+(Num.lessModule less 4).length
  let shift := floor+(Num.floorModule floor 4).length
  let subtract := shift+(Num.shiftLeftModule shift 4).length
  let add := subtract+(Num.subtractModule subtract 4).length
  let zeroEntry := add+(Num.addModule add 4).length
  let packWord := zeroEntry+(Num.isZeroModule zeroEntry).length
  [roundExtractBody (b+6) (b+1) (b+7),
   roundMachineBody init (b+2),
   roundLoopBody (b+2) (b+3),
   roundEdgeBody B (b+4),
   roundFractionalBody B (b+5),
   roundConnectedBody B (b+9),
   epochFlowCopyBody B.copy,
   recoverScanBody (b+7) (b+8),
   recoverWordBody floor packWord,
   roundRepairRelinkBody B,
   roundFindRootBody (op 0),
   roundPathSumBody (op 5),
   roundForestPathMinBody (op 4),
   roundPathAddBody (op 3),
   roundLinkBody (op 1),
   roundFlushCutBody B.copy (op 2),
   roundLinkRecordBody (b+26),
   roundPackLinkBody B.pack B.link,
   roundAvailabilityBody floor shift subtract,
   roundPathZeroBody zeroEntry,
   roundDeltaBody B.less,
   roundStoreCoordinateBody (b+27) B.copy,
   roundCleanupBody B.cleanup B.pathMin B.pathZero B.cut,
   roundCyclePushBody B.pathMin B.delta B.coordinate B.pathAdd,
   roundCycleRepairBody B.push B.cleanup,
   roundRelinkBody B.integer B.availability B.packLink,
   roundAppendBlockBody B.copy,
   roundFlowArithmeticBody add subtract,
   copyWords]

/-- Shared numeric modules in their contiguous address interval. -/
def solverRoundAux (b : ℕ) : List Stmt :=
  let integer := b+29
  let less := integer+(Num.isIntegerModule integer 4).length
  let floor := less+(Num.lessModule less 4).length
  let shift := floor+(Num.floorModule floor 4).length
  let subtract := shift+(Num.shiftLeftModule shift 4).length
  let add := subtract+(Num.subtractModule subtract 4).length
  let zeroEntry := add+(Num.addModule add 4).length
  let packWord := zeroEntry+(Num.isZeroModule zeroEntry).length
  Num.isIntegerModule integer 4 ++ (Num.lessModule less 4 ++ (Num.floorModule floor 4 ++ (Num.shiftLeftModule shift 4 ++ (Num.subtractModule subtract 4 ++ (Num.addModule add 4 ++ (Num.isZeroModule zeroEntry ++ (Num.packWordModule packWord 4)))))))

/-- The recovered circulation is returned from the first entry. -/
def solverRoundModule (b init : ℕ) (op : ℕ → ℕ) : List Stmt :=
  solverRoundControl b init op ++ solverRoundAux b

private theorem solverRoundControl_noRand (b init : ℕ) (op : ℕ → ℕ) :
    ∀ body∈solverRoundControl b init op,body.NoRand := by
  intro body hb
  simp only [solverRoundControl,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact roundExtract_noRand _ _ _
  · exact roundMachine_noRand _ _
  · exact roundLoop_noRand _ _
  · exact roundEdge_noRand _ _
  · exact roundFractional_noRand _ _
  · exact roundConnected_noRand _ _
  · exact epochFlowCopy_noRand _
  · exact recoverScan_noRand _ _
  · exact recoverWord_noRand _ _
  · exact roundRepairRelink_noRand _
  · exact roundFindRoot_noRand _
  · exact roundPathSum_noRand _
  · exact roundForestPathMin_noRand _
  · exact roundPathAdd_noRand _
  · exact roundLink_noRand _
  · exact roundFlushCut_noRand _ _
  · exact roundLinkRecord_noRand _
  · exact roundPackLink_noRand _ _
  · exact roundAvailability_noRand _ _ _
  · exact roundPathZero_noRand _
  · exact roundDelta_noRand _
  · exact roundStoreCoordinate_noRand _ _
  · exact roundCleanup_noRand _ _ _ _
  · exact roundCyclePush_noRand _ _ _ _
  · exact roundCycleRepair_noRand _ _
  · exact roundRelink_noRand _ _ _
  · exact roundAppendBlock_noRand _
  · exact roundFlowArithmetic_noRand _ _
  · simp [copyWords,forRange,forUp,Stmt.NoRand]

/-- All rounding and recovery statements are deterministic. -/
theorem solverRoundModule_noRand (b init : ℕ) (op : ℕ → ℕ) :
    ∀ body∈solverRoundModule b init op,body.NoRand := by
  intro body h
  simp only [solverRoundModule,solverRoundAux,List.mem_append] at h
  rcases h with h | h | h | h | h | h | h | h | h
  · exact solverRoundControl_noRand b init op body h
  · exact Num.isIntegerModule_noRand _ _ _ h
  · exact Num.lessModule_noRand _ _ _ h
  · exact Num.floorModule_noRand _ _ _ h
  · exact Num.shiftLeftModule_noRand _ _ _ h
  · exact Num.subtractModule_noRand _ _ _ h
  · exact Num.addModule_noRand _ _ _ h
  · simp only [Num.isZeroModule,List.mem_singleton] at h
    subst body
    exact Num.isZeroBody_noRand _
  · simp only [Num.packWordModule,List.mem_singleton] at h
    subst body
    exact Num.packWordBody_noRand _ _

set_option maxRecDepth 4096 in
set_option maxHeartbeats 520000 in
/-- The recovery module uses the forest contract at the chosen precision.
Everything else, including the numeric calls and final output scan,
is verified by the linked code. -/
theorem solverRoundModule_fromSearch {w b init A : ℕ} {p : Program} {op : ℕ → ℕ}
    (D : DynForest) (hD : D.IsSpec) (rate : ℕ → ℕ)
    (allocation : ℕ → List ℕ → ℕ) (R : DSRep D.State)
    (J : Circulation) (K : ℤ) (hp : ∀ e,1≤J.capacity e)
    (U V : ℕ) (hm : 0 < J.m) (hV : 1≤V)
    (hNums : NumbersBounded J.toInstance (U:ℝ)) (hPenalty : 0≤(K:ℝ))
    (hLarge : 2*J.toInstance.m*(U:ℝ)<(K:ℝ))
    (hw : ipmParameterWordBits (initialInstance J.toInstance K).m V≤w)
    (hBounds : NumbersBounded (initialInstance J.toInstance K) (V:ℝ))
    (hModule : p.HasAt b (solverRoundModule b init op))
    (himpl : R.Implements w p init op (forestMachineContract D w 4
      (ipmLimbs (initialInstance J.toInstance K).m V)
      (ipmPrecision (initialInstance J.toInstance K).m V) rate allocation))
    (hAlloc : ∀ b u v a heap,allocation 0 [b,u,heap]≤A ∧ allocation 4 [b,u,v,heap]≤A ∧
      allocation 3 [b,u,v,a,heap]≤A ∧ allocation 2 [b,u,v,heap]≤A ∧
      allocation 1 [b,a,heap]≤A ∧ allocation 5 [b,u,v,heap]≤A)
    (E old heap graph cost one dest : ℕ) (before mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (z : ℤ)
    (fstar : Fin (initialInstance J.toInstance K).m → ℝ)
    (hstar : (initialInstance J.toInstance K).IsMinCostFlow fstar)
    (hz : (initialInstance J.toInstance K).cost fstar=(z:ℝ))
    (hResult : TargetOffsetResult (ipmMinRatioFormat (initialInstance J.toInstance K).m V hw)
      (initialInstance J.toInstance K) E old heap z z before mem)
    (hBit : mem (heap-1)=1)
    (hWords : let I := initialInstance J.toInstance K
      ∀ a∈[I.n,I.m,graph,cost,mem (heap-2),ipmLimbs I.m V,ipmPrecision I.m V,one,heap,dest,J.m],a<2^w)
    (hRows : ZeroLowerAt mem graph (initialInstance J.toInstance K))
    (hCosts : let I := initialInstance J.toInstance K
      RoundCostsAt I mem cost 4 (ipmLimbs I.m V))
    (hUnit : let I := initialInstance J.toInstance K
      RatAt mem one 4 (ipmLimbs I.m V) (ipmPrecision I.m V) 1)
    (hCost : cost+(initialInstance J.toInstance K).m*ipmLimbs (initialInstance J.toInstance K).m V≤heap)
    (hGraph : graph+(zeroLowerWords (initialInstance J.toInstance K)).length≤heap)
    (hOne : one+ipmLimbs (initialInstance J.toInstance K).m V≤heap)
    (hCap : ∀ e,J.capacity e<2^w) (hDest : dest+J.m≤heap)
    (hSpace : let I := initialInstance J.toInstance K
      let L := ipmLimbs I.m V
      let P := ipmPrecision I.m V
      let r := heap+I.m*L
      r+roundMachineSpace (allocation 6 [I.n,L,P,r]) A L I.m+recoverScanSpace L J.m<2^w) :
    let I := initialInstance J.toInstance K
    let L := ipmLimbs I.m V
    let P := ipmPrecision I.m V
    let r := heap+I.m*L
    ∃ out final c,
      Runs w p ω (roundExtractBody (b+6) (b+1) (b+7))
        (startState [I.n,I.m,graph,cost,mem (heap-2),L,P,one,heap,dest,J.m] mem pos)
        (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧ heap≤out ∧
      out≤r+roundMachineSpace (allocation 6 [I.n,L,P,r]) A L I.m+recoverScanSpace L J.m ∧
      ZeroFrom final.mem out ∧ (∀ a<dest,final.mem a=mem a) ∧
      c≤roundMachineCost (rate I.n) L I.n I.m+17*(I.m*L)+J.m*(100*L+240)+100 := by
  let I := initialInstance J.toInstance K
  let P := ipmPrecision I.m V
  let F := ipmMinRatioFormat I.m V hw
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
  have h14 := (ipm_parameter_words_fit I.m V hw).1
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
  exact roundExtract_fromSearch D hD rate allocation R J K hp U V hm hV hNums hPenalty hLarge hw hBounds
    F rfl himpl B hLink hCopyFlow (atCtl 1) (atCtl 2) (atCtl 3) (atCtl 4) (atCtl 5)
    (atCtl 9) hScan hAlloc E old heap graph cost one dest before mem pos ω z fstar hstar hz
    hResult hBit hWords hRows hCosts hUnit hCost hGraph hOne hCap hDest hSpace

set_option maxHeartbeats 450000 in
/-- The recovery module uses the forest contract at the chosen precision.
Everything else, including the numeric calls and final output scan,
is verified by the linked code. -/
theorem solverRoundModule_fromSearch_widened {w b init A : ℕ} {p : Program} {op : ℕ → ℕ}
    (D : DynForest) (hD : D.IsSpec) (rate : ℕ → ℕ)
    (allocation : ℕ → List ℕ → ℕ) (R : DSRep D.State)
    (J : Circulation) (K : ℤ) (hp : ∀ e,1≤J.capacity e)
    (U V k : ℕ) (hm : 0 < J.m) (hV : 1≤V)
    (hNums : NumbersBounded J.toInstance (U:ℝ)) (hPenalty : 0≤(K:ℝ))
    (hLarge : 2*J.toInstance.m*(U:ℝ)<(K:ℝ))
    (hw : ipmQualityParameterWordBits (initialInstance J.toInstance K).m V k≤w)
    (hBounds : NumbersBounded (initialInstance J.toInstance K) (V:ℝ))
    (hModule : p.HasAt b (solverRoundModule b init op))
    (himpl : R.Implements w p init op (forestMachineContract D w 4
      (ipmQualityLimbs (initialInstance J.toInstance K).m V k)
      (ipmQualityPrecision (initialInstance J.toInstance K).m V k) rate allocation))
    (hAlloc : ∀ b u v a heap,allocation 0 [b,u,heap]≤A ∧ allocation 4 [b,u,v,heap]≤A ∧
      allocation 3 [b,u,v,a,heap]≤A ∧ allocation 2 [b,u,v,heap]≤A ∧
      allocation 1 [b,a,heap]≤A ∧ allocation 5 [b,u,v,heap]≤A)
    (E old heap graph cost one dest : ℕ) (before mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (z : ℤ)
    (fstar : Fin (initialInstance J.toInstance K).m → ℝ)
    (hstar : (initialInstance J.toInstance K).IsMinCostFlow fstar)
    (hz : (initialInstance J.toInstance K).cost fstar=(z:ℝ))
    (hResult : TargetOffsetResult (ipmQualityMinRatioFormat (initialInstance J.toInstance K).m V k hw)
      (initialInstance J.toInstance K) E old heap z z before mem)
    (hBit : mem (heap-1)=1)
    (hWords : let I := initialInstance J.toInstance K
      ∀ a∈[I.n,I.m,graph,cost,mem (heap-2),ipmQualityLimbs I.m V k,ipmQualityPrecision I.m V k,one,heap,dest,J.m],a<2^w)
    (hRows : ZeroLowerAt mem graph (initialInstance J.toInstance K))
    (hCosts : let I := initialInstance J.toInstance K
      RoundCostsAt I mem cost 4 (ipmQualityLimbs I.m V k))
    (hUnit : let I := initialInstance J.toInstance K
      RatAt mem one 4 (ipmQualityLimbs I.m V k) (ipmQualityPrecision I.m V k) 1)
    (hCost : cost+(initialInstance J.toInstance K).m*ipmQualityLimbs (initialInstance J.toInstance K).m V k≤heap)
    (hGraph : graph+(zeroLowerWords (initialInstance J.toInstance K)).length≤heap)
    (hOne : one+ipmQualityLimbs (initialInstance J.toInstance K).m V k≤heap)
    (hCap : ∀ e,J.capacity e<2^w) (hDest : dest+J.m≤heap)
    (hSpace : let I := initialInstance J.toInstance K
      let L := ipmQualityLimbs I.m V k
      let P := ipmQualityPrecision I.m V k
      let r := heap+I.m*L
      r+roundMachineSpace (allocation 6 [I.n,L,P,r]) A L I.m+recoverScanSpace L J.m<2^w) :
    let I := initialInstance J.toInstance K
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
  let I := initialInstance J.toInstance K
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
  exact roundExtract_fromSearch_widened D hD rate allocation R J K hp U V k hm hV hNums hPenalty hLarge hw hBounds
    F rfl himpl B hLink hCopyFlow (atCtl 1) (atCtl 2) (atCtl 3) (atCtl 4) (atCtl 5)
    (atCtl 9) hScan hAlloc E old heap graph cost one dest before mem pos ω z fstar hstar hz
    hResult hBit hWords hRows hCosts hUnit hCost hGraph hOne hCap hDest hSpace

end MinCostFlow.IPM.Machine
