module

  public import MinCostFlow.Final.ConnectedPrograms
public import MinCostFlow.Final.CappedQuality
public import MinCostFlow.IPM.Machine.BoundedSolverWithV
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Scaling.ModulePlacement
import Mathlib.Tactic

/-!
# Word RAM linkage for capped quality

The connected solver passes the actual graph and its encoding.
Its read-only quality call selects the exponent at the fixed
edge cap, so every arithmetic and data structure call uses that
quality at the actual graph's numeric width.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine IPM IPM.Machine

/-- The capped quality entry follows the ordinary quality and bit-length entries. -/
def linkedCappedSolverProgram (threshold A : ℕ) (dispatch : SolverDispatch)
    (cycle forest : List Stmt) : Program :=
  let b := linkedConnectedQualityBase dispatch cycle forest
  Program.mk (boundedConnectedIPMRuntimeModule 0 dispatch ++ cycle ++ forest ++
    [Num.IPM.bitLengthBody b, integerQualityBody b A, cappedQualityBody (b+1) A threshold])

/-- All instructions of the linked capped solver are deterministic when
the cycle and forest code is deterministic. -/
theorem linkedCappedSolverProgram_deterministic (threshold A : ℕ) (e : SolverDispatch)
    (cycle forest : List Stmt) (hcycle : ∀ s ∈ cycle, s.NoRand)
    (hforest : ∀ s ∈ forest, s.NoRand) :
    (linkedCappedSolverProgram threshold A e cycle forest).IsDeterministic := by
  intro body h
  simp only [linkedCappedSolverProgram, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at h
  rcases h with ((h | h) | h) | rfl | rfl | rfl
  · exact boundedConnectedIPMRuntimeModule_noRand _ _ _ h
  · exact hcycle _ h
  · exact hforest _ h
  · exact Num.IPM.bitLengthModule_noRand _ _ List.mem_cons_self
  · exact integerQualityBody_noRand _ _
  · exact cappedQualityBody_noRand _ _ _

set_option maxRecDepth 4096 in
/-- The linked capped solver meets the compressed solver contract whenever the
connected-graph model and the two procedure modules satisfy their machine contracts at
the resulting precision (allowing forest rate and space to depend on `L`, and allocation on `w, L`). -/
theorem linkedCappedSolverProgram_meetsForestContract (w threshold A : ℕ)
    (resources : SolverForestResources) (e : SolverDispatch) (cycle forest : List Stmt)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hword : 2 < 2^w) (hQuality : e.quality = linkedConnectedQualityBase e cycle forest + 2)
    (hSupported : ∀ J : Circulation, J.n ≤ 2*J.m+1 → 0 < J.m →
      J.CostsBounded (J.m^10) → (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m^40) →
      let I := solverConnectedAugmented J
      let k := cappedQualityExponent threshold A I.m
      ∀ hw : ipmQualityParameterWordBits I.m (solverPenalty J.m) k ≤ w,
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverQualityForestDataStructuresAt w (linkedCappedSolverProgram threshold A e cycle forest) e
            ({resources with qualityExponent := k}) I (solverPenalty J.m) hw C D RC RD) :
    let r : SolverForestRuntimeResources := ⟨resources, cappedQualityExponent threshold A, cappedQualityCost⟩
    MeetsContract w (linkedCappedSolverProgram threshold A e cycle forest) 0
      (compressedSolverContract w (forestConnectedSolverRuntimeTime r) (forestConnectedSolverRuntimeWorkspace r)) := by
  intro r
  let b := linkedConnectedQualityBase e cycle forest
  have hall := hasAt_self (boundedConnectedIPMRuntimeModule 0 e ++ cycle ++ forest ++
    [Num.IPM.bitLengthBody b, integerQualityBody b A, cappedQualityBody (b+1) A threshold])
  have hmain := Num.hasAt_append_left (Num.hasAt_append_left (Num.hasAt_append_left hall))
  have hTail : (linkedCappedSolverProgram threshold A e cycle forest).HasAt b
      [Num.IPM.bitLengthBody b, integerQualityBody b A, cappedQualityBody (b+1) A threshold] := by
    simpa only [linkedCappedSolverProgram, b, linkedConnectedQualityBase,
      List.length_append, Nat.zero_add] using Num.hasAt_append_right hall
  have hSplit : (linkedCappedSolverProgram threshold A e cycle forest).HasAt b
      ([Num.IPM.bitLengthBody b] ++ [integerQualityBody b A, cappedQualityBody (b+1) A threshold]) :=
    hTail
  have hBit := Num.IPM.bitLength_meetsContract hword (Num.hasAt_append_left hSplit)
  have hRest := Num.hasAt_append_right hSplit
  change (linkedCappedSolverProgram threshold A e cycle forest).HasAt (b+1)
    ([integerQualityBody b A] ++ [cappedQualityBody (b+1) A threshold]) at hRest
  have hInteger := integerQuality_meetsContract (Num.hasAt_append_left hRest).head hBit
  have hCapBody : (linkedCappedSolverProgram threshold A e cycle forest).procs[e.quality]? =
      some (cappedQualityBody (b+1) A threshold) := by
    rw [hQuality]
    have hh := (Num.hasAt_append_right hRest).head
    simpa only [List.length_cons,List.length_nil,Nat.add_assoc,Nat.add_zero] using hh
  have hCap := cappedQuality_meetsContract hCapBody hInteger
  exact boundedConnectedIPMRuntime_meetsForestCompressedContract r e D hD hmain hCap hSupported

/-- `boundedConnectedIPMRuntimeModuleWithV 0 e` has the exact same length as `boundedConnectedIPMRuntimeModule 0 e`. -/
theorem boundedConnectedIPMRuntimeModuleWithV_eq_length (e : SolverDispatch) :
    (boundedConnectedIPMRuntimeModuleWithV 0 e).length = (boundedConnectedIPMRuntimeModule 0 e).length := by
  have hcV : (connectedSolverControlWithV 0 e).length = 13 := by simp [connectedSolverControlWithV]
  have hc : (connectedSolverControl 0 e).length = 13 := by simp [connectedSolverControl]
  have hsV : ∀ b, (solverSearchModuleWithV b e.cycleInit e.cycleOp).length =
      33 + (solverSearchAux (b + 33)).length := fun b => by
    simp [solverSearchModuleWithV, solverSearchControlWithV]; omega
  have hs : ∀ b, (solverSearchModule b e.cycleInit e.cycleOp).length =
      33 + (solverSearchAux (b + 33)).length := fun b => by
    simp [solverSearchModule, solverSearchControl]; omega
  unfold boundedConnectedIPMRuntimeModuleWithV boundedConnectedIPMRuntimeModule
  simp only [List.length_append, hcV, hc, connectedSolverOwnModulesWithV, connectedSolverOwnModules,
    List.length_cons, hsV, hs, solverRoundModule, solverRoundControl]

/-- `V`-passing variant of `linkedCappedSolverProgram`: replaces
`boundedConnectedIPMRuntimeModule` with `boundedConnectedIPMRuntimeModuleWithV`
(preserving every downstream module offset). -/
def linkedCappedSolverProgramWithV (threshold A : ℕ) (dispatch : SolverDispatch)
    (cycle forest : List Stmt) : Program :=
  let b := linkedConnectedQualityBase dispatch cycle forest
  Program.mk (boundedConnectedIPMRuntimeModuleWithV 0 dispatch ++ cycle ++ forest ++
    [Num.IPM.bitLengthBody b, integerQualityBody b A, cappedQualityBody (b+1) A threshold])

/-- All instructions of `linkedCappedSolverProgramWithV` are deterministic when
the cycle and forest code is deterministic. -/
theorem linkedCappedSolverProgramWithV_deterministic (threshold A : ℕ) (e : SolverDispatch)
    (cycle forest : List Stmt) (hcycle : ∀ s ∈ cycle, s.NoRand)
    (hforest : ∀ s ∈ forest, s.NoRand) :
    (linkedCappedSolverProgramWithV threshold A e cycle forest).IsDeterministic := by
  intro body h
  simp only [linkedCappedSolverProgramWithV, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at h
  rcases h with ((h | h) | h) | rfl | rfl | rfl
  · exact boundedConnectedIPMRuntimeModuleWithV_noRand _ _ _ h
  · exact hcycle _ h
  · exact hforest _ h
  · exact Num.IPM.bitLengthModule_noRand _ _ List.mem_cons_self
  · exact integerQualityBody_noRand _ _
  · exact cappedQualityBody_noRand _ _ _

set_option maxRecDepth 4096 in
/-- `V`-passing variant of `linkedCappedSolverProgram_meetsForestContract`. -/
theorem linkedCappedSolverProgramWithV_meetsForestContract (w threshold A : ℕ)
    (resources : SolverForestResources) (e : SolverDispatch) (cycle forest : List Stmt)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hword : 2 < 2^w) (hQuality : e.quality = linkedConnectedQualityBase e cycle forest + 2)
    (hSupported : ∀ J : Circulation, J.n ≤ 2*J.m+1 → 0 < J.m →
      J.CostsBounded (J.m^10) → (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m^40) →
      let I := solverConnectedAugmented J
      let k := cappedQualityExponent threshold A I.m
      ∀ hw : ipmQualityParameterWordBits I.m (solverPenalty J.m) k ≤ w,
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverQualityForestDataStructuresWithVAt w (linkedCappedSolverProgramWithV threshold A e cycle forest) e
            ({resources with qualityExponent := k}) I (solverPenalty J.m) hw C D RC RD) :
    let r : SolverForestRuntimeResources := ⟨resources, cappedQualityExponent threshold A, cappedQualityCost⟩
    MeetsContract w (linkedCappedSolverProgramWithV threshold A e cycle forest) 0
      (compressedSolverContract w (forestConnectedSolverRuntimeTime r) (forestConnectedSolverRuntimeWorkspace r)) := by
  intro r
  let b := linkedConnectedQualityBase e cycle forest
  have hbEq : (boundedConnectedIPMRuntimeModuleWithV 0 e ++ cycle ++ forest).length = b := by
    simp only [b, linkedConnectedQualityBase, List.length_append,
      boundedConnectedIPMRuntimeModuleWithV_eq_length]
  have hall := hasAt_self (boundedConnectedIPMRuntimeModuleWithV 0 e ++ cycle ++ forest ++
    [Num.IPM.bitLengthBody b, integerQualityBody b A, cappedQualityBody (b+1) A threshold])
  have hmain := Num.hasAt_append_left (Num.hasAt_append_left (Num.hasAt_append_left hall))
  have hTail : (linkedCappedSolverProgramWithV threshold A e cycle forest).HasAt b
      [Num.IPM.bitLengthBody b, integerQualityBody b A, cappedQualityBody (b+1) A threshold] := by
    have hr := Num.hasAt_append_right hall
    rwa [Nat.zero_add, hbEq] at hr
  have hSplit : (linkedCappedSolverProgramWithV threshold A e cycle forest).HasAt b
      ([Num.IPM.bitLengthBody b] ++ [integerQualityBody b A, cappedQualityBody (b+1) A threshold]) :=
    hTail
  have hBit := Num.IPM.bitLength_meetsContract hword (Num.hasAt_append_left hSplit)
  have hRest := Num.hasAt_append_right hSplit
  change (linkedCappedSolverProgramWithV threshold A e cycle forest).HasAt (b+1)
    ([integerQualityBody b A] ++ [cappedQualityBody (b+1) A threshold]) at hRest
  have hInteger := integerQuality_meetsContract (Num.hasAt_append_left hRest).head hBit
  have hCapBody : (linkedCappedSolverProgramWithV threshold A e cycle forest).procs[e.quality]? =
      some (cappedQualityBody (b+1) A threshold) := by
    rw [hQuality]
    have hh := (Num.hasAt_append_right hRest).head
    simpa only [List.length_cons,List.length_nil,Nat.add_assoc,Nat.add_zero] using hh
  have hCap := cappedQuality_meetsContract hCapBody hInteger
  exact boundedConnectedIPMRuntimeWithV_meetsForestCompressedContract r e D hD hmain hCap hSupported

/-- The linked capped solver meets the compressed solver contract whenever the
connected-graph model and the two procedure modules satisfy their machine contracts at
the resulting precision. -/
theorem linkedCappedSolverProgram_meetsConnectedContract (w threshold A : ℕ)
    (resources : SolverResources) (e : SolverDispatch) (cycle forest : List Stmt)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hword : 2 < 2^w) (hQuality : e.quality = linkedConnectedQualityBase e cycle forest + 2)
    (hSupported : ∀ J : Circulation, J.n ≤ 2*J.m+1 → 0 < J.m →
      J.CostsBounded (J.m^10) → (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m^40) →
      let I := solverConnectedAugmented J
      let k := cappedQualityExponent threshold A I.m
      ∀ hw : ipmQualityParameterWordBits I.m (solverPenalty J.m) k ≤ w,
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverQualityConnectedDataStructuresAt w (linkedCappedSolverProgram threshold A e cycle forest) e
            ({resources with qualityExponent := k}) I (solverPenalty J.m) hw C D RC RD) :
    let r : SolverRuntimeResources := ⟨resources, cappedQualityExponent threshold A, cappedQualityCost⟩
    MeetsContract w (linkedCappedSolverProgram threshold A e cycle forest) 0
      (compressedSolverContract w (connectedSolverRuntimeTime r) (connectedSolverRuntimeWorkspace r)) :=
  linkedCappedSolverProgram_meetsForestContract w threshold A resources.toForestResources e cycle forest D hD
    hword hQuality (fun J hJn hm hCost hCap hw =>
      let ⟨C, RC, RD, hDS⟩ := hSupported J hJn hm hCost hCap hw
      ⟨C, RC, RD, hDS.toForest⟩)

/-- The linked capped solver meets the compressed solver contract
whenever the selected model and the two procedure modules satisfy
their machine contracts at the resulting precision. -/
theorem linkedCappedSolverProgram_meetsContract (w threshold A : ℕ)
    (resources : SolverResources) (e : SolverDispatch) (cycle forest : List Stmt)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hword : 2 < 2^w) (hQuality : e.quality = linkedConnectedQualityBase e cycle forest + 2)
    (hSupported : ∀ J : Circulation, J.n ≤ 2*J.m+1 → 0 < J.m →
      J.CostsBounded (J.m^10) → (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m^40) →
      let I := solverConnectedAugmented J
      let k := cappedQualityExponent threshold A I.m
      ∀ hw : ipmQualityParameterWordBits I.m (solverPenalty J.m) k ≤ w,
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverQualityDataStructuresAt w (linkedCappedSolverProgram threshold A e cycle forest) e
            ({resources with qualityExponent := k}) I (solverPenalty J.m) hw C D RC RD) :
    let r : SolverRuntimeResources := ⟨resources, cappedQualityExponent threshold A, cappedQualityCost⟩
    MeetsContract w (linkedCappedSolverProgram threshold A e cycle forest) 0
      (compressedSolverContract w (connectedSolverRuntimeTime r) (connectedSolverRuntimeWorkspace r)) :=
  linkedCappedSolverProgram_meetsConnectedContract w threshold A resources e cycle forest D hD
    hword hQuality (fun J hJn hm hCost hCap hw =>
      let ⟨C, RC, RD, hDS⟩ := hSupported J hJn hm hCost hCap hw
      ⟨C, RC, RD, hDS.toConnected⟩)

end MinCostFlow.Final
