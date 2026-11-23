module

public import MinCostFlow.LastLevelProgram.PackedInitializer
import MinCostFlow.DynSpanner.Program.DynGraphBatch
import MinCostFlow.DynSpanner.Program.GraphTranslateProcs
import MinCostFlow.DynSpanner.Program.SortOps
import MinCostFlow.LastLevelProgram.BranchGraph
import MinCostFlow.LastLevelProgram.BranchStretch
import MinCostFlow.LastLevelProgram.BranchStretchSources
import MinCostFlow.LastLevelProgram.CollectionHeader
import MinCostFlow.LastLevelProgram.ConnectedLSST
import MinCostFlow.LastLevelProgram.LoopOnlyBranch
import MinCostFlow.LastLevelProgram.PackEndpoints
import MinCostFlow.LastLevelProgram.Readout
import MinCostFlow.LastLevelProgram.RelocatedTreeCall
import MinCostFlow.LastLevelProgram.RoundLoop
import MinCostFlow.LastLevelProgram.StagedAppendProof
import MinCostFlow.LastLevelProgram.StagedController
import MinCostFlow.LastLevelProgram.TraversalDistances
import MinCostFlow.LastLevelProgram.UnitWeights
import MinCostFlow.LastLevelProgram.WeightUpdateCall
import MinCostFlow.Num.AddCarry
import MinCostFlow.Num.Copy
import MinCostFlow.Num.FixedDivide
import MinCostFlow.Num.FixedMultiply
import MinCostFlow.Num.IntegerDivide
import MinCostFlow.Num.NegateCarry
import MinCostFlow.Num.ShiftLeft
import MinCostFlow.Num.SignExtend
import MinCostFlow.Num.Subtract
import MinCostFlow.Num.UnsignedLess
import MinCostFlow.Scaling.ClogTwoProgram

/-!
# Determinism of the packed last-level program

The standalone last-level program `packedLastLevelProgram guest d c` implements Definition 5.8
(pages 19–20) without using `rand`, regardless of the guest program `guest`. The guest enters only
through `relocatedTreeProcedures`, whose relocated statements already contain no `rand`
(`relocatedTreeProcedures_noRand`).

We check each installed sub-module structurally: external modules supply their own `NoRand` lemmas,
the four unexposed bodies (`dispatchRuntimeInit`, `stagedPackedRoundBody`,
`rootedAncestorTableBody`, `rootedDistanceBody`) carry `NoRand` lemmas in their defining files, and
every remaining exposed body is verified directly by unfolding its statement constructors. Combining
the blocks proves `packedLastLevelProgram_isDeterministic`.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM

private def AllNoRand (xs : List Stmt) : Prop :=
  ∀ s ∈ xs, s.NoRand

private theorem allNoRand_nil : AllNoRand [] := by
  intro _ h; cases h

private theorem allNoRand_cons {s : Stmt} {xs : List Stmt}
    (hs : s.NoRand) (hxs : AllNoRand xs) : AllNoRand (s :: xs) := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact hs
  · exact hxs t ht

private theorem allNoRand_append {xs ys : List Stmt}
    (hxs : AllNoRand xs) (hys : AllNoRand ys) : AllNoRand (xs ++ ys) := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · exact hxs s hs
  · exact hys s hs

private theorem allNoRand_replicate_nop (n : ℕ) : AllNoRand (List.replicate n .nop) := by
  intro s hs
  rw [List.eq_of_mem_replicate hs]
  trivial

private theorem stagedAddressAssignments_noRand (rs : List ℕ) (es : List Expr) :
    (stagedAddressAssignments rs es).NoRand := by
  induction rs generalizing es with
  | nil => simp [stagedAddressAssignments, Stmt.NoRand]
  | cons r rs ih =>
    cases es with
    | nil => simp [stagedAddressAssignments, Stmt.NoRand]
    | cons e es => simp [stagedAddressAssignments, Stmt.NoRand, ih es]

private theorem copyWords_noRand : copyWords.NoRand := by
  simp [copyWords, forRange, forUp, Stmt.NoRand]

/-- The input table preparation module uses no `rand` statement. -/
theorem packedInputTableModule_noRand (b : ℕ) :
    ∀ s ∈ packedInputTableModule b, s.NoRand := by
  change AllNoRand (packedInputTableModule b)
  unfold packedInputTableModule
  refine allNoRand_append ?_ ?_
  · refine allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_
      (allNoRand_cons ?_ (allNoRand_cons ?_ allNoRand_nil)))))
    · simp [representativeKeyBody, Stmt.NoRand]
    · simp [packVertexIndexBody, packVertexLoop, forRange, forUp, Stmt.NoRand]
    · simp [packEdgeBody, packEdgeLoop, forRange, forUp, Stmt.NoRand]
    · exact packEndpointsBody_noRand
    · simp [stretchIndexKeyTableBody, representativeKeyScan, representativeKeyScanStep,
        forRange, forUp, Stmt.NoRand]
    · simp [stretchIndexScanBody, stretchIndexScanSetup, stretchIndexScan,
        stretchIndexScanStep, forRange, forUp, Stmt.NoRand]
  · refine allNoRand_cons (Num.unsignedLessBody_noRand _) allNoRand_nil

/-- The initializer format module uses no `rand` statement. -/
theorem packedInitializerFormatModule_noRand
    (b log scanPrecision weightWidth scanWidth convert : ℕ) :
    ∀ s ∈ packedInitializerFormatModule b log scanPrecision weightWidth scanWidth convert,
      s.NoRand := by
  change AllNoRand _
  unfold packedInitializerFormatModule
  refine allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_
    (allNoRand_cons ?_ (allNoRand_cons ?_ allNoRand_nil)))))
  · simp [scaleWordBody, Stmt.NoRand]
  · simp [precisionWordBody, Stmt.NoRand]
  · simp [guestSimulationWidthBody, Stmt.NoRand]
  · simp [setupAndPackGuestBody, Stmt.NoRand]
  · simp [guestFormatSetupBody, Stmt.NoRand]
  · simp [packGuestLengthsBody, packGuestLengthsLoop, forRange, forUp, Stmt.NoRand]

/-- The format-scan module uses no `rand` statement. -/
theorem packedFormatScansModule_noRand (b log : ℕ) :
    ∀ s ∈ packedFormatScansModule b log, s.NoRand := by
  change AllNoRand _
  unfold packedFormatScansModule
  refine allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_
    (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_
      (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_
        allNoRand_nil)))))))))))
  · simp [queryPrecisionBody, Stmt.NoRand]
  · simp [weightBoundWidthBody, Stmt.NoRand]
  · simp [guestWidthBody, guestWidthLoop, forRange, forUp, Stmt.NoRand]
  · simp [commonLengthShiftBody, commonLengthShiftLoop, forRange, forUp, Stmt.NoRand]
  · simp [lowerLengthShiftBody, Stmt.NoRand]
  · simp [blockValuationBody, blockValuationLoop, forRange, forUp, Stmt.NoRand]
  · simp [blockValuationStepBody, Stmt.NoRand]
  · simp [limbValuationBody, Stmt.NoRand]
  · simp [raiseGuestWidthBody, Stmt.NoRand]
  · simp [blockWidthBody, blockWidthLoop, forRange, forUp, Stmt.NoRand]
  · simp [blockWidthStepBody, Stmt.NoRand]
  · simp [solverLimbSizeBody, Stmt.NoRand]

/-- The initial-weights module uses no `rand` statement. -/
theorem packedInitialWeightsModule_noRand (b round : ℕ) :
    ∀ s ∈ packedInitialWeightsModule b round, s.NoRand := by
  change AllNoRand _
  unfold packedInitialWeightsModule
  refine allNoRand_cons initCollectionBody_noRand (allNoRand_cons ?_ (allNoRand_cons ?_ allNoRand_nil))
  · simp [stagedInitialWeightSetup, stagedAfterRoundUnitBody, stagedStretchUnitBody,
      stagedInitialWeightsBody, stagedRoundWeightCursor, Stmt.NoRand]
  · simp [stridedUnitWeightBody, stridedUnitWeightLoop, forRange, forUp, Stmt.NoRand]

/-- The four-bit round arithmetic module uses no `rand` statement. -/
theorem packedRoundArithmeticModule_noRand (b : ℕ) :
    ∀ s ∈ packedRoundArithmeticModule b, s.NoRand := by
  change AllNoRand _
  unfold packedRoundArithmeticModule
  simp only [List.append_assoc]
  refine allNoRand_append ?_ (allNoRand_append ?_ (allNoRand_append ?_ (allNoRand_append ?_
    (allNoRand_append ?_ (allNoRand_append ?_ (allNoRand_append ?_ (allNoRand_append ?_
      (allNoRand_append ?_ (allNoRand_append ?_ ?_)))))))))
  · refine allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_
      (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_
        (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_
          (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_
            (allNoRand_cons copyWords_noRand allNoRand_nil))))))))))))))))
    · simp [stretchWeightRoundBody, Stmt.NoRand]
    · simp [treeStretchRoundBody, Stmt.NoRand]
    · simp [buildTreeTablesBody, Stmt.NoRand]
    · simp [traverseTreeQueueBody, traverseTreeQueue, initializeTreeQueue, scanTreeQueueVertex,
        readTreeQueueVertex, scanTreeQueueRecord, Stmt.NoRand]
    · exact rootedDistanceBody_noRand _
    · simp [rootDistanceStepBody, Stmt.NoRand]
    · exact rootedAncestorTableBody_noRand _
    · simp [ancestorRowBody, ancestorRowLoop, forRange, forUp, Stmt.NoRand]
    · simp [rootedStretchRoundBody, stretchRoundLoop, forRange, forUp, Stmt.NoRand]
    · simp [edgeStretchQueryBody, Stmt.NoRand]
    · simp [rootedTreeAncestorBody, depthTableAncestorQuery, prepareAncestorQuery,
        readEndpointDepths, orientDepth, ancestorQuery, climbBitsLoop, climbBitBody,
        alignedAncestor, climbTogetherLoop, climbTogetherBody, forRange, forUp, Stmt.NoRand]
    · simp [edgeStretchBody, Stmt.NoRand]
    · simp [pathLengthBody, Stmt.NoRand]
    · simp [weightRoundBody, weightRoundLoop, forRange, forUp, Stmt.NoRand]
    · simp [widenWeightBody, Stmt.NoRand]
    · simp [stretchFromLengthBody, Stmt.NoRand]
  · exact allNoRand_cons (Num.addCarryBody_noRand _ _) allNoRand_nil
  · exact Num.subtractModule_noRand _ _
  · exact allNoRand_cons (Num.negateCarryBody_noRand _ _) allNoRand_nil
  · exact allNoRand_replicate_nop 6
  · refine allNoRand_cons ?_ (allNoRand_cons (weightUpdateBody_noRand _ _ _) allNoRand_nil)
    simp [narrowWeightBody, Stmt.NoRand]
  · exact Num.signExtendModule_noRand _ _
  · exact Num.fixedDivideModule_noRand _ _
  · exact Num.fixedMultiplyModule_noRand _ _
  · exact Num.integerDivideModule_noRand _ _
  · exact allNoRand_cons Num.copyBody_noRand allNoRand_nil

/-- The round buffer and packing module uses no `rand` statement. -/
theorem packedRoundBufferModule_noRand (b arithmetic : ℕ) :
    ∀ s ∈ packedRoundBufferModule b arithmetic, s.NoRand := by
  change AllNoRand _
  unfold packedRoundBufferModule
  refine allNoRand_append ?_ (Num.shiftLeftModule_noRand _ _)
  refine allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_
    (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_
      allNoRand_nil)))))))
  · simp [packWideValuesBody, forRange, forUp, Stmt.NoRand]
  · simp [packWideWeightsBody, forRange, forUp, Stmt.NoRand]
  · simp [denominatorBody, Stmt.NoRand]
  · simp [selectedAdjacencyBody, originalTreeAdjacency, originalTreeAdjacencyStep,
      readSelectedTreeEdge, forRange, forUp, Stmt.NoRand]
  · simp [pushTreeEdgeBody, Stmt.NoRand]
  · simp [pushTreeIncidenceBody, pushTreeIncidence, Stmt.NoRand]
  · simp [packGuestWeightsBody, packPrecisionLoop, forRange, forUp, Stmt.NoRand]
  · simp [storeWordBody, storeWordLoop, forRange, forUp, Stmt.NoRand]

/-- The branch publication module uses no `rand` statement. -/
theorem packedBranchModule_noRand (b copy : ℕ) :
    ∀ s ∈ packedBranchModule b copy, s.NoRand := by
  change AllNoRand _
  unfold packedBranchModule
  refine allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_
    (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons (copyBranchStretchBody_noRand _)
      (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_
        (allNoRand_cons ?_ (allNoRand_cons writeBranchHeaderBody_noRand
          (allNoRand_cons publishBranchBody_noRand allNoRand_nil)))))))))))))
  · simp [branchEdgeRecordsBody, branchEdgeRecordsLoop, forRange, forUp, Stmt.NoRand]
  · simp [writeBranchEdgeRecordBody, Stmt.NoRand]
  · simp [namedStretchBody, Stmt.NoRand]
  · simp [stretchSourceBody, stretchSourceLoop, forRange, forUp, Stmt.NoRand]
  · simp [writeStretchSourceBody, Stmt.NoRand]
  · simp [scatterBranchStretchBody, scatterBranchStretchLoop, forRange, forUp, Stmt.NoRand]
  · simp [publishRootedBranchBody, Stmt.NoRand]
  · simp [writeRootBitBody, Stmt.NoRand]
  · simp [serializeBranchBody, Stmt.NoRand]
  · simp [writeStretchDescriptorBody, Stmt.NoRand]
  · simp [finishBranchBody, Stmt.NoRand]

/-- The packed tree selector module uses no `rand` statement, for every guest program. -/
theorem packedTreeSelectorModule_noRand (guest : Program) (D b : ℕ) :
    ∀ s ∈ packedTreeSelectorModule guest D b, s.NoRand := by
  change AllNoRand _
  unfold packedTreeSelectorModule
  refine allNoRand_append ?_ (allNoRand_append ?_ (relocatedTreeProcedures_noRand guest _))
  · refine allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_
      (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_ (allNoRand_cons ?_
        (allNoRand_cons ?_ allNoRand_nil))))))))
    · simp [selectAndQueryConvertedTreeBody, stagedConvertedTreeReturn,
        stagedConvertAndTreeBody, Stmt.NoRand]
    · simp [selectPaddedGuestWidthBody, Stmt.NoRand]
    · simp [guestWorkspaceBody, Stmt.NoRand]
    · simp [paddedGuestWidthBody, Stmt.NoRand]
    · simp [packGuestStridedBody, packGuestStridedLoop, forRange, forUp, Stmt.NoRand]
    · simp [conversionBlockBody, conversionBlockLoop, forRange, forUp, Stmt.NoRand]
    · simp [storeConversionBitBody, Stmt.NoRand]
    · simp [conversionBitBody, Stmt.NoRand]
    · simp [formatBitBody, Stmt.NoRand]
  · exact allNoRand_cons (Scaling.Machine.clogTwoBody_noRand _) allNoRand_nil

/-- The packed round module uses no `rand` statement. -/
theorem packedRoundModule_noRand (b select initGraph : ℕ) :
    ∀ s ∈ packedRoundModule b select initGraph, s.NoRand := by
  change AllNoRand _
  unfold packedRoundModule
  refine allNoRand_append (allNoRand_cons (stagedPackedRoundBody_noRand ..) allNoRand_nil)
    (allNoRand_append (packedRoundArithmeticModule_noRand _)
      (allNoRand_append (packedRoundBufferModule_noRand _ _)
        (allNoRand_append (packedBranchModule_noRand _ _)
          (allNoRand_cons ?_ allNoRand_nil))))
  simp [dedupSelectedTreeBody, dedupTreeEdges, dedupTreeEdgeStep, forRange, forUp, Stmt.NoRand]

/-- The packed selected-round module uses no `rand` statement, for every guest program. -/
theorem packedSelectedRoundModule_noRand (guest : Program) (D b initGraph : ℕ) :
    ∀ s ∈ packedSelectedRoundModule guest D b initGraph, s.NoRand := by
  change AllNoRand _
  unfold packedSelectedRoundModule
  exact allNoRand_append (packedRoundModule_noRand _ _ _)
    (packedTreeSelectorModule_noRand guest D _)

/-- The shared initializer helper procedures use no `rand` statement. -/
theorem packedRepresentativeInitializerProcedures_noRand
    (guest : Program) (b d graphOps initGraph : ℕ) :
    ∀ s ∈ packedRepresentativeInitializerProcedures guest b d graphOps initGraph, s.NoRand := by
  change AllNoRand _
  unfold packedRepresentativeInitializerProcedures
  exact allNoRand_append (packedInputTableModule_noRand _)
    (allNoRand_append (DynSpanner.Program.sortProcs_noRand _)
      (allNoRand_append (DynSpanner.Program.gtProcs_noRand _ _)
        (allNoRand_append (packedInitializerFormatModule_noRand _ _ _ _ _ _)
          (allNoRand_append (packedFormatScansModule_noRand _ _)
            (allNoRand_append (packedInitialWeightsModule_noRand _ _)
              (packedSelectedRoundModule_noRand guest d _ initGraph))))))

private theorem packedRepresentativeInitializerBody_noRand
    (guest : Program) (b d c graphOps initGraph : ℕ) :
    (packedRepresentativeInitializerBody guest b d c graphOps initGraph).NoRand := by
  simp only [packedRepresentativeInitializerBody, representativeRuntimeInitWith,
    prepareRuntimeEndpoints, prepareRuntimeRepresentative, representativeRuntimeInput,
    representativeRebuildInput, representativePrepareEdges, representativeKeyScan,
    representativeKeyScanStep, representativeSortAndScan, representativeKeySort,
    representativeGroupScan, representativeGroupInit, representativeGroupStep,
    representativeClassStep, representativeReadCandidate, representativeBeginClass,
    representativeFlush, representativeAppend, representativeChoose, representativeLengthLess,
    representativePrepareIndices, representativePrepareVertexSlots, representativePrepareVertices,
    representativeVertexLoop, representativeVertexStep, representativeWriteVertexPair,
    representativeSortVertices, representativeVertexSlots, representativeVertexSlotStep,
    representativePrepareEdgeIndex, representativeSortEdgeNames, representativePublishEdgeIndex,
    collectionIndexAndEndpoints, prepareOriginalEdgeNames, prepareStretchIndices,
    writeStretchIndices, writeStretchIndexStep,
    collectionFormatBody, collectionWeightScale, collectionGuestFormat, collectionSimulationWidth,
    installControllerLevels, forRange, forUp, Stmt.NoRand, and_self]

private theorem stagedCompactCollectionThen_noRand (init weights round copy : ℕ) :
    (stagedCompactCollectionThen init weights round copy).NoRand := by
  simp only [stagedCompactCollectionThen, finishCompactCollectionSetup, finishCollectionSetupWith,
    installCompactCollectionWeightFormat, installCollectionCount, rebuildCollectionThen,
    lastLevelRoundsBody_noRand, publishRuntimeCollection, stagedAddressAssignments_noRand,
    Stmt.NoRand, and_self]

/-- The packed representative initializer module uses no `rand` statement. -/
theorem packedRepresentativeInitializerModule_noRand
    (guest : Program) (b d c graphOps initGraph : ℕ) :
    ∀ s ∈ packedRepresentativeInitializerModule guest b d c graphOps initGraph, s.NoRand := by
  change AllNoRand _
  unfold packedRepresentativeInitializerModule
  exact allNoRand_append
    (allNoRand_cons (packedRepresentativeInitializerBody_noRand guest b d c graphOps initGraph)
      allNoRand_nil)
    (allNoRand_append (packedRepresentativeInitializerProcedures_noRand guest b d graphOps initGraph)
      (allNoRand_cons (stagedCompactCollectionThen_noRand ..) allNoRand_nil))

private theorem loopOnlyInit_noRand (init copy header : ℕ) :
    (loopOnlyInit init copy header).NoRand := by
  simp only [loopOnlyInit, loopOnlySetup, loopOnlyLoadInput, loopOnlyReserve, loopOnlyBuild,
    loopOnlyBranchGraph, loopOnlyStretchBody, loopOnlyStretchLoop, loopOnlyStretchStep,
    loopOnlyCopyStretch, loopOnlyStretchDescriptor, loopOnlyPublish, loopOnlyBranchHeader,
    loopOnlyCollectionHeader, forRange, forUp, Stmt.NoRand, and_self]

/-- **Determinism of the packed last-level program** (Definition 5.8, pages 19–20).
Every procedure in `packedLastLevelProgram guest d c` contains no `rand` statement, for every
guest program `guest`. -/
theorem packedLastLevelProgram_isDeterministic (guest : Program) (d c : ℕ) :
    (packedLastLevelProgram guest d c).IsDeterministic := by
  change AllNoRand (packedLastLevelProgram guest d c).procs
  unfold packedLastLevelProgram
  refine allNoRand_append DynSpanner.Program.dgProcs_noRand ?_
  refine allNoRand_append ?_ (packedRepresentativeInitializerModule_noRand guest 19 d c 0 14)
  exact allNoRand_cons (dispatchRuntimeInit_noRand 17 19)
    (allNoRand_cons readoutBody_noRand
      (allNoRand_cons (loopOnlyInit_noRand 14 74 18)
        (allNoRand_cons writeBranchHeaderBody_noRand allNoRand_nil)))

end MinCostFlow.LastLevelProgram
