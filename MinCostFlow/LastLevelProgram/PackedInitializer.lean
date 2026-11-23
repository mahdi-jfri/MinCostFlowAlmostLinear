module

public import MinCostFlow.LastLevelProgram.CollectionFormat
public import MinCostFlow.LastLevelProgram.PackedRuntimeSpace
public import MinCostFlow.LastLevelProgram.PackedNumericPhases
public import MinCostFlow.LastLevelProgram.StagedRebuildProof
public import MinCostFlow.LastLevelProgram.GuestFormatSetup
public import MinCostFlow.LastLevelProgram.PackGuestLengths
public import MinCostFlow.LastLevelProgram.LimbValuation
public import MinCostFlow.LastLevelProgram.BlockWidth
public import MinCostFlow.LastLevelProgram.RepresentativeScan
import MinCostFlow.LastLevelProgram.StagedPackedNumeric
import MinCostFlow.Num.ModulePlacement
import Mathlib.Tactic
import MinCostFlow.Num.UnsignedLess

/-!
# Procedures for preparing the packed initializer

Definition 5.8 (pages 19–20) chooses the guest length format before
rebuilding the branch collection. The caller's length and weight formats
are passed in runtime registers.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num DynSpanner.Program
open scoped BigOperators

/-- Install the scale, precision, simulation-width, and length-packing
entries. The scans and bit converter are supplied by the enclosing module. -/
@[expose] def packedInitializerFormatModule
    (b log scanPrecision weightWidth scanWidth convert : ℕ) : List Stmt :=
  [scaleWordBody log,precisionWordBody log,guestSimulationWidthBody log,
    setupAndPackGuestBody (b+4) (b+5),
    guestFormatSetupBody scanPrecision weightWidth scanWidth,packGuestLengthsBody convert]

/-- Each initializer call addresses its installed format procedure. -/
theorem packedInitializerFormatModule_entries
    {p : Program} {b log scanPrecision weightWidth scanWidth convert : ℕ}
    (hp : p.HasAt b (packedInitializerFormatModule b log scanPrecision weightWidth scanWidth convert)) :
    p.procs[b]? = some (scaleWordBody log) ∧
    p.procs[b+1]? = some (precisionWordBody log) ∧
    p.procs[b+2]? = some (guestSimulationWidthBody log) ∧
    p.procs[b+3]? = some (setupAndPackGuestBody (b+4) (b+5)) ∧
    p.procs[b+4]? = some (guestFormatSetupBody scanPrecision weightWidth scanWidth) ∧
    p.procs[b+5]? = some (packGuestLengthsBody convert) :=
  ⟨hp.head,hp.get (i := 1) (show 1 < 6 by decide),hp.get (i := 2) (show 2 < 6 by decide),
    hp.get (i := 3) (show 3 < 6 by decide),hp.get (i := 4) (show 4 < 6 by decide),
    hp.get (i := 5) (show 5 < 6 by decide)⟩

/-- Scan the live length blocks for their common binary shift and
the limb width needed by the guest. -/
@[expose] def packedFormatScansModule (b log : ℕ) : List Stmt :=
  [queryPrecisionBody (b+3),
   weightBoundWidthBody log,
   guestWidthBody (b+8),
   commonLengthShiftBody (b+4),
   lowerLengthShiftBody (b+5),
   blockValuationBody (b+6),
   blockValuationStepBody (b+7),
   limbValuationBody,
   raiseGuestWidthBody (b+9),
   blockWidthBody (b+10),
   blockWidthStepBody (b+11),
   solverLimbSizeBody]

/-- The scan module supplies the precision and width scan contracts. -/
theorem packedFormatScansModule_contracts
    {p : Program} {w b log names lengths L P m grid : ℕ}
    (name : ℕ → ℕ) (E : Finset ℕ)
    (hp : p.HasAt b (packedFormatScansModule b log))
    (hlog : p.HasAt log (Scaling.Machine.clogTwoModule log)) :
    MeetsContract w p b (queryPrecisionContract w names lengths L P m grid name E) ∧
    MeetsContract w p (b+1) (weightBoundWidthContract w) ∧
    ∀ Q initial, MeetsContract w p (b+2) (guestWidthContract w names lengths L P Q initial m name) := by
  have atIndex (i : ℕ) (hi : i < 12) := hp.get (i := i) hi
  refine ⟨queryPrecision_meetsContract name E hp.head ?_,
    weightBoundWidth_meetsContract (atIndex 1 (by decide)) hlog, ?_⟩
  · exact commonLengthShift_meetsContract name (atIndex 3 (by decide))
      (lowerLengthShift_meetsContract (atIndex 4 (by decide))
        (blockValuation_meetsContract (atIndex 5 (by decide))
          (blockValuationStep_meetsContract (atIndex 6 (by decide))
            (limbValuation_meetsContract (atIndex 7 (by decide))))))
  · intro Q initial
    exact guestWidth_meetsContract name (atIndex 2 (by decide))
      (raiseGuestWidth_meetsContract (atIndex 8 (by decide))
        (blockWidth_meetsContract (atIndex 9 (by decide))
          (blockWidthStep_meetsContract (atIndex 10 (by decide))
            (solverLimbSize_meetsContract (atIndex 11 (by decide))))))

/-- The installed format and scan modules compute the model's scale,
guest width, and packed lengths in the caller's runtime format. -/
theorem packedInitializerFormatModule_contracts
    {p guest : Program} {w b scans selector D cap names lengths L P dst target : ℕ}
    (G : MGraph) (C : ℝ)
    (hp : p.HasAt b (packedInitializerFormatModule b (selector+9) scans
      (scans+1) (scans+2) (selector+5)))
    (hs : p.HasAt scans (packedFormatScansModule scans (selector+9)))
    (hselector : p.HasAt selector (packedTreeSelectorModule guest D selector)) :
    MeetsContract w p b (scaleWordContract w G) ∧
    MeetsContract w p (b+1) (precisionWordContract w) ∧
    MeetsContract w p (b+2) (guestSimulationWidthContract w G.n) ∧
    MeetsContract w p (b+3)
      (setupAndPackGuestContract w cap names lengths L P dst target G C (edgeName G)) := by
  obtain ⟨hscale,hprecision,hsim,hformat,hsetup,hpack⟩ := packedInitializerFormatModule_entries hp
  obtain ⟨_,_,_,_,_,hconvert,hlog,_⟩ := packedTreeSelectorModule_entries hselector w
  obtain ⟨hq,hweights,hwidth⟩ := packedFormatScansModule_contracts
    (w := w) (names := names) (lengths := lengths) (L := L) (P := P)
    (m := G.m) (grid := weightPrecision C G) (edgeName G) G.E hs hlog
  exact ⟨scaleWord_meetsContract G hscale hlog,precisionWord_meetsContract hprecision hlog,
    guestSimulationWidth_meetsContract hsim hlog,
    setupAndPackGuest_meetsContract G C (edgeName G) hformat
      (guestFormatSetup_meetsContract G C (edgeName G) hsetup hq hweights hwidth)
      (packGuestLengths_meetsContract G hpack (guestLengthBlock_meetsContract hconvert))⟩

/-- Install the representative key, endpoint packing, and named stretch
index procedures. The graph sorting module is shared by the initializer. -/
@[expose] def packedInputTableModule (b : ℕ) : List Stmt :=
  [representativeKeyBody,packVertexIndexBody,packEdgeBody (b+3),packEndpointsBody,
   stretchIndexKeyTableBody b,stretchIndexScanBody] ++ Num.unsignedLessModule (b+6)

/-- The preparation calls use the installed table procedures. -/
theorem packedInputTableModule_entries {p : Program} {b : ℕ}
    (hp : p.HasAt b (packedInputTableModule b)) :
    p.procs[b]? = some representativeKeyBody ∧
    p.procs[b+1]? = some packVertexIndexBody ∧
    p.procs[b+2]? = some (packEdgeBody (b+3)) ∧
    p.procs[b+3]? = some packEndpointsBody ∧
    p.procs[b+4]? = some (stretchIndexKeyTableBody b) ∧
    p.procs[b+5]? = some stretchIndexScanBody ∧
    p.HasAt (b+6) (Num.unsignedLessModule (b+6)) := by
  have atIndex (i : ℕ) (hi : i < 7) := hp.get (i := i) hi
  refine ⟨atIndex 0 (by decide), atIndex 1 (by decide), atIndex 2 (by decide),
    atIndex 3 (by decide), atIndex 4 (by decide), atIndex 5 (by decide),?_⟩
  intro i hi
  have he : i = 0 := by
    change i < 1 at hi
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hi)
  subst i
  exact atIndex 6 (by decide)

/-- Run endpoint preparation from the caller contract using the
installed representative table module. -/
theorem packedInputTableModule_prepareEndpoints
    {w b sort dedup ops g vCap eCap L P multiplier : ℕ}
    {p : Program} {ω : ℕ → Bool} (fmt : Format w)
    (tool : Chain.LastLevelTool) (allocation : ℕ → List ℕ → ℕ)
    (G : MGraph) (mem : ℕ → ℕ) (lengths heap pos : ℕ)
    (hp : p.HasAt b (packedInputTableModule b))
    (hsort : p.HasAt sort (sortProcs sort))
    (hdedup : p.HasAt dedup (gtProcs sort ops))
    (hw : 16 ≤ 2^w) (hcap : vCap*vCap*eCap ≤ 2^w)
    (hpre : (MinRatio.lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier P
      allocation).initPre [g,lengths,L,fmt.precision,heap] mem) :
    let ℓ := MinRatio.readEdgeValues mem lengths 4 L fmt.precision G.E
    let src := heap+11*G.m+vCap+1
    src+queryLengths (representativeGraph G ℓ) < 2^w →
    ∃ out cost, Runs w p ω (prepareRuntimeEndpoints b sort (b+6) (dedup+gtIdxSortDedup)
        (b+1) (b+2)) (startState [g,lengths,L,fmt.precision,heap] mem pos) .normal out cost ∧
      DynGraphAt out.mem g vCap eCap G ∧
      (∀ i < (representativeGraph G ℓ).m, out.mem (src+i) = (indexedGraph (representativeGraph G ℓ)).tail i ∧
        out.mem (src+((representativeGraph G ℓ).m+i)) = (indexedGraph (representativeGraph G ℓ)).head i) ∧
      (∀ i < (representativeGraph G ℓ).m, out.mem (heap+2*G.m+i) = edgeName (representativeGraph G ℓ) i) ∧
      (∀ i < (representativeGraph G ℓ).n,
        out.mem (heap+7*G.m+i) = vertexName (representativeGraph G ℓ) i) ∧
      out.regs 0 = g ∧ out.regs 112 = g ∧ out.regs 113 = vCap ∧ out.regs 114 = eCap ∧
      out.regs 100 = heap+2*G.m ∧ out.regs 73 = (representativeGraph G ℓ).m ∧ out.regs 72 = (representativeGraph G ℓ).n ∧
      out.regs 99 = lengths ∧ out.regs 127 = L ∧ out.regs 144 = L ∧ out.regs 145 = fmt.precision ∧
      out.regs 146 = heap+11*G.m ∧ out.regs 142 = heap+11*G.m+vCap ∧
      out.regs 141 = src ∧ out.regs 151 = heap ∧ out.regs 150 = heap+7*G.m ∧
      out.regs 115 = G.n ∧ out.regs 116 = dgVListBase g vCap ∧ out.regs 133 = G.m ∧
      out.regs 134 = heap ∧ out.regs 136 = heap+G.m ∧ out.regs 137 = dgEListBase g vCap eCap ∧
      out.regs 138 = heap+3*G.m ∧ out.regs 131 = heap+4*G.m ∧
      (∀ a, a < heap ∨ src+queryLengths (representativeGraph G ℓ) ≤ a → out.mem a = mem a) ∧
      cost ≤ 200*G.m*(Nat.log 2 (G.m+1)+1)+G.m*(41*L+114)+
        250*(2*(representativeGraph G ℓ).m)*(Nat.log 2 (2*(representativeGraph G ℓ).m+1)+1)+114*(representativeGraph G ℓ).m+37*(representativeGraph G ℓ).n+
        200*(representativeGraph G ℓ).m*(Nat.log 2 ((representativeGraph G ℓ).m+1)+1)+argsSize collectionEndpointArgs+565 := by
  obtain ⟨hkey,hvertices,hendpoints,hpack,_,_,hcmp⟩ := packedInputTableModule_entries hp
  exact prepareRuntimeEndpoints_of_initPre fmt tool allocation G mem lengths heap pos hkey hsort
    (Num.unsignedLess_meetsContract (by omega) hcmp) hdedup hvertices hendpoints hpack hw hcap hpre

/-- Prepare the representative graph and all three name tables before
formatting the guest input. The scan leaves the caller and endpoints intact. -/
theorem packedInputTables_runs
    {w b sort dedup ops copy g vCap eCap L P multiplier : ℕ}
    {p : Program} {ω : ℕ → Bool} (fmt : Format w)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ)
    (allocation : ℕ → List ℕ → ℕ)
    (G : MGraph) (mem : ℕ → ℕ) (lengths heap pos : ℕ)
    (hp : p.HasAt b (packedInputTableModule b))
    (hsort : p.HasAt sort (sortProcs sort))
    (hdedup : p.HasAt dedup (gtProcs sort ops))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hw : 16 ≤ 2^w) (hcap : vCap*vCap*eCap ≤ 2^w)
    (hne : (SparseCore.nonLoopEdges G).Nonempty)
    (hpre : (MinRatio.lastLevelRuntimeMachineContract fmt L (fixedPointLastLevelTool oracle C) G vCap eCap multiplier P
      allocation).initPre [g,lengths,L,fmt.precision,heap] mem) :
    let ℓ := MinRatio.readEdgeValues mem lengths 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    let src := heap+11*G.m+vCap+1
    src+queryLengths H < 2^w →
    ∃ prepared named indexed prep cn ci,
      Runs w p ω (prepareRuntimeEndpoints b sort (b+6) (dedup+gtIdxSortDedup) (b+1) (b+2))
        (startState [g,lengths,L,fmt.precision,heap] mem pos) .normal prepared prep ∧
      Runs w p ω (prepareOriginalEdgeNames copy sort) prepared .normal named cn ∧
      Runs w p ω (prepareStretchIndices (b+4) (b+5)) named .normal indexed ci ∧
      (∀ i < G.m, indexed.mem (heap+i) = edgeName G i) ∧
      (∀ i < G.m, indexed.mem (heap+4*G.m+i) = branchStretchIndex G ℓ (edgeName G i)) ∧
      (∀ i < H.m, indexed.mem (heap+2*G.m+i) = edgeName H i) ∧
      (∀ i < H.n, indexed.mem (heap+7*G.m+i) = vertexName H i) ∧
      (∀ i < H.m, indexed.mem (src+i) = (indexedGraph H).tail i ∧
        indexed.mem (src+(H.m+i)) = (indexedGraph H).head i) ∧
      (∀ a, a < heap ∨ src+queryLengths H ≤ a → indexed.mem a = mem a) ∧
      (∀ r, r ≠ 135 → r ≠ 139 → r ≠ 140 → indexed.regs r = prepared.regs r) ∧
      prepared.regs 72 = H.n ∧ prepared.regs 73 = H.m ∧
      prepared.regs 99 = lengths ∧ prepared.regs 100 = heap+2*G.m ∧ prepared.regs 127 = L ∧
      prepared.regs 141 = src ∧ prepared.regs 142 = heap+11*G.m+vCap ∧
      prepared.regs 144 = L ∧ prepared.regs 145 = fmt.precision ∧
      prepared.regs 150 = heap+7*G.m ∧ prepared.regs 151 = heap ∧
      prepared.regs 113 = vCap ∧ prepared.regs 114 = eCap ∧ prepared.regs 115 = G.n ∧
      prepared.regs 116 = dgVListBase g vCap ∧ prepared.regs 131 = heap+4*G.m ∧
      prepared.regs 133 = G.m ∧ prepared.regs 134 = heap ∧
      prep ≤ runtimeEndpointMultiplier L G.m*(G.m+1) ∧
      cn+ci ≤ (200*(Nat.log 2 (G.m+1)+1)+500)*((fixedPointLastLevelTool oracle C).cost G+1) := by
  intro ℓ H src hroom
  let tool := fixedPointLastLevelTool oracle C
  obtain ⟨prepared,prep,hr,hgraph,ht,hn,hv,_,h112,h113,h114,h100,h73,h72,h99,h127,h144,h145,_,h142,h141,h151,h150,h115,h116,
    h133,h134,h136,h137,h138,h131,hframe,hprepCost⟩ :=
    packedInputTableModule_prepareEndpoints (ω := ω) fmt tool allocation G mem lengths heap pos
      hp hsort hdedup hw hcap hpre hroom
  obtain ⟨hkey,_,_,_,hkeys,hscan,_⟩ := packedInputTableModule_entries hp
  obtain ⟨_,hgEnd,_⟩ := runtimeEndpoints_inputs_of_initPre fmt tool allocation G mem hpre
  have hfit : heap+5*G.m < 2^w := by dsimp only [src] at hroom; omega
  obtain ⟨named,indexed,cn,ci,hnRun,hiRun,hnames,hindices,hpres,hregs,htableCost⟩ :=
    runtimeStretchTables_runs (ω := ω) prepared G ℓ heap hcopy hsort hkeys hkey hscan hgraph
      h112 h113 h114 h134 h136 h137 h100 h138 h131 h133 hw hcap hgEnd hfit h73 hn
  have hcard : H.m ≤ G.m := Finset.card_le_card (representativeGraph_subgraph hgraph.1 ℓ).2.1
  refine ⟨prepared,named,indexed,prep,cn,ci,hr,hnRun,hiRun,hnames,hindices,?_,?_,?_,?_,hregs,h72,h73,h99,h100,h127,h141,h142,h144,h145,h150,h151,
    h113,h114,h115,h116,h131,h133,h134,
    hprepCost.trans (runtimeEndpointCost_le G ℓ L hgraph.1),
    htableCost.trans (runtimeStretchTablesCost_le oracle C G ℓ hgraph.1 hne)⟩
  · exact fun i hi => (hpres _ (Or.inr (Or.inl ⟨by omega,by omega⟩))).trans (hn i hi)
  · exact fun i hi => (hpres _ (Or.inr (Or.inr (by omega)))).trans (hv i hi)
  · intro i hi
    have hs : heap+5*G.m ≤ src := by dsimp only [src]; omega
    exact ⟨(hpres _ (Or.inr (Or.inr (by omega)))).trans (ht i hi).1,
      (hpres _ (Or.inr (Or.inr (by omega)))).trans (ht i hi).2⟩
  · intro a ha
    refine (hpres a ?_).trans (hframe a ha)
    rcases ha with ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inr (by dsimp only [src] at ha; omega))

/-- Procedures shared by preparation and the compact collection controller. -/
@[expose] def packedRepresentativeInitializerProcedures (guest : Program)
    (b d graphOps initGraph : ℕ) : List Stmt :=
  packedInputTableModule (b+1) ++
  (sortProcs (b+8) ++
  (gtProcs (b+8) graphOps ++
  (packedInitializerFormatModule (b+17) (b+177) (b+23) (b+24) (b+25) (b+173) ++
  (packedFormatScansModule (b+23) (b+177) ++
  (packedInitialWeightsModule (b+35) (b+38) ++
    packedSelectedRoundModule guest d (b+38) initGraph)))))

/-- The controller follows the guest and its host-side procedures. -/
def packedControllerEntry (guest : Program) (b d graphOps initGraph : ℕ) : ℕ :=
  b+1+(packedRepresentativeInitializerProcedures guest b d graphOps initGraph).length

/-- Prepare the graph and format, then call the controller with only its live inputs. -/
@[expose] def packedRepresentativeInitializerBody (guest : Program) (b d c graphOps initGraph : ℕ) : Stmt :=
  representativeRuntimeInitWith (b+1) (b+8) (b+7) (b+12+gtIdxSortDedup)
    (b+2) (b+3) (b+17) (b+18) (b+20) (b+19) (b+55) (b+177) (b+5) (b+6) d c
    (.seq (.call 160 (packedControllerEntry guest b d graphOps initGraph) packedControllerInputArgs)
      (.ret (.reg 160)))

/-- Install the initializer, its helpers, and the controller at their call addresses. -/
@[expose] def packedRepresentativeInitializerModule (guest : Program)
    (b d c graphOps initGraph : ℕ) : List Stmt :=
  [packedRepresentativeInitializerBody guest b d c graphOps initGraph] ++
    (packedRepresentativeInitializerProcedures guest b d graphOps initGraph ++
      [stagedCompactCollectionThen (b+35) (b+36) (b+38) (b+55)])

/-- The controller starts in its own call frame. -/
theorem packedRepresentativeInitializerModule_controller {p guest : Program}
    {b d c graphOps initGraph : ℕ}
    (hp : p.HasAt b (packedRepresentativeInitializerModule guest b d c graphOps initGraph)) :
    p.procs[packedControllerEntry guest b d graphOps initGraph]? =
      some (stagedCompactCollectionThen (b+35) (b+36) (b+38) (b+55)) :=
  (Num.hasAt_append_right (Num.hasAt_append_right hp)).head

/-- Installation provides the preparation and round procedures at their
call addresses. -/
theorem packedRepresentativeInitializerModule_entries {p guest : Program}
    {b d c graphOps initGraph : ℕ}
    (hp : p.HasAt b (packedRepresentativeInitializerModule guest b d c graphOps initGraph)) :
    p.procs[b]? = some (packedRepresentativeInitializerBody guest b d c graphOps initGraph) ∧
    p.HasAt (b+1) (packedInputTableModule (b+1)) ∧
    p.HasAt (b+8) (sortProcs (b+8)) ∧
    p.HasAt (b+12) (gtProcs (b+8) graphOps) ∧
    p.HasAt (b+17) (packedInitializerFormatModule (b+17) (b+177) (b+23) (b+24) (b+25) (b+173)) ∧
    p.HasAt (b+23) (packedFormatScansModule (b+23) (b+177)) ∧
    p.HasAt (b+35) (packedInitialWeightsModule (b+35) (b+38)) ∧
    p.HasAt (b+38) (packedSelectedRoundModule guest d (b+38) initGraph) := by
  unfold packedRepresentativeInitializerModule at hp
  have htables := Num.hasAt_append_left (Num.hasAt_append_right hp)
  unfold packedRepresentativeInitializerProcedures at htables
  have hsort := Num.hasAt_append_right htables
  have hgt := Num.hasAt_append_right hsort
  have hformat := Num.hasAt_append_right hgt
  have hscans := Num.hasAt_append_right hformat
  have hweights := Num.hasAt_append_right hscans
  exact ⟨hp.head,Num.hasAt_append_left htables,Num.hasAt_append_left hsort,
    Num.hasAt_append_left hgt,Num.hasAt_append_left hformat,Num.hasAt_append_left hscans,
    Num.hasAt_append_left hweights,Num.hasAt_append_right hweights⟩

/-- The last-level data structure uses operation 15 to initialize and
operation 16 to expose a branch. Both initializer routes use the same
graph procedures and four-bit caller format. -/
@[expose] def packedLastLevelProgram (guest : Program) (d c : ℕ) : Program :=
  ⟨dgProcs ++
    ([dispatchRuntimeInit 17 19,readoutBody,loopOnlyInit 14 74 18,writeBranchHeaderBody] ++
      packedRepresentativeInitializerModule guest 19 d c 0 14)⟩

/-- Expose the dispatcher, readout, and installed non-loop module of the
fixed last-level program. -/
theorem packedLastLevelProgram_entries (guest : Program) (d c : ℕ) :
    let p := packedLastLevelProgram guest d c
    p.HasAt 0 dgProcs ∧
      p.procs[15]? = some (dispatchRuntimeInit 17 19) ∧ p.procs[16]? = some readoutBody ∧
      p.procs[17]? = some (loopOnlyInit 14 74 18) ∧
      p.procs[18]? = some writeBranchHeaderBody ∧
      p.HasAt 19 (packedRepresentativeInitializerModule guest 19 d c 0 14) := by
  intro p
  have hall : p.HasAt 0 p.procs := by
    intro i hi
    simpa only [Nat.zero_add] using List.getElem?_eq_getElem hi
  change p.HasAt 0 (dgProcs ++
    ([dispatchRuntimeInit 17 19,readoutBody,loopOnlyInit 14 74 18,writeBranchHeaderBody] ++
      packedRepresentativeInitializerModule guest 19 d c 0 14)) at hall
  have hrest := Num.hasAt_append_right hall
  have h := Num.hasAt_append_left hrest
  exact ⟨Num.hasAt_append_left hall,h.head,h.get (i := 1) (show 1 < 4 by decide),
    h.get (i := 2) (show 2 < 4 by decide),h.get (i := 3) (show 3 < 4 by decide),
    Num.hasAt_append_right hrest⟩

/-- The assembled last-level program implements initialization and
branch readout on the loop-only route. -/
theorem packedLastLevelProgram_implements_loopOnly
    {w vCap eCap L Q : ℕ} (fmt : Format w)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ)
    (G : MGraph) (guest : Program) (d c : ℕ)
    (hw : 16 ≤ 2^w) (hloops : ¬ (SparseCore.nonLoopEdges G).Nonempty) :
    (lastLevelRepresentation vCap eCap fmt.limbBits L fmt.precision G.E).Implements
      w (packedLastLevelProgram guest d c) 15 (fun _ => 16)
      (MinRatio.lastLevelRuntimeMachineContract fmt L (fixedPointLastLevelTool oracle C) G vCap eCap
        (loopOnlyMultiplier L G.n G.m+(29*G.m+81)/2) Q
        (packedRuntimeAllocation G guest C c L vCap eCap)) := by
  obtain ⟨hgraph,hinit,hop,hloop,hheader,hgeneral⟩ :=
    packedLastLevelProgram_entries guest d c
  obtain ⟨_,_,_,_,_,_,_,hselected⟩ := packedRepresentativeInitializerModule_entries hgeneral
  obtain ⟨hround,_⟩ := packedSelectedRoundModule_entries hselected
  obtain ⟨_,harith,_,_,_⟩ := packedRoundModule_entries hround
  have hcopy := (packedRoundArithmeticModule_helpers harith).1
  exact packedRuntime_implements_loopOnly fmt oracle C G guest c
    (dgProcs_hasBatch hgraph) (dgProcs_hasEdge hgraph) (dgProcs_hasOps hgraph)
    (copyWords_meetsContract hcopy) (branchHeader_meetsContract hheader)
    hw hloops hinit hloop hop

/-- Execute the packed initializer's guest format calls from their
installed entries and the prepared length and name tables. -/
theorem packedInitializerFormatModule_runs
    {w b scans selector cap names lengths L P dst src d c₀ : ℕ}
    {p guest : Program} {ω : ℕ → Bool} (st : State) (H : MGraph) (C : ℝ)
    (hn : st.regs 72 = H.n) (hm : st.regs 73 = H.m)
    (hnames : st.regs 100 = names) (hlengths : st.regs 99 = lengths)
    (hL : st.regs 144 = L) (hP : st.regs 145 = P)
    (hdst : st.regs 142 = dst) (hsrc : st.regs 141 = src)
    (hD : d = ⌈max 1 C⌉₊) (hdPos : 1 ≤ d)
    (hp : p.HasAt b (packedInitializerFormatModule b (selector+9) scans
      (scans+1) (scans+2) (selector+5)))
    (hs : p.HasAt scans (packedFormatScansModule scans (selector+9)))
    (hselector : p.HasAt selector (packedTreeSelectorModule guest d selector))
    (hnameTable : ∀ i < H.m, st.mem (names+i) = edgeName H i)
    (hlen : ∀ e ∈ H.E, e < cap ∧ lengths+e*L+L ≤ dst ∧
      Num.Valid st.mem (lengths+e*L) 4 L ∧ 0 < Num.fixVal st.mem (lengths+e*L) 4 L P)
    (hwidth : P ≤ 4*L) (hmPos : 0 < H.m)
    (hspan : names+H.m ≤ dst) (hlenSpan : lengths+cap*L ≤ src+queryLengths H)
    (hdstSpan : dst < src+queryLengths H) (hcPos : 1 ≤ c₀) :
    let len := fun e => if e ∈ H.E then Num.fixVal st.mem (lengths+e*L) 4 L P else 0
    let Q := roundQueryPrecision C H len
    let N := roundQueryLimbs C H len
    let F := setupAndPackGuestContract w cap names lengths L P dst (src+queryLengths H) H C (edgeName H)
    let args := [names,lengths,L,P,H.m,weightPrecision C H,dst,src+queryLengths H]
    packedFormatScalarBound H d c₀ L P (weightPrecision C H) Q N
      (WideWord.lsstLSimMin c₀ H.n H.m N 1) < 2^w →
    src+queryLengths H+H.m*N < 2^w →
    ∃ out ready cost levelCost, Runs w p ω (collectionFormatBody b (b+1) (b+3) (b+2) (.const d) (.const c₀))
        st .normal out cost ∧
      Runs w p ω (installControllerLevels (selector+9)) out .normal ready levelCost ∧
      ready.regs 86 = Nat.clog 2 H.n ∧ ready.mem = out.mem ∧
      (∀ r, r ≠ 86 → ready.regs r = out.regs r) ∧ levelCost ≤ 40*Nat.clog 2 H.n+22 ∧
      F.post args st.mem (out.regs 74) out.mem ∧
      out.regs 83 = Q ∧ out.regs 74 = N ∧ out.regs 75 = WideWord.lsstLSimMin c₀ H.n H.m N 1 ∧
      out.regs 95 = weightPrecision C H ∧ out.regs 107 = integerScale d H ∧
      (∀ r, r ∉ ([74,75,83,95,107] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ argsSize collectionGuestFormatArgs+F.cost args st.mem+
        40*(Nat.log 2 (H.n+2)+1)+40*weightPrecision C H+
        40*(Nat.log 2 (4*H.m+2)+Nat.log 2 (16*H.m+6)+2)+169 := by
  intro len Q N F args hscalar hEnd
  obtain ⟨hw,hdFit,hcFit,hnFit,hmFit,hscaleFit,hwords,hQ,hN,hPN,hSimEnd,_⟩ :=
    packedFormatScalarBound_fields H d c₀ L P (weightPrecision C H) Q N _ w hscalar
  have hscalePos : 0 < integerScale d H := by
    unfold integerScale
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) hmPos)
      (Nat.pow_pos (by omega))
  obtain ⟨hscale,hprecision,hformatSim,hformat⟩ :=
    packedInitializerFormatModule_contracts H C hp hs hselector
  obtain ⟨out,cost,hrun,hpost,h83,h74,h75,h95,h107,hkeep,hcost⟩ :=
    preparedCollectionFormat_runs st H C hn hm hnames hlengths hL hP hdst hsrc
    hD hdPos hdFit hscale hprecision hformat hformatSim hnameTable hlen hw hwidth hmPos
        hnFit hmFit hscalePos hscaleFit hwords hspan hlenSpan hdstSpan hcPos hcFit
    hQ hN hPN hEnd hSimEnd
  obtain ⟨_,_,_,_,_,_,hlog,_⟩ := packedTreeSelectorModule_entries hselector w
  obtain ⟨ready,levelCost,hlevel,h86,hmem,hreg,hlevelCost⟩ :=
    installControllerLevels_runs (w := w) out (Scaling.Machine.clogTwo_meetsContract hlog H.n)
      ((hkeep 72 (by decide)).trans hn) (by omega) (by omega)
  exact ⟨out,ready,cost,levelCost,hrun,hlevel,h86,hmem,hreg,hlevelCost,hpost,
    h83,h74,h75,h95,h107,hkeep,hcost⟩

/-- The formatted guest prefix retains the representative endpoints
and the prepared name tables. The original caller frame also survives. -/
theorem packedInitializer_formatMemory
    {w cap names lengths L P dst src N heap : ℕ} {H : MGraph}
    {original indexed formatted : ℕ → ℕ}
    (C : ℝ) (len : ℕ → ℝ)
    (hpost : (setupAndPackGuestContract w cap names lengths L P dst
      (src+queryLengths H) H C (edgeName H)).post
      [names,lengths,L,P,H.m,weightPrecision C H,dst,src+queryLengths H] indexed N formatted)
    (hlen : (fun e => if e ∈ H.E then fixVal indexed (lengths+e*L) 4 L P else 0) = len)
    (hdst : heap ≤ dst) (hs : dst < src)
    (hzero : ZeroFrom indexed (src+queryLengths H))
    (hends : ∀ i < H.m, indexed (src+i) = (indexedGraph H).tail i ∧
      indexed (src+(H.m+i)) = (indexedGraph H).head i)
    (hframe : ∀ a < heap, indexed a = original a) :
    (∀ i < H.m, formatted (src+i) = (indexedGraph H).tail i ∧
      formatted (src+(H.m+i)) = (indexedGraph H).head i) ∧
    (∀ i < H.m, ListAt formatted (src+queryLengths H+i*N)
      (encodeLimbs 1 N (queryNumerator (roundQueryPrecision C H len) (len (edgeName H i))))) ∧
    ZeroFrom formatted (src+queryWeights H N) ∧
    (∀ a < heap, formatted a = original a) ∧
    (∀ a < dst, formatted a = indexed a) := by
  obtain ⟨ht,hpacked,hfresh,hprefix⟩ :=
    collectionFormat_packedPrefix H C (edgeName H) hpost len hlen hdst hs hzero hends
  obtain ⟨_,_,_,hf⟩ := hpost
  exact ⟨ht,hpacked,hfresh,fun a ha => (hprefix a ha).trans (hframe a ha),
    fun a ha => hf a (by omega) (Or.inl (by omega))⟩

/-- The input-table phase preserves the caller lengths and allocates
the representative names and endpoint arrays before the format scan. -/
theorem packedInitializer_formatInputs
    {w g vCap eCap L stretchPrecision multiplier lengths heap : ℕ}
    (fmt : Format w) (tool : Chain.LastLevelTool) (allocation : ℕ → List ℕ → ℕ)
    (G : MGraph) (original indexed : ℕ → ℕ)
    (hpre : (MinRatio.lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier
      stretchPrecision allocation).initPre [g,lengths,L,fmt.precision,heap] original) :
    let ℓ := MinRatio.readEdgeValues original lengths 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    let dst := heap+11*G.m+vCap
    let src := dst+1
    (∀ a, a < heap ∨ src+queryLengths H ≤ a → indexed a = original a) →
    ZeroFrom original heap →
    (∀ e ∈ H.E, e < eCap ∧ lengths+e*L+L ≤ dst ∧ Valid indexed (lengths+e*L) 4 L ∧
      0 < fixVal indexed (lengths+e*L) 4 L fmt.precision) ∧
    (fun e => if e ∈ H.E then fixVal indexed (lengths+e*L) 4 L fmt.precision else 0) =
      LSF.safeLen H ℓ ∧
    heap+2*G.m+H.m ≤ dst ∧ lengths+eCap*L ≤ src+queryLengths H ∧
    ZeroFrom indexed (src+queryLengths H) := by
  intro ℓ H dst src hframe hzero
  obtain ⟨hgraph,_,hblocks⟩ := runtimeEndpoints_inputs_of_initPre fmt tool allocation G original hpre
  have hEnd := (show heap ≤ dst by dsimp only [dst]; omega)
  have hf (a : ℕ) (ha : a < heap) := hframe a (Or.inl ha)
  have hl := preparedRepresentativeLengths ℓ hgraph.1 hgraph.2.2.1 hEnd hf hblocks
  have hlen := preparedRepresentative_safeLen ℓ hgraph.1 hgraph.2.2.1 hEnd hf hblocks
  have hsub : H.m ≤ G.m := Finset.card_le_card (representativeGraph_subgraph hgraph.1 ℓ).2.1
  have hspan : lengths+eCap*L ≤ heap := by
    obtain ⟨g',len',heap',heq,_,_,hbase,_⟩ := hpre
    simp only [List.cons.injEq,and_true,true_and] at heq
    obtain ⟨rfl,rfl,rfl⟩ := heq
    obtain ⟨g',len',heap',heq,_,_,hspan,_,_⟩ := hbase
    simp only [List.cons.injEq,and_true] at heq
    obtain ⟨rfl,rfl,rfl⟩ := heq
    exact hspan
  exact ⟨fun e he => ⟨(hl e he).1,(hl e he).2.1,(hl e he).2.2.1,(hl e he).2.2.2.2⟩,
    hlen,by dsimp only [dst]; omega,by dsimp only [src,dst]; omega,
    fun a ha => (hframe a (Or.inr ha)).trans (hzero a (by dsimp only [src,dst] at ha; omega))⟩

/-- Run the input tables and guest format setup in order, using the
representative graph and lengths selected from the original caller memory. -/
theorem packedInitializer_prepare_runs
    {w g vCap eCap L P multiplier c₀ : ℕ} {guest : Program} {ω : ℕ → Bool}
    (fmt : Format w)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ)
    (G : MGraph) (mem : ℕ → ℕ) (lengths heap pos : ℕ)
    (hc : 1 ≤ c₀) (hne : (SparseCore.nonLoopEdges G).Nonempty)
    (hconn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v)
    (hzero : ZeroFrom mem heap) :
    let d := ⌈max 1 C⌉₊
    let p := packedLastLevelProgram guest d c₀
    let allocation := packedRuntimeAllocation G guest C c₀ L vCap eCap
    let D := MinRatio.lastLevelRuntimeMachineContract fmt L (fixedPointLastLevelTool oracle C)
      G vCap eCap multiplier P allocation
    let args := [g,lengths,L,fmt.precision,heap]
    let ℓ := MinRatio.readEdgeValues mem lengths 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    let len := LSF.safeLen H ℓ
    let src := heap+11*G.m+vCap+1
    let Q := roundQueryPrecision C H len
    let N := roundQueryLimbs C H len
    let sim := WideWord.lsstLSimMin c₀ H.n H.m N 1
    D.initPre args mem → heap+D.initSpace args mem < 2^w →
    ∃ prepared named indexed formatted ready prep cn ci cf cl,
      Runs w p ω (prepareRuntimeEndpoints 20 27 26 (31+gtIdxSortDedup) 21 22)
        (startState args mem pos) .normal prepared prep ∧
      Runs w p ω (prepareOriginalEdgeNames 74 27) prepared .normal named cn ∧
      Runs w p ω (prepareStretchIndices 24 25) named .normal indexed ci ∧
      Runs w p ω (collectionFormatBody 36 37 39 38 (.const d) (.const c₀))
        indexed .normal formatted cf ∧
      Runs w p ω (installControllerLevels 196) formatted .normal ready cl ∧
      ready.regs 86 = Nat.clog 2 H.n ∧ ready.mem = formatted.mem ∧
      ready.regs 83 = Q ∧ ready.regs 74 = N ∧ ready.regs 75 = sim ∧
      ready.regs 95 = weightPrecision C H ∧ ready.regs 107 = integerScale d H ∧
      (∀ r, r ≠ 86 → r ∉ ([74,75,83,95,107,135,139,140] : List ℕ) →
        ready.regs r = prepared.regs r) ∧
      (∀ i < H.m, ready.mem (src+i) = (indexedGraph H).tail i ∧
        ready.mem (src+(H.m+i)) = (indexedGraph H).head i) ∧
      (∀ i < H.m, ListAt ready.mem (src+queryLengths H+i*N)
        (encodeLimbs 1 N (queryNumerator Q (len (edgeName H i))))) ∧
      ZeroFrom ready.mem (src+queryWeights H N) ∧
      (∀ a < heap, ready.mem a = mem a) ∧
      (∀ a < heap+11*G.m+vCap, ready.mem a = indexed.mem a) ∧
      ready.regs 72 = H.n ∧ ready.regs 73 = H.m ∧
      ready.regs 127 = L ∧ ready.regs 141 = src ∧ ready.regs 151 = heap ∧
      ready.regs 113 = vCap ∧ ready.regs 114 = eCap ∧ ready.regs 115 = G.n ∧
      ready.regs 116 = dgVListBase g vCap ∧ ready.regs 131 = heap+4*G.m ∧
      ready.regs 133 = G.m ∧ ready.regs 134 = heap ∧
      ready.regs 150 = heap+7*G.m ∧ ready.regs 99 = lengths ∧ ready.regs 100 = heap+2*G.m ∧
      ready.regs 145 = fmt.precision ∧
      (∀ i < G.m, ready.mem (heap+i) = edgeName G i) ∧
      (∀ i < G.m, ready.mem (heap+4*G.m+i) = branchStretchIndex G ℓ (edgeName G i)) ∧
      (∀ i < H.m, ready.mem (heap+2*G.m+i) = edgeName H i) ∧
      (∀ i < H.n, ready.mem (heap+7*G.m+i) = vertexName H i) ∧
      prep ≤ runtimeEndpointMultiplier L G.m*(G.m+1) ∧
      cn+ci ≤ (200*(Nat.log 2 (G.m+1)+1)+500)*((fixedPointLastLevelTool oracle C).cost G+1) ∧
      cl ≤ 40*Nat.clog 2 H.n+22 ∧
      cf ≤ argsSize collectionGuestFormatArgs+
        (((98*L+92)+(80*N+37))*H.m+40*(2*H.m).size+145)+
        40*(Nat.log 2 (H.n+2)+1)+40*weightPrecision C H+
        40*(Nat.log 2 (4*H.m+2)+Nat.log 2 (16*H.m+6)+2)+169 := by
  intro d p allocation D args ℓ H len src Q N sim hpre hroom
  obtain ⟨_,_,_,_,_,hgeneral⟩ := packedLastLevelProgram_entries guest d c₀
  obtain ⟨_,hp,hsort,hdedup,hf,hs,_,hselected⟩ :=
    packedRepresentativeInitializerModule_entries hgeneral
  obtain ⟨hround,ht⟩ := packedSelectedRoundModule_entries hselected
  obtain ⟨_,harith,_,_,_⟩ := packedRoundModule_entries hround
  have hcopy := copyWords_meetsContract (w := w) (packedRoundArithmeticModule_helpers harith).1
  obtain ⟨hm,_,_,haddress,_,_,_,_⟩ :=
    packedRuntimeAllocation_controllerBounds fmt oracle G guest C c₀ mem hne hconn hpre hroom
  change src+queryWeights H N < 2^w at haddress
  obtain ⟨_,hcap,hscalar⟩ :=
    packedRuntimeAllocation_nonLoop_words fmt (fixedPointLastLevelTool oracle C)
      G guest C c₀ mem hne hpre hroom
  have hwidth := hpre.choose_spec.choose_spec.choose_spec.2.2.1
  have hd : 1 ≤ d := by
    exact_mod_cast (le_max_left (1 : ℝ) C).trans (Nat.le_ceil (max 1 C))
  have hw := (packedFormatScalarBound_fields H d c₀ L fmt.precision (weightPrecision C H)
    Q N sim w hscalar).1
  have hsrc : src+queryLengths H < 2^w :=
    (Nat.le_add_right _ (H.m*N)).trans_lt (by simpa only [queryWeights, Nat.add_assoc] using haddress)
  obtain ⟨prepared,named,indexed,prep,cn,ci,hr,hnr,hir,hOriginal,hIndices,hnames,hVertices,hends,hframe,hregs,
    hn,hmr,hl,hname,h127,hsr,hdr,hL,hP,h150,h151,h113,h114,h115,h116,h131,h133,h134,
    hPrepCost,hIndexCost⟩ :=
    packedInputTables_runs (ω := ω) fmt oracle C allocation G mem lengths heap pos
      hp hsort hdedup hcopy (Nat.le_of_lt hw) hcap hne hpre hsrc
  obtain ⟨hblocks,hlen,hspan,hlspan,hfresh⟩ :=
    packedInitializer_formatInputs fmt (fixedPointLastLevelTool oracle C) allocation G mem
      indexed.mem hpre hframe hzero
  have hkeep (r : ℕ) (hr₁ : r ≠ 135) (hr₂ : r ≠ 139) (hr₃ : r ≠ 140) :=
    hregs r hr₁ hr₂ hr₃
  have hdst : heap+11*G.m+vCap < src+queryLengths H := by
    dsimp only [src]
    omega
  have hsetup := packedInitializerFormatModule_runs (w := w) (ω := ω) (p := p) (guest := guest)
    (c₀ := c₀) (b := 36) (scans := 42) (selector := 187) (cap := eCap)
    (names := heap+2*G.m) (lengths := lengths) (L := L) (P := fmt.precision)
    (dst := heap+11*G.m+vCap) (src := src) indexed H C
    ((hkeep 72 (by decide) (by decide) (by decide)).trans hn)
    ((hkeep 73 (by decide) (by decide) (by decide)).trans hmr)
    ((hkeep 100 (by decide) (by decide) (by decide)).trans hname)
    ((hkeep 99 (by decide) (by decide) (by decide)).trans hl)
    ((hkeep 144 (by decide) (by decide) (by decide)).trans hL)
    ((hkeep 145 (by decide) (by decide) (by decide)).trans hP)
    ((hkeep 142 (by decide) (by decide) (by decide)).trans hdr)
    ((hkeep 141 (by decide) (by decide) (by decide)).trans hsr)
    rfl hd hf hs ht hnames hblocks hwidth hm hspan hlspan hdst hc
  dsimp only at hsetup
  rw [hlen] at hsetup
  obtain ⟨formatted,ready,cf,cl,hfr,hlr,hdepth,hmem,hready,hLevelCost,hpost,hQ,hN,hsim,hgrid,hscale,hfregs,hFormatCost⟩ :=
    hsetup hscalar (by simpa only [queryWeights, Nat.add_assoc] using haddress)
  obtain ⟨hendpoints,hpacked,hzeroPacked,hcaller,hprefix⟩ :=
    packedInitializer_formatMemory C len (hN ▸ hpost) hlen
      (show heap ≤ heap+11*G.m+vCap by omega)
      (show heap+11*G.m+vCap < src by dsimp only [src]; omega)
      hfresh hends (fun a ha => hframe a (Or.inl ha))
  have hretained (r : ℕ) (hr86 : r ≠ 86)
      (hr : r ∉ ([74,75,83,95,107,135,139,140] : List ℕ)) :
      ready.regs r = prepared.regs r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h74,h75,h83,h95,h107,h135,h139,h140⟩ := hr
    exact (hready r hr86).trans ((hfregs r (by simp [h74,h75,h83,h95,h107])).trans
      (hkeep r h135 h139 h140))
  have hcard : H.m ≤ G.m := by
    obtain ⟨hgraph,_,_⟩ :=
      runtimeEndpoints_inputs_of_initPre fmt (fixedPointLastLevelTool oracle C) allocation G mem hpre
    exact Finset.card_le_card (representativeGraph_subgraph hgraph.1 ℓ).2.1
  have hvertices : H.n ≤ 2*H.m := representativeGraph_n_le_twice_m G ℓ
  have htableFrame (a : ℕ) (ha : a < heap+11*G.m+vCap) : ready.mem a = indexed.mem a :=
    (congrFun hmem a).trans (hprefix a ha)
  have hFormatCost' : cf ≤ argsSize collectionGuestFormatArgs+
      (((98*L+92)+(80*N+37))*H.m+40*(2*H.m).size+145)+
      40*(Nat.log 2 (H.n+2)+1)+40*weightPrecision C H+
      40*(Nat.log 2 (4*H.m+2)+Nat.log 2 (16*H.m+6)+2)+169 := by
    unfold setupAndPackGuestContract at hFormatCost
    dsimp only at hFormatCost
    rw [hlen] at hFormatCost
    exact hFormatCost
  refine ⟨prepared,named,indexed,formatted,ready,prep,cn,ci,cf,cl,hr,hnr,hir,hfr,hlr,
    hdepth,hmem,(hready 83 (by decide)).trans hQ,(hready 74 (by decide)).trans hN,
    (hready 75 (by decide)).trans hsim,(hready 95 (by decide)).trans hgrid,
    (hready 107 (by decide)).trans hscale,hretained,?_,?_,?_,?_,htableFrame,
    (hretained 72 (by decide) (by decide)).trans hn,
    (hretained 73 (by decide) (by decide)).trans hmr,
    (hretained 127 (by decide) (by decide)).trans h127,
    (hretained 141 (by decide) (by decide)).trans hsr,
    (hretained 151 (by decide) (by decide)).trans h151,
    (hretained 113 (by decide) (by decide)).trans h113,
    (hretained 114 (by decide) (by decide)).trans h114,
    (hretained 115 (by decide) (by decide)).trans h115,
    (hretained 116 (by decide) (by decide)).trans h116,
    (hretained 131 (by decide) (by decide)).trans h131,
    (hretained 133 (by decide) (by decide)).trans h133,
    (hretained 134 (by decide) (by decide)).trans h134,
    (hretained 150 (by decide) (by decide)).trans h150,
    (hretained 99 (by decide) (by decide)).trans hl,
    (hretained 100 (by decide) (by decide)).trans hname,
    (hretained 145 (by decide) (by decide)).trans hP,
    fun i hi => (htableFrame _ (by omega)).trans (hOriginal i hi),
    fun i hi => (htableFrame _ (by omega)).trans (hIndices i hi),
    fun i hi => (htableFrame _ (by omega)).trans (hnames i hi),
    fun i hi => (htableFrame _ (by omega)).trans (hVertices i hi),
    hPrepCost,hIndexCost,hLevelCost,hFormatCost'⟩
  · simpa only [hmem] using hendpoints
  · simpa only [hmem] using hpacked
  · simpa only [hmem] using hzeroPacked
  · simpa only [hmem] using hcaller

/-- The fixed last-level program publishes a branch with its installed
graph, fixed-point, and output layout procedures. -/
theorem packedLastLevelProgram_append_runs
    {w vCap eCap L caller : ℕ}
    {ω : ℕ → Bool} (guest : Program) (d c : ℕ) (st : State)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ)
    (G : MGraph) (ℓ : ℕ → ℝ) (count collection j rounds vertices indices start names : ℕ)
    (g guestL staging cursor repNames scale : ℕ) (original staged : ℕ → ℕ)
    (hnl : (SparseCore.nonLoopEdges G).Nonempty) (hG : G.IsValid)
    (hconn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v)
    (hw : 16 ≤ 2^w)
    (h13 : st.regs 13 = count) (h41 : st.regs 41 = vCap) (h42 : st.regs 42 = eCap)
    (h59 : st.regs 59 = indices) (h55 : st.regs 55 = L)
    (h56 : st.regs 56 = collection) (h57 : st.regs 57 = j)
    (h40 : st.regs 40 = vertices) (h61 : st.regs 61 = G.m) (h62 : st.regs 62 = names)
    (h19 : st.regs 19 = L) (hLPos : 0 < L)
    (hbits : 14 ≤ w)
    (hgraph : DynGraphAt original g vCap eCap G)
    (hgraphEnd : g+dynGraphSize vCap eCap ≤ staging)
    (hstageFrame : ∀ a < staging, staged a = original a)
    (h28 : st.regs 28 = repNames) (h5 : st.regs 5 = staging) (h12 : st.regs 12 = cursor)
    (h43 : st.regs 43 = G.n) (h44 : st.regs 44 = dgVListBase g vCap)
    (T : MGraph) :
    let p := packedLastLevelProgram guest d c
    let H := representativeGraph G ℓ
    let P := weightPrecision C H
    let query := stretchQuery oracle H ℓ P
    let branch := ((fixedPointLastLevelTool oracle C).build G ℓ).2 j
    let afterStretch := start+H.m*L
    let numericEnd := afterStretch+H.m*L
    let records := numericEnd+2*L
    let ptr := records+3*count
    let tree := ptr+4
    let roots := tree+dynGraphSize vCap eCap
    let addresses := roots+vCap+2
    let stop := addresses+eCap+eCap*L+eCap*L
    st.regs 1 = H.m → stop < 2^w →
    st.regs 36 = start → st.regs 37 = L → st.regs 38 = afterStretch →
    collection+1+rounds ≤ staging → j < rounds →
    st.regs 16 = numericEnd → ZeroFrom st.mem numericEnd →
    indices+G.m ≤ staging → names+G.m ≤ staging → vertices+H.n ≤ staging →
    (∀ i < H.n, original (vertices+i) = vertexName H i) →
    (∀ i < G.m, original (indices+i) = branchStretchIndex G ℓ (edgeName G i)) →
    (∀ i < G.m, original (names+i) = edgeName G i) →
    st.regs 23 = P → P < 2^w → 2*(2 : ℝ)^P < Num.capacity 4 L →
    (scale : ℝ) = roundedScale C H →
    oracle H (LSF.safeLen H ℓ) (weights P (roundedScale C H) query j) = restoreTreeNames H T →
    retainedStagedTreeAt H T (staging+queryWeights H guestL) (cursor+1+H.m) count staged st.mem →
    (∀ i ∈ T.E, i < H.m) →
    repNames+H.m ≤ staging+queryWeights H guestL → vertices+H.n ≤ staging+queryWeights H guestL →
    (∀ i < H.m, staged (repNames+i) = edgeName H i ∧
      staged (staging+i) = (indexedGraph H).tail i ∧
      staged (staging+(H.m+i)) = (indexedGraph H).head i) →
    (∀ v < H.n, staged (vertices+v) = vertexName H v) →
    staging+queryWeights H guestL ≤ cursor+1+H.m → cursor+1+H.m+H.n ≤ numericEnd →
    (∀ i < H.m, Valid st.mem (start+i*L) 4 L ∧
      fixVal st.mem (start+i*L) 4 L P =
        query (weights P ((scale : ℤ) : ℝ) query j) (edgeName H i)) →
    ∃ out cost,
      Runs w p ω (stagedBranchAppendBody 164 172 14 174 179)
        st .normal out cost ∧ out.regs 54 = stop ∧
      out.regs 38 = afterStretch ∧
      ZeroFrom out.mem stop ∧ out.mem (collection+1+j) = ptr ∧
      BranchWithin out.mem ptr (collection+1+rounds) stop vCap eCap L G.E ∧
      MinRatio.LSFAt out.mem ptr vCap eCap 4 L caller G.E branch ∧
      (∀ a < numericEnd, a ≠ collection+1+j → out.mem a = st.mem a) ∧
      cost ≤ stagedAppendModelCost G L count := by
  intro p
  obtain ⟨hgraphModule,_,_,_,_,hgeneral⟩ := packedLastLevelProgram_entries guest d c
  obtain ⟨_,_,_,_,_,_,_,hselected⟩ := packedRepresentativeInitializerModule_entries hgeneral
  obtain ⟨hround,_⟩ := packedSelectedRoundModule_entries hselected
  obtain ⟨_,harith,hbuffer,hbranch,_⟩ := packedRoundModule_entries hround
  obtain ⟨_,_,hunit,_,_,_,_,hstore,hshift⟩ := packedRoundBufferModule_entries hbuffer
  have hcopy := (packedRoundArithmeticModule_helpers harith).1
  have hlimb : Num.base 4 < 2^w := by
    change 16 < 2^w
    exact (show 16 < 2^14 by decide).trans_le (Nat.pow_le_pow_right (by decide) hbits)
  exact stagedPackedAppendModel_runs (ω := ω) st oracle C G ℓ count collection j rounds
    vertices indices start names g guestL staging cursor repNames scale original staged
    hnl hG hconn hw h13 h41 h42 h59 h55 h56 h57 h40 h61 h62 h19 hLPos (by decide)
    (by omega) hlimb hunit hstore hshift (dgProcs_hasBatch hgraphModule)
    (dgProcs_hasEdge hgraphModule) (dgProcs_hasOps hgraphModule)
    hgraph hgraphEnd hstageFrame h28 h5 h12 h43 h44 T hcopy hbranch

/-- Execute selection and deduplication at the fixed program's round
entries. The canonical selector contract sees the actual staged buffer. -/
theorem packedLastLevelProgram_treeSelection_runs
    {w guestCost levels vCap eCap L P caller base count handle bound j src guestL sim Q stride : ℕ}
    {ω : ℕ → Bool} {H T : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem : ℕ → ℕ} (st staged : State) (pos : ℕ) (len : ℕ → ℝ) (C : ℝ)
    (hready : GraphQueryReady C H len (weights P ρ query j))
    (hguestL : guestL = roundQueryLimbs C H len)
    (hguestQ : Q = roundQueryPrecision C H len)
    (hs : stagedRoundStateAtStride H vCap eCap 4 L P caller base count handle bound stride E branches ρ query mem j st)
    (hstrideGe : L ≤ stride)
    (hkeep : ∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
      staged.regs r = (startState ((List.range 70).map (st.regs ∘ roundControllerRegister))
        st.mem pos).regs r)
    (hcursor : staged.regs 5 = st.regs 0)
    (hweight : staged.regs 8 = st.mem (st.regs 0-1))
    (hn : st.regs 72 = H.n) (hm : st.regs 73 = H.m)
    (hguest : st.regs 74 = guestL) (hsim : st.regs 75 = sim)
    (hstride : st.regs 81 = stride) (hP : st.regs 82 = P) (hQ : st.regs 83 = Q)
    (hhost : st.regs 91 = L) (hbound : bound < 2^w) (hwords : ∀ r, st.regs r < 2^w)
    (hcopy : ∀ i < queryWeights H guestL, staged.mem (st.regs 0+i) = st.mem (src+i))
    (hframe : ∀ a, a < st.regs 0 ∨ st.regs 0+queryWeights H guestL ≤ a → staged.mem a = st.mem a)
    (hbase : src+queryWeights H guestL = base)
    (ht : ∀ i < H.m, mem (src+i) = (indexedGraph H).tail i)
    (hh : ∀ i < H.m, mem (src+(H.m+i)) = (indexedGraph H).head i)
    (hlen : ∀ i < H.m, ListAt mem (src+queryLengths H+i*guestL)
      (encodeLimbs 1 guestL (queryNumerator Q (len (edgeName H i)))))
    (hw : 16 ≤ 2^w) (hL : 4*L < 2^w) (hprec : P+guestL < 2^w)
    (guest : Program) (D c : ℕ)
    (hstagedWords : ∀ r, staged.regs r < 2^w)
    (hq : st.regs 0+queryOriginals H guestL+1+
      2^paddedGuestWidth guest D H.n H.m sim (queryHeap H guestL) ≤ 2^w →
      (packedLastLevelProgram guest D c).HasAt 187 (packedTreeSelectorModule guest D 187) →
      MeetsContract w (packedLastLevelProgram guest D c) 187
      (convertedTreeSelectorContract w guest D H T guestL sim (st.regs 0) guestCost
        (st.mem (st.regs 0-1)) stride L P Q (queryNumerator Q ∘ len)
        (queryNumerator Q ∘ weights P ρ query j)))
    (hv : (indexedGraph H).Valid)
    (hc : ∀ a ∈ (indexedGraph H).toMGraph.V, ∀ b ∈ (indexedGraph H).toMGraph.V,
      (indexedGraph H).toMGraph.Connected a b)
    (γ : ℝ) (htree : LSF.IsLSST (indexedGraph H).toMGraph
      (len ∘ edgeName H) (weights P ρ query j ∘ edgeName H) γ T) :
    let cursor := st.regs 0
    let width := paddedGuestWidth guest D H.n H.m sim (queryHeap H guestL)
    let guestEnd := cursor+queryOriginals H guestL+1+2^width
    j < count →
    cursor+(count-j)*stagedPackedRoundSpace H guest D guestL sim levels L P H.n vCap eCap ≤ bound →
    ∃ selected cost, Runs w (packedLastLevelProgram guest D c) ω (stagedTreeSelectionBody 187 186 convertedGuestCallArgs)
      staged .normal selected cost ∧
      selectedTreeAt H T (cursor+queryWeights H guestL) (guestEnd+H.m)
        (selected.regs 13) staged.mem selected.mem ∧
      selected.regs 12 = cursor+queryOriginals H guestL+2^width ∧
      selected.regs 13 ≤ H.n ∧ (∀ r, selected.regs r < 2^w) ∧
      (∀ r, r ≠ 12 → r ≠ 13 → selected.regs r = staged.regs r) ∧
      selected.regs 0 = H.n ∧ selected.regs 1 = H.m ∧ selected.regs 5 = cursor ∧
      (∀ i < H.m, staged.mem (cursor+i) = (indexedGraph H).tail i) ∧
      (∀ i < H.m, staged.mem (cursor+(H.m+i)) = (indexedGraph H).head i) ∧
      cost ≤ argsSize convertedGuestCallArgs +
        convertedTreeSelectorCost w guest D H guestL sim guestCost +
        argsSize (stagedDedupArgs (.reg 0) (.reg 1) (.reg 2) (.reg 3) (.reg 5) (.reg 12)) +
        40*H.n+17 := by
  obtain ⟨_,_,_,_,_,hgeneral⟩ := packedLastLevelProgram_entries guest D c
  obtain ⟨_,_,_,_,_,_,_,hround⟩ := packedRepresentativeInitializerModule_entries hgeneral
  obtain ⟨hroundBody,hselector⟩ := packedSelectedRoundModule_entries hround
  obtain ⟨_,_,_,_,hdedup⟩ := packedRoundModule_entries hroundBody
  exact packedController_treeSelection_runs st staged pos len C hready hguestL hguestQ hs
    hstrideGe hkeep hcursor hweight hn hm hguest hsim hstride hP hQ hhost hbound hwords
    hcopy hframe hbase ht hh hlen hw hL hprec guest D hstagedWords (fun h => hq h hselector)
    hdedup hv hc γ htree

/-- The runtime caller supplies a ready canonical query in every live
round. The representative graph is connected, and the guest and host
formats fit the selector's arithmetic. -/
theorem packedInitializer_liveSelectorInputs
    {w L vCap eCap multiplier stretchPrecision g lengths handle j : ℕ}
    (fmt : Format w) (guest : Program) (c : ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ)
    (G : MGraph) (mem : ℕ → ℕ)
    (hOracle : LSF.HasLSSTSpec oracle C)
    (hne : (SparseCore.nonLoopEdges G).Nonempty)
    (hconn : ∀ a ∈ G.V, ∀ b ∈ G.V, G.Connected a b) :
    let allocation := packedRuntimeAllocation G guest C c L vCap eCap
    let D := MinRatio.lastLevelRuntimeMachineContract fmt L (fixedPointLastLevelTool oracle C)
      G vCap eCap multiplier stretchPrecision allocation
    let args := [g,lengths,L,fmt.precision,handle]
    let ℓ := MinRatio.readEdgeValues mem lengths 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    let len := LSF.safeLen H ℓ
    let P := weightPrecision C H
    let query := stretchQuery oracle H ℓ P
    let N := roundQueryLimbs C H len
    P ≤ stretchPrecision → D.initPre args mem →
    handle+D.initSpace args mem < 2^w → j < H.m →
    GraphQueryReady C H len (weights P (roundedScale C H) query j) ∧
      (indexedGraph H).Valid ∧ 0 < H.n ∧ 0 < H.m ∧
      (∀ a ∈ (indexedGraph H).toMGraph.V, ∀ b ∈ (indexedGraph H).toMGraph.V,
        (indexedGraph H).toMGraph.Connected a b) ∧
      14 ≤ w ∧ 16 < 2^w ∧ 4*L < 2^w ∧ P+N < 2^w := by
  intro allocation D args ℓ H len P query N hP hpre hspace hj
  obtain ⟨hgraph,_,_⟩ :=
    runtimeEndpoints_inputs_of_initPre fmt (fixedPointLastLevelTool oracle C) allocation G mem hpre
  obtain ⟨hv,hm,hconnected⟩ := stagedController_compactGraph G ℓ hgraph.1 hne hconn
  have hpreLive := packedRuntimePre_of_finer fmt allocation (fixedPointLastLevelTool oracle C)
    G mem hP hpre
  have hready := (canonicalRound_modelInputs_of_runtimePre (j := j) fmt allocation
    oracle C G mem hOracle hne hpreLive hj).1
  obtain ⟨hbits,_,hscalar⟩ := packedRuntimeAllocation_nonLoop_words fmt
    (fixedPointLastLevelTool oracle C) G guest C c mem hne hpre hspace
  obtain ⟨hw,_,_,_,_,_,hhost,_,_,_,_,hprec⟩ :=
    packedFormatScalarBound_fields H ⌈max 1 C⌉₊ c L fmt.precision P _ N _ w hscalar
  refine ⟨hready,hv,hv.1,hm,hconnected,hbits,hw,?_,hprec⟩
  omega

/-- The cited low-stretch tree program supplies the same tree as the
fixed-point model at the installed selector entry in every ready round. -/
theorem packedLastLevelProgram_withCanonicalSelector :
    ∃ (guest : Program) (c₀ : ℕ) (K Cf : ℝ)
      (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph),
      1 ≤ c₀ ∧
      let C := graphCanonicalConstant K Cf
      let D := graphCanonicalIntegerConstant K Cf
      LSF.HasLSSTSpec oracle C ∧
      (fixedPointLastLevelTool oracle C).IsSpec (SparseCore.lastLevelParams (128 * max 1 C)) ∧
      ∀ G len wt, 0 < G.n → 0 < G.m → GraphQueryReady C G len wt →
        let L := roundQueryLimbs C G len
        let Q := roundQueryPrecision C G len
        let sim := WideWord.lsstLSimMin c₀ G.n G.m L 1
        ∃ (tree : MGraph) (guestCost : ℕ),
          oracle G len wt = restoreTreeNames G tree ∧
          LSF.IsLSST (indexedGraph G).toMGraph (len ∘ edgeName G) (wt ∘ edgeName G)
            ((4*max K 1+5)*Real.log (↑G.n+2)^2) tree ∧
          (guestCost : ℝ) ≤ 16000 * ((G.m+G.n+1 : ℕ) : ℝ) *
            WideWord.lsstOverheadFactor guest c₀ K G.n G.m L ∧
          ∀ (w staging src stride hostL P : ℕ),
            staging+queryOriginals G L+1+
              2^paddedGuestWidth guest D G.n G.m sim (queryHeap G L) ≤ 2^w →
            MeetsContract w (packedLastLevelProgram guest D c₀) 187
              (convertedTreeSelectorContract w guest D G tree L sim staging guestCost src stride
                hostL P Q (queryNumerator Q ∘ len) (queryNumerator Q ∘ wt)) := by
  obtain ⟨guest,c,K,Cf,oracle,hc,hOracle,hSpec,hquery⟩ :=
    graphCanonicalModel_withSelector
  refine ⟨guest,c,K,Cf,oracle,hc,hOracle,hSpec,?_⟩
  intro G len wt hn hm hready N Q sim
  obtain ⟨tree,cost,hmodel,htree,hcost,hcall⟩ := hquery G len wt hn hm hready
  refine ⟨tree,cost,hmodel,htree,hcost,?_⟩
  intro w staging src stride hostL P hspace
  let D := graphCanonicalIntegerConstant K Cf
  obtain ⟨_,_,_,_,_,hgeneral⟩ := packedLastLevelProgram_entries guest D c
  obtain ⟨_,_,_,_,_,_,_,hround⟩ := packedRepresentativeInitializerModule_entries hgeneral
  have hselector := (packedSelectedRoundModule_entries hround).2
  exact hcall _ w 187 staging src stride hostL P hselector hspace

/-- Link the live controller round at its fixed procedure index. The
phase proof starts after staging the copied guest prefix. -/
theorem packedLastLevelProgram_round_meetsContract
    {w D c
      vCap eCap h L P caller base count handle bound guestL sim src j budget stride : ℕ}
    {guest : Program} {H : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ}
    {query : (ℕ → ℝ) → ℕ → ℝ} {mem : ℕ → ℕ} (st : State) (Next : State → Prop)
    (hs : stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound stride E branches ρ query mem j st)
    (hn : st.regs 72 = H.n) (hm : st.regs 73 = H.m)
    (hguest : st.regs 74 = guestL) (hsim : st.regs 75 = sim) (hsrc : st.regs 141 = src)
    (hbase : src+queryWeights H guestL = base) (hw : 1 < 2^w)
    (hheap : queryHeap H guestL < 2^w) (hfit : bound+queryWeights H guestL < 2^w)
    (hbound : bound < 2^w) (hwords : ∀ r, st.regs r < 2^w) :
    let p := packedLastLevelProgram guest D c
    let C := stagedControllerRoundContract st Next j budget
    let args := (List.range 70).map (st.regs ∘ roundControllerRegister)
    (∀ pos ω staged, staged.regs 5 = st.regs 0 →
        staged.regs 8 = st.mem (st.regs 0-1) → staged.regs 31 = st.mem (st.regs 0-1) →
        (∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
          staged.regs r = (startState args st.mem pos).regs r) →
        (∀ i < queryWeights H guestL, staged.mem (st.regs 0+i) = st.mem (src+i)) →
        (∀ a, a < st.regs 0 ∨ st.regs 0+queryWeights H guestL ≤ a →
          staged.mem a = st.mem a) →
        (∀ r, staged.regs r < 2^w) →
      ∃ mid ready out cn cl cb stop weights,
        Runs w p ω
          (.seq (stagedTreeSelectionBody 187 186 convertedGuestCallArgs)
            (prepareAndRunWideStagedNumericBody 74 162 163
              164 165 58))
          staged .normal mid cn ∧
        Runs w p ω (publishableWideOutputs 168) mid .normal ready cl ∧
        Runs w p ω (stagedBranchAppendBody 164 172 14 174 179)
          ready .normal out cb ∧
        out.regs 54 = stop ∧ out.regs 38 = weights ∧ stop+1 < 2^w ∧
        ZeroFrom out.mem stop ∧
        C.post args st.mem (stop+1) (Function.update out.mem stop weights) ∧
        cn+cl+cb+21+17*queryWeights H guestL+14+
          argsSize [.reg 69,.reg 5,
            (canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 5 (.const 0)]
          ≤ C.cost args st.mem) →
    MeetsContract w p 57 C := by
  intro p C args hphases
  obtain ⟨_,_,_,_,_,hgeneral⟩ := packedLastLevelProgram_entries guest D c
  have hround := (packedRepresentativeInitializerModule_entries hgeneral).2.2.2.2.2.2.2
  exact stagedPackedControllerRound_linkStaged st Next hs hn hm hguest hsim hsrc hbase
    hw hheap hfit hround hbound hwords hphases

/-- Run the fixed program's collection controller, starting with
unit weights and invoking the live round contract at each iteration. -/
theorem packedLastLevelProgram_controller_runs
    {w D c vCap eCap L P caller guestL sim src handle bound budget step : ℕ}
    {guest : Program} {ω : ℕ → Bool} (st : State) (G : MGraph) (ℓ : ℕ → ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C ρ : ℝ)
    (query : (ℕ → ℝ) → ℕ → ℝ)
    (hbits : 10 ≤ w)
    (hnl : (SparseCore.nonLoopEdges G).Nonempty) (hw : 1 < 2^w)
    (hL : st.regs 127 = L) (hP : st.regs 95 = P) (h151 : st.regs 151 = handle)
    (hguestL : st.regs 74 = guestL) (hsim : st.regs 75 = sim) (hsrc : st.regs 141 = src)
    (hfit : bound < 2^w)
    (hwidth : 2*(2 : ℝ)^P < capacity 4 L) :
    let p := packedLastLevelProgram guest D c
    let H := representativeGraph G ℓ
    let base := src+queryWeights H guestL
    let s := (fixedPointLastLevelTool oracle C).build G ℓ
    let Inv := stagedRoundStateAtStride H vCap eCap 4 L P caller base s.1 handle bound L G.E s.2 ρ query st.mem
    let loopCost := (argsSize publishedRoundArgs+budget+10)*s.1+7
    st.regs 72 = H.n → st.regs 73 = H.m → 0 < H.m → queryHeap H guestL < 2^w →
    handle+1+s.1 ≤ base → ZeroFrom st.mem base →
    base+1+s.1+2*L+H.m*L+1+s.1*step ≤ bound →
    (∀ r, st.regs r < 2^w) →
    (∀ prepared : State, prepared.regs 81 = L → prepared.regs 82 = P →
      prepared.regs 91 = L → prepared.regs 104 = L →
      (∀ r, r ∉ ([1,3,81,82,91,104] : List ℕ) → prepared.regs r = st.regs r) →
      ∀ j < s.1, ∀ current : State, Inv j current →
        current.regs 0+(s.1-j)*step ≤ bound →
        (∀ r, current.regs r < 2^w) →
        (∀ r, 4 ≤ r → current.regs r = prepared.regs r) →
        current.regs 2 = j →
        MeetsContract w p 57
          (stagedControllerRoundContract current
            (fun next => Inv (j+1) next ∧ next.regs 0+(s.1-(j+1))*step ≤ bound)
            j budget)) →
    ∃ o out cost, Runs w p ω (stagedCompactCollectionThen 54 55 57 74) st o out cost ∧
      (∃ limit, o = .returned limit ∧ handle+1+s.1 ≤ limit ∧ limit ≤ bound ∧
        CollectionPrefix out.mem handle s.1 s.1 limit vCap eCap 4 L caller G.E s.2 ∧
        ZeroFrom out.mem limit ∧ (∀ a < handle, out.mem a = st.mem a)) ∧
      cost ≤ collectionHeaderAddress.size+20+
        (argsSize initialWeightControllerArgs+((17*L+27)*H.m+56*L+111)+loopCost+
          (17*(s.1+1)+19)+17) := by
  intro p
  obtain ⟨_,_,_,_,_,hgeneral⟩ := packedLastLevelProgram_entries guest D c
  obtain ⟨_,_,_,_,_,_,hweights,hround⟩ := packedRepresentativeInitializerModule_entries hgeneral
  exact packedCompactController_of_rounds st G ℓ oracle C ρ query hweights hround
    hbits hnl hw hL hP h151 hguestL hsim hsrc hfit hwidth

end MinCostFlow.LastLevelProgram
