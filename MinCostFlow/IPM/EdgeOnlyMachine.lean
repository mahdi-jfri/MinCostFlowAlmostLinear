module

public import MinCostFlow.IPM.EdgeOnly
public import MinCostFlow.IPM.Machine.MinRatioContract
public import MinCostFlow.IPM.Machine.RefreshLayout
public import MinCostFlow.IPM.Machine.ConnectedRefresh
public import MinCostFlow.IPM.Machine.DetectBatchOutput
public import MinCostFlow.IPM.Machine.DetectRefreshCheckedInput
public import MinCostFlow.IPM.Machine.HistoryAppend
public import MinCostFlow.IPM.Machine.HistoryIteration
public import MinCostFlow.IPM.Machine.EpochConditionsDetectInput
public import MinCostFlow.IPM.Machine.SolverSearchLink
public import MinCostFlow.IPM.Machine.SolverSearchLinkWithV
import Lean.Elab.Tactic.Omega

/-!
# Edge-only updates for the machine IPM's histories and refresh batches

Every batch and dynamic history constructed by the machine IPM under `MinCostFlow/IPM/Machine/`
uses only edge insertions and deletions:

1. **Refresh batches**: `RefreshBatch G U` (required by `minRatioMachineContractAt`,
   `minRatioMachineContract`, `minRatioMachineContractWithV`, `refreshEdges_isRefreshBatch`,
   `connectedInitial_refreshes`, `detectBatch_output`, and `checkedUpdate_pre_after_detectRefresh`)
   contains only edge deletions and insertions (`Bundle.IsEdgeUpdate`).
2. **Appended histories**: constant initial histories, `appendHistoryStage`,
   `appendHistoryIteration`, `EpochConditions`, and `EpochPoint.detectInput` all preserve
   `Chain.Ordered.HistoryEdgeOnly`.
3. **Linked search bridge**: `solverSearchModule_runs_widened_edgeOnly` and
   `solverSearchModuleWithV_runs_widened_edgeOnly` specialize
   `solverSearchModule_runs_widened_upTo_on` and `solverSearchModuleWithV_runs_widened_upTo_on`
   to `MinRatioSpecWithFailureEdgeOnlyConnectedUpTo`, using the fixed-graph invariant
   `MinRatioGraphFixed (namedInstance I)` without modifying any lower machine-IPM module.
-/

public section
namespace MinCostFlow.IPM.Machine

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain.Ordered

/-! ### Refresh batches and machine Update preconditions -/

/-- Every primitive update in a machine `RefreshBatch` is an edge deletion or insertion. -/
theorem RefreshBatch.isEdgeUpdate {G : MGraph} {U : List MinCostFlow.Update}
    (hU : RefreshBatch G U) : ∀ u ∈ U, IsEdgeUpdate u := by
  intro u hu
  have h := hU.2.2 u hu
  cases u with
  | insert _ _ _ => trivial
  | delete _ => trivial
  | split _ _ _ _ => exact False.elim h

/-- Any batch satisfying the Update precondition of `minRatioMachineContractAt` (including both
`minRatioMachineContract` and `minRatioMachineContractWithV`) consists solely of edge updates. -/
theorem minRatioMachineContractAt_update_isEdgeUpdate {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (initPre : List ℕ → (ℕ → ℕ) → Prop)
    {s : A.State} {args : List ℕ} {mem : ℕ → ℕ}
    (hpre : (minRatioMachineContractAt F A G m κ α rate allocation initPre).pre 0 s args mem) :
    ∃ U : List MinCostFlow.Update,
      BatchAt mem (args.getD 1 0) U ∧ RefreshBatch G U ∧ ∀ u ∈ U, IsEdgeUpdate u := by
  obtain ⟨_, handle, batch, g, l, eta, heap, U, rfl, _, _, _, hBatch, _, hRefresh, _⟩ := hpre
  exact ⟨U, hBatch, hRefresh, hRefresh.isEdgeUpdate⟩

/-- Every batch passed to `minRatioMachineContract`'s Update operation is edge-only. -/
theorem minRatioMachineContract_update_isEdgeUpdate {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    {s : A.State} {args : List ℕ} {mem : ℕ → ℕ}
    (hpre : (minRatioMachineContract F A G m κ α rate allocation).pre 0 s args mem) :
    ∃ U : List MinCostFlow.Update,
      BatchAt mem (args.getD 1 0) U ∧ RefreshBatch G U ∧ ∀ u ∈ U, IsEdgeUpdate u :=
  minRatioMachineContractAt_update_isEdgeUpdate F A G m κ α rate allocation
    (minRatioInitPre F G m κ α) hpre

/-- Every batch passed to `minRatioMachineContractWithV`'s Update operation is edge-only. -/
theorem minRatioMachineContractWithV_update_isEdgeUpdate {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m V : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    {s : A.State} {args : List ℕ} {mem : ℕ → ℕ}
    (hpre : (minRatioMachineContractWithV F A G m V κ α rate allocation).pre 0 s args mem) :
    ∃ U : List MinCostFlow.Update,
      BatchAt mem (args.getD 1 0) U ∧ RefreshBatch G U ∧ ∀ u ∈ U, IsEdgeUpdate u :=
  minRatioMachineContractAt_update_isEdgeUpdate F A G m κ α rate allocation
    (minRatioInitPreWithV F G m V κ α) hpre

/-- Every refresh batch applied to the connected augmented graph (`ConnectedRefresh.lean`)
consists solely of edge updates, and the graph stays connected with its original vertex set. -/
theorem connectedInitial_refreshes_isEdgeUpdate (I : Instance) (K : ℤ) (hI : I.IsValid)
    (batches : List (List ℕ))
    (he : ∀ es ∈ batches, ∀ e ∈ es, e ∈ (namedInstance (connectedInitialInstance I K)).E) :
    let G := namedInstance (connectedInitialInstance I K)
    let H := batches.foldl (fun H es => H.applyBatch (refreshEdges G es)) G
    (∀ es ∈ batches, ∀ u ∈ refreshEdges G es, IsEdgeUpdate u) ∧
    MinRatioGraphFixed G H ∧
    MinRatioGraphConnectedFixedV G.V H := by
  dsimp only
  have href := connectedInitial_refreshes I K hI batches he
  refine ⟨fun es _ => refreshEdges_isEdgeUpdate _ es, href.1, ?_, href.2⟩
  exact congrArg MGraph.V href.1

/-- The Update batch produced by `detectBatchContract` (`DetectBatchOutput.lean`) consists solely
of edge insertions and deletions. -/
theorem detectBatch_output_isEdgeUpdate {w source report heap v : ℕ} {I : Instance}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hpre : (detectBatchContract w I S).pre [source, report, heap] mem)
    (hout : (detectBatchContract w I S).post [source, report, heap] mem v mem')
    (hvWord : v < 2 ^ w) :
    ∃ es : List ℕ, es.Nodup ∧ es.toFinset = S ∧
      BatchAt mem' heap (refreshEdges (namedInstance I) es) ∧
      ∀ u ∈ refreshEdges (namedInstance I) es, IsEdgeUpdate u := by
  obtain ⟨es, hnd, hset, _, hbatch, _, _, _, _, _⟩ := detectBatch_output hpre hout hvWord
  exact ⟨es, hnd, hset, hbatch, refreshEdges_isEdgeUpdate (namedInstance I) es⟩

/-- After `detectRefresh` accepts (`DetectRefreshCheckedInput.lean`), any batch built from the
resulting checked-update precondition consists solely of edge insertions and deletions. -/
theorem checkedUpdate_pre_after_detectRefresh_batch_isEdgeUpdate {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v source eta neg maximum minimum : ℕ}
    {s : A.State} {x final : R.τ} {mem mem' : ℕ → ℕ} {request : ℝ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b, names, I.m, base, lo, up, f, F.limbs, heap, c, r, a, one, mn, mx, F.fmt.precision, E, ld, gd, I.m] mem)
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).post
      [b, names, I.m, base, lo, up, f, F.limbs, heap, c, r, a, one, mn, mx, F.fmt.precision, E, ld, gd, I.m] mem v mem')
    (haccept : mem' (v - 1) = 1)
    (hrep : R.rep b (A.detect s).2 final mem') (hfoot : ∀ z, R.foot b final z → z < v)
    (hbWord : b < 2 ^ w) (hmWord : I.m < 2 ^ w)
    (hI : I.IsValid) (hgraph : ListAt mem source (zeroLowerWords I))
    (hgraphEnd : source + (zeroLowerWords I).length ≤ f) (hgraphWords : ∀ z ∈ zeroLowerWords I, z < 2 ^ w)
    (heEnd : eta + F.limbs ≤ f) (hnEnd : neg + F.limbs ≤ f)
    (hxEnd : maximum + F.limbs ≤ f) (hmEnd : minimum + F.limbs ≤ f)
    (hrequest : ScalarAt mem eta F.fmt.limbBits F.limbs F.fmt.precision request)
    (heLo : (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ request) (heHi : request ≤ (2 : ℝ) ^ F.rangeExponent)
    (hn : ScalarAt mem neg F.fmt.limbBits F.limbs F.fmt.precision (-(2 : ℝ) ^ F.rangeExponent))
    (hx : ScalarAt mem maximum F.fmt.limbBits F.limbs F.fmt.precision ((2 : ℝ) ^ F.rangeExponent))
    (hm : ScalarAt mem minimum F.fmt.limbBits F.limbs F.fmt.precision ((2 : ℝ) ^ (-(F.rangeExponent : ℤ))))
    (hk : (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ κ * α)
    (hprec : 5 * F.rangeExponent + Nat.size I.m + 30 ≤ F.fmt.precision)
    (hq : ∀ e ∈ (namedInstance I).E, |A.query (A.detect s).2 e| ≤ (2 : ℝ) ^ F.rangeExponent)
    (hvalid : ∀ e < I.m, Num.Valid mem (gd + e * F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (ld + e * F.limbs) F.fmt.limbBits F.limbs)
    (hrange : ∀ e ∈ (namedInstance I).E,
      |readVector mem gd F.fmt.limbBits F.limbs F.fmt.precision I.m e| ≤ (2 : ℝ) ^ F.rangeExponent ∧
      (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m e ≤ (2 : ℝ) ^ F.rangeExponent)
    (hreached : MinRatioReachedWith A (namedInstance I) s
      (readVector mem gd F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m))
    (hspace : (v + 2) + (1 + 6 * (A.detect s).1.card) + updateAllocationBound w b gd ld eta allocation + (1 + 2 * F.limbs) + 2 < 2 ^ w) :
    ∀ {batchEnd : ℕ} {batchMem : ℕ → ℕ},
      (detectBatchContract w I (A.detect s).1).post [source, mem' (v - 2), v] mem' batchEnd batchMem →
      batchEnd < 2 ^ w →
      ∃ es : List ℕ, es.Nodup ∧ es.toFinset = (A.detect s).1 ∧
        BatchAt batchMem v (refreshEdges (namedInstance I) es) ∧
        ∀ u ∈ refreshEdges (namedInstance I) es, IsEdgeUpdate u := by
  have hchk := checkedUpdate_pre_after_detectRefresh F A I κ α rate allocation R hpre hout haccept
    hrep hfoot hbWord hmWord hI hgraph hgraphEnd hgraphWords heEnd hnEnd hxEnd hmEnd
    hrequest heLo heHi hn hx hm hk hprec hq hvalid hrange hreached hspace
  obtain ⟨source', report', g', l', eta', heap', neg', mx', mn', heq, hBatchPre, _⟩ := hchk.1
  simp only [List.cons.injEq, and_true, true_and] at heq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq
  intro batchEnd batchMem hBatchPost hEndW
  exact detectBatch_output_isEdgeUpdate hBatchPre hBatchPost hEndW

/-! ### Machine history constructors preserve `HistoryEdgeOnly` -/

/-- A constant-graph history with empty batches (as used in `EpochInitialFlow.lean` and
`EpochConditionsInitial.lean`) has only edge updates at every horizon `T`. -/
theorem constantHistory_historyEdgeOnly (G : MGraph) (g l : ℕ → ℝ) (T : ℕ) :
    HistoryEdgeOnly ⟨fun _ => G, fun _ => [], fun _ => g, fun _ => l⟩ T := by
  intro t _ _ u hu
  exact False.elim (List.not_mem_nil hu)

/-- Prefix agreement on update batches transfers `HistoryEdgeOnly`. -/
theorem historyEdgeOnly_prefix_congr {D E : DynamicInstance} {T : ℕ}
    (h : ∀ j ≤ T, D.U j = E.U j) (hD : HistoryEdgeOnly D T) :
    HistoryEdgeOnly E T := by
  intro t ht1 htT u hu
  exact hD t ht1 htT u ((h t htT).symm ▸ hu)

/-- Extending a history by one edge-only stage preserves `HistoryEdgeOnly`. -/
theorem historyEdgeOnly_succ {D : DynamicInstance} {T : ℕ}
    (hD : HistoryEdgeOnly D T) (hU : ∀ u ∈ D.U (T + 1), IsEdgeUpdate u) :
    HistoryEdgeOnly D (T + 1) := by
  intro t ht1 htT u hu
  by_cases hle : t ≤ T
  · exact hD t ht1 hle u hu
  · have heq : t = T + 1 := by omega
    subst heq
    exact hU u hu

/-- Appending an edge-only batch via `appendHistoryStage` (`HistoryAppend.lean`) preserves
`HistoryEdgeOnly`. -/
theorem appendHistoryStage_historyEdgeOnly {D : DynamicInstance} {T : ℕ}
    (U : List MinCostFlow.Update) (g l : ℕ → ℝ)
    (hD : HistoryEdgeOnly D T) (hU : ∀ u ∈ U, IsEdgeUpdate u) :
    HistoryEdgeOnly (appendHistoryStage D T U g l) (T + 1) := by
  apply historyEdgeOnly_succ
  · apply historyEdgeOnly_prefix_congr (D := D) _ hD
    intro j hj
    have hne : j ≠ T + 1 := by omega
    simp only [appendHistoryStage, Function.update_of_ne hne]
  · simpa only [appendHistoryStage, Function.update_self] using hU

/-- Appending a Detect stage (`U = []`) via `appendHistoryStage` preserves `HistoryEdgeOnly`. -/
theorem appendHistoryStage_detect_historyEdgeOnly {D : DynamicInstance} {T : ℕ}
    (g l : ℕ → ℝ) (hD : HistoryEdgeOnly D T) :
    HistoryEdgeOnly (appendHistoryStage D T [] g l) (T + 1) :=
  appendHistoryStage_historyEdgeOnly [] g l hD (fun _ hu => False.elim (List.not_mem_nil hu))

/-- Appending a refresh Update stage (`refreshEdges G es`) via `appendHistoryStage` preserves
`HistoryEdgeOnly`. -/
theorem appendHistoryStage_refresh_historyEdgeOnly {D : DynamicInstance} {T : ℕ}
    (G : MGraph) (es : List ℕ) (g l : ℕ → ℝ) (hD : HistoryEdgeOnly D T) :
    HistoryEdgeOnly (appendHistoryStage D T (refreshEdges G es) g l) (T + 1) :=
  appendHistoryStage_historyEdgeOnly (refreshEdges G es) g l hD (refreshEdges_isEdgeUpdate G es)

/-- Appending a complete Detect-then-refresh-Update iteration via `appendHistoryIteration`
(`HistoryIteration.lean`) preserves `HistoryEdgeOnly`. -/
theorem appendHistoryIteration_historyEdgeOnly {D : DynamicInstance} {T : ℕ}
    (es : List ℕ) (g l : ℕ → ℝ) (hD : HistoryEdgeOnly D T) :
    HistoryEdgeOnly (appendHistoryIteration D T es g l) (T + 1 + 1) :=
  appendHistoryStage_refresh_historyEdgeOnly (D.G T) es g l
    (appendHistoryStage_detect_historyEdgeOnly (D.g T) (D.ℓ T) hD)

/-- Every history in an `EpochConditions` state (`EpochConditions.lean`) automatically has only
edge updates, because it is a valid min-ratio history on the fixed graph `namedInstance I`. -/
theorem EpochConditions.historyEdgeOnly {w : ℕ} {F : MinRatioFormat w}
    {A : MinRatioDataStructureWithFailure} {I : Instance} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ} {R : DSRep A.State}
    {L : EpochLayout} {q K : ℕ} {initialMem : ℕ → ℕ}
    {initialHeap space finish i : ℕ} {P : EpochPoint R.τ}
    (h : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap space finish i P) :
    HistoryEdgeOnly P.history (2 * i) :=
  historyEdgeOnly_of_minRatioHistoryValid_fixedGraph
    h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1

/-- The Detect extension `P.detectInput i` (`EpochConditionsDetectInput.lean`) of any
`EpochConditions` state has only edge updates. -/
theorem EpochConditions.detectInput_historyEdgeOnly {w : ℕ} {F : MinRatioFormat w}
    {A : MinRatioDataStructureWithFailure} {I : Instance} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ} {R : DSRep A.State}
    {L : EpochLayout} {q K : ℕ} {initialMem : ℕ → ℕ}
    {initialHeap space finish i : ℕ} {P : EpochPoint R.τ}
    (h : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap space finish i P) :
    HistoryEdgeOnly (P.detectInput i).history (2 * i + 1) :=
  appendHistoryStage_detect_historyEdgeOnly _ _ h.historyEdgeOnly

/-- Extending an `EpochConditions` history by one Detect/refresh iteration has only edge updates. -/
theorem EpochConditions.nextIteration_historyEdgeOnly {w : ℕ} {F : MinRatioFormat w}
    {A : MinRatioDataStructureWithFailure} {I : Instance} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ} {R : DSRep A.State}
    {L : EpochLayout} {q K : ℕ} {initialMem : ℕ → ℕ}
    {initialHeap space finish i : ℕ} {P : EpochPoint R.τ}
    (h : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap space finish i P)
    (es : List ℕ) (g l : ℕ → ℝ) :
    HistoryEdgeOnly (appendHistoryIteration P.history (2 * i) es g l) (2 * (i + 1)) := by
  have heq : 2 * (i + 1) = 2 * i + 1 + 1 := by omega
  rw [heq]
  exact appendHistoryIteration_historyEdgeOnly es g l h.historyEdgeOnly

/-! ### Linked search runs under `MinRatioSpecWithFailureEdgeOnlyConnectedUpTo` -/

/-- The linked solver's bisection (`SolverSearchLink.lean`) runs directly from an edge-only
connected min-ratio specification, using the fixed-graph invariant `MinRatioGraphFixed` so no
lower machine-IPM lemma needs modification. -/
theorem solverSearchModule_runs_widened_edgeOnly {w b init : ℕ} {p : Program} {op : ℕ → ℕ}
    (I : Instance) (U k : ℕ) (hw : ipmQualityParameterWordBits I.m U k ≤ w)
    (A : MinRatioDataStructureWithFailure) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep A.State) (hp : p.HasAt b (solverSearchModule b init op))
    (hA : MinRatioSpecWithFailureEdgeOnlyConnectedUpTo A (1 / (2 : ℝ) ^ k)
      (Num.IPM.alphaPrime I.m U / 8)
      ((ipmQualityRangeExponent I.m U k + slackRangeExponent I.m U + 6 : ℕ) : ℝ)
      ((1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m U / 1024) I.m I.n)
    (hConn : MinRatioGraphConnected (namedInstance I))
    (himpl : R.Implements w p init op (minRatioMachineContract (ipmQualityMinRatioFormat I.m U k hw)
      A (namedInstance I) I.m (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m U / 8) rate allocation))
    (old : EpochLayout) (qp source heap B : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hE : old.exponent = ipmQualityRangeExponent I.m U k)
    (hfixed : TargetFixedInputs (ipmQualityMinRatioFormat I.m U k hw) I old qp qp heap (1 / 4)
      ((25 / 32 : ℝ) * ((1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m U / 32) ^ 2 / 50)
      (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow (ipmQualityMinRatioFormat I.m U k hw) I old.exponent source heap mem)
    (hhalf : ∀ e, (1 / 2 : ℝ) ≤ epochVector (ipmQualityMinRatioFormat I.m U k hw) I mem source e - (I.edge e).lower ∧
      (1 / 2 : ℝ) ≤ (I.edge e).upper - epochVector (ipmQualityMinRatioFormat I.m U k hw) I mem source e)
    (hwords : ∀ z ∈ targetOffsetPacket old (ipmQualityMinRatioFormat I.m U k hw) I 0 qp source heap (targetTestLimit I.m U k) (I.m * U ^ 2), z < 2 ^ w)
    (hRadius : 2 * (I.m * U ^ 2) < 2 ^ w)
    (hRound : targetSearchRounds (I.m * U ^ 2) < 2 ^ w)
    (halloc : ∀ j < 4, ∀ args, allocation j args ≤ B)
    (hLimit : targetTestLimit I.m U k < 2 ^ w)
    (hspace : heap + targetSearchSpace (ipmQualityMinRatioFormat I.m U k hw) I.m U k old.exponent B < 2 ^ w)
    (hz : ZeroFrom mem heap) (hm : 0 < I.m) (hU : 0 < U) (hsize : 2 ≤ I.m * U)
    (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m, 0 ≤ (I.edge e).lower) :
    let F := ipmQualityMinRatioFormat I.m U k hw
    let limit := targetTestLimit I.m U k
    let radius := I.m * U ^ 2
    ∃ v final cost, ∃ z : ℤ, ∃ fstar,
      Runs w p ω (targetSearchBody (b + 1))
        (startState (targetOffsetPacket old F I 0 qp source heap limit radius ++ [targetSearchRounds radius]) mem pos)
        (.returned v) final cost ∧
      I.IsMinCostFlow fstar ∧ I.cost fstar = (z : ℝ) ∧
      TargetOffsetResult F I old.exponent heap v z z mem final.mem ∧ final.mem (v - 1) = 1 ∧
      v ≤ heap + targetSearchSpace F I.m U k old.exponent B ∧
      cost ≤ targetSearchCost F I.m U k old.exponent rate :=
  solverSearchModule_runs_widened_upTo_on I U k hw A rate allocation R hp
    (hA.toUpToOn_fixedGraph (namedInstance I) hConn)
    (MinRatioStageFixed.admits (namedInstance I) (by push_cast; linarith)) himpl old qp source heap B mem pos ω
    hE hfixed hflow hhalf hwords hRadius hRound halloc hLimit hspace hz hm hU hsize hI hnums hLower

/-- `V`-passing variant of `solverSearchModule_runs_widened_edgeOnly`
(`SolverSearchLinkWithV.lean`). -/
theorem solverSearchModuleWithV_runs_widened_edgeOnly {w b init : ℕ} {p : Program} {op : ℕ → ℕ}
    (I : Instance) (U k V : ℕ) (hw : ipmQualityParameterWordBits I.m U k ≤ w)
    (A : MinRatioDataStructureWithFailure) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep A.State) (hp : p.HasAt b (solverSearchModuleWithV b init op))
    (hA : MinRatioSpecWithFailureEdgeOnlyConnectedUpTo A (1 / (2 : ℝ) ^ k)
      (Num.IPM.alphaPrime I.m U / 8)
      ((ipmQualityRangeExponent I.m U k + slackRangeExponent I.m U + 6 : ℕ) : ℝ)
      ((1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m U / 1024) I.m I.n)
    (hConn : MinRatioGraphConnected (namedInstance I))
    (himpl : R.Implements w p init op (minRatioMachineContractWithV (ipmQualityMinRatioFormat I.m U k hw)
      A (namedInstance I) I.m V (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m U / 8) rate allocation))
    (old : EpochLayout) (qp source heap B : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hE : old.exponent = ipmQualityRangeExponent I.m U k)
    (hfixed : TargetFixedInputs (ipmQualityMinRatioFormat I.m U k hw) I old qp qp heap (1 / 4)
      ((25 / 32 : ℝ) * ((1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m U / 32) ^ 2 / 50)
      (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow (ipmQualityMinRatioFormat I.m U k hw) I old.exponent source heap mem)
    (hhalf : ∀ e, (1 / 2 : ℝ) ≤ epochVector (ipmQualityMinRatioFormat I.m U k hw) I mem source e - (I.edge e).lower ∧
      (1 / 2 : ℝ) ≤ (I.edge e).upper - epochVector (ipmQualityMinRatioFormat I.m U k hw) I mem source e)
    (hwords : ∀ z ∈ targetOffsetPacket old (ipmQualityMinRatioFormat I.m U k hw) I 0 qp source heap (targetTestLimit I.m U k) (I.m * U ^ 2), z < 2 ^ w)
    (hV : V < 2 ^ w)
    (hRadius : 2 * (I.m * U ^ 2) < 2 ^ w)
    (hRound : targetSearchRounds (I.m * U ^ 2) < 2 ^ w)
    (halloc : ∀ j < 4, ∀ args, allocation j args ≤ B)
    (hLimit : targetTestLimit I.m U k < 2 ^ w)
    (hspace : heap + targetSearchSpace (ipmQualityMinRatioFormat I.m U k hw) I.m U k old.exponent B < 2 ^ w)
    (hz : ZeroFrom mem heap) (hm : 0 < I.m) (hU : 0 < U) (hsize : 2 ≤ I.m * U)
    (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m, 0 ≤ (I.edge e).lower) :
    let F := ipmQualityMinRatioFormat I.m U k hw
    let limit := targetTestLimit I.m U k
    let radius := I.m * U ^ 2
    ∃ v final cost, ∃ z : ℤ, ∃ fstar,
      Runs w p ω (targetSearchBodyWithV (b + 1))
        (startState (targetOffsetPacket old F I 0 qp source heap limit radius ++ [targetSearchRounds radius, V]) mem pos)
        (.returned v) final cost ∧
      I.IsMinCostFlow fstar ∧ I.cost fstar = (z : ℝ) ∧
      TargetOffsetResult F I old.exponent heap v z z mem final.mem ∧ final.mem (v - 1) = 1 ∧
      v ≤ heap + targetSearchSpace F I.m U k old.exponent B ∧
      cost ≤ targetSearchCost F I.m U k old.exponent rate :=
  solverSearchModuleWithV_runs_widened_upTo_on I U k V hw A rate allocation R hp
    (hA.toUpToOn_fixedGraph (namedInstance I) hConn)
    (MinRatioStageFixed.admits (namedInstance I) (by push_cast; linarith)) himpl old qp source heap B mem pos ω
    hE hfixed hflow hhalf hwords hV hRadius hRound halloc hLimit hspace hz hm hU hsize hI hnums hLower

end MinCostFlow.IPM.Machine
