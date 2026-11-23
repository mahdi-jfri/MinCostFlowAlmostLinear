module

public import MinCostFlow.MinRatio.PathPayloadAdapter
public import MinCostFlow.LinkCut.ForestModelSplice
public import MinCostFlow.MinRatio.PathPayloadRead
public import MinCostFlow.MinRatio.PathPayloadFits
public import MinCostFlow.MinRatio.PathTreeCost
public import WordRAM.DataStructure

/-!
# Section 6 tree-operation contract

The abstract state is the link-cut tree state `LctState`, instantiated with the
Section 6 payload. Link, Cut, path updates, and summaries use the model
functions of the link-cut trees. Point reads expose the node before reading its value.
Point writes expose it, change the value, and pull its summary.

Finding a ready edge permits any ready edge, as the paper does. It exposes
that edge and returns its slot, or returns zero exactly when none is ready.
The implementation remains deterministic even though its specification
does not prescribe a tie rule. Numeric-fit premises are representation
conditions. A caller must establish them from its chosen precision and range.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut

abbrev PathTreeState := LctState (Option PathEdgeValue) PathSummary PathTag

def pathTreeFits (h L : ℕ) (s : PathTreeState) : Prop :=
  ∀ x ≤ 2 * s.n,
    PathEdgeFits h L (s.splay.nodes x).val ∧ PathSummaryFits h L (s.splay.nodes x).sum ∧
      Num.Fits h L (s.splay.nodes x).tag.flow ∧ Num.Fits h L (s.splay.nodes x).tag.detector

def pathTreeActive (s : PathTreeState) (x : ℕ) : Prop :=
  ∃ trees free depth, LctInvWith pathPayload s trees free depth ∧ x ∈ trees.flatMap AuxTree.toList

def pathTreeReady (s : PathTreeState) (x : ℕ) : Prop :=
  isEdgeSlot s.n x ∧ pathTreeActive s x ∧
    ∃ v, ((lctExpose pathPayload s x).splay.nodes x).val = some v ∧ 0 ≤ v.detector

def pathTreeConnected (s : PathTreeState) (u v : ℕ) : Prop :=
  (lctConnectedCost pathPayload s u v).2.1 = true

def pathTreeWrite (s : PathTreeState) (x : ℕ) (v : Option PathEdgeValue) : PathTreeState :=
  let exposed := lctExpose pathPayload s x
  let updated := exposed.splay.updateNode x (fun node => { node with val := v })
  { exposed with splay := SplayState.pull pathPayload updated x }

/-- The parameter contract used by Section 6. Indices are Link, Cut,
PathApply, PathSummary, PointRead, PointWrite, and FindReady.
Tree vertices and slots use the one-based node names of the link-cut trees. -/
noncomputable def pathTreeMachineContract {w : ℕ} (fmt : Num.Format w) (L constant : ℕ)
    (allocation : ℕ → ℕ → List ℕ → ℕ) : DataStructure PathTreeState where
  initPre args _ := ∃ n heap, args = [n, L, heap] ∧ 2 * n + 1 < 2 ^ w ∧
    L < 2 ^ w ∧ fmt.precision < 2 ^ w ∧ Nat.log 2 (2 * n + 1) ≤ fmt.limbBits * L
  initPost args _ s _ := s = lctInit pathPayload (args.getD 0 0) none
  initCost args _ := constant * (L + 1) ^ 2 * (args.getD 0 0 + 1)
  initSpace args _ := allocation 7 (args.getD 0 0) args
  pre i s args mem := LctInv pathPayload s ∧ pathTreeFits fmt.limbBits L s ∧
    2 * s.n + 1 < 2 ^ w ∧ Nat.log 2 (2 * s.n + 1) ≤ fmt.limbBits * L ∧
    match i with
    | 0 => ∃ handle u v value heap, args = [handle, u, v, value, heap] ∧
        isVertex s.n u ∧ isVertex s.n v ∧ ¬ pathTreeConnected s u v ∧ s.freeHead ≠ 0 ∧
        value + (2 + 4 * L) ≤ heap ∧ PathEdgeAt mem value fmt.limbBits L (readPathEdge mem value fmt.limbBits L) ∧
        (readPathEdge mem value fmt.limbBits L).isSome = true ∧
        pathTreeFits fmt.limbBits L (lctLink pathPayload s u v (readPathEdge mem value fmt.limbBits L))
    | 1 => ∃ handle u v heap, args = [handle, u, v, heap] ∧ isVertex s.n u ∧ isVertex s.n v ∧
        pathTreeFits fmt.limbBits L (lctCut pathPayload s u v)
    | 2 => ∃ handle u v tag heap, args = [handle, u, v, tag, heap] ∧
        isVertex s.n u ∧ isVertex s.n v ∧ pathTreeConnected s u v ∧ tag + 2 * L ≤ heap ∧
        PathTagAt mem tag fmt.limbBits L (readPathTag mem tag fmt.limbBits L) ∧
        pathTreeFits fmt.limbBits L (lctPathApply pathPayload s u v (readPathTag mem tag fmt.limbBits L))
    | 3 => ∃ handle u v heap, args = [handle, u, v, heap] ∧ isVertex s.n u ∧ isVertex s.n v ∧
        pathTreeConnected s u v ∧ pathTreeFits fmt.limbBits L (lctPathSummary pathPayload s u v).1
    | 4 => ∃ handle node heap, args = [handle, node, heap] ∧ pathTreeActive s node ∧
        pathTreeFits fmt.limbBits L (lctExpose pathPayload s node)
    | 5 => ∃ handle node value heap, args = [handle, node, value, heap] ∧
        isEdgeSlot s.n node ∧ pathTreeActive s node ∧ value + (2 + 4 * L) ≤ heap ∧
        PathEdgeAt mem value fmt.limbBits L (readPathEdge mem value fmt.limbBits L) ∧
        (readPathEdge mem value fmt.limbBits L).isSome = true ∧
        pathTreeFits fmt.limbBits L (pathTreeWrite s node (readPathEdge mem value fmt.limbBits L))
    | 6 => ∃ handle heap, args = [handle, heap] ∧
        ∀ x, pathTreeReady s x → pathTreeFits fmt.limbBits L (lctExpose pathPayload s x)
    | _ => False
  post i s args mem s' mem' := match i with
    | 0 => s' = lctLink pathPayload s (args.getD 1 0) (args.getD 2 0)
        (readPathEdge mem (args.getD 3 0) fmt.limbBits L) ∧ mem' (heapArg args) = s.freeHead
    | 1 => s' = lctCut pathPayload s (args.getD 1 0) (args.getD 2 0)
    | 2 => s' = lctPathApply pathPayload s (args.getD 1 0) (args.getD 2 0)
        (readPathTag mem (args.getD 3 0) fmt.limbBits L)
    | 3 => let result := lctPathSummary pathPayload s (args.getD 1 0) (args.getD 2 0)
        s' = result.1 ∧ PathSummaryAt mem' (heapArg args) fmt.limbBits L result.2
    | 4 => s' = lctExpose pathPayload s (args.getD 1 0) ∧
        PathEdgeAt mem' (heapArg args) fmt.limbBits L (s'.splay.nodes (args.getD 1 0)).val
    | 5 => s' = pathTreeWrite s (args.getD 1 0) (readPathEdge mem (args.getD 2 0) fmt.limbBits L)
    | 6 => (mem' (heapArg args) = 0 ∧ s' = s ∧ ¬ ∃ x, pathTreeReady s x) ∨
        ∃ x, mem' (heapArg args) = x ∧ pathTreeReady s x ∧ s' = lctExpose pathPayload s x
    | _ => False
  cost _ s _ _ := pathTreeBudget constant L s.n
  space i s args _ := allocation i s.n args

end MinCostFlow.MinRatio

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut

private def exampleTree : PathTreeState := lctInit pathPayload 1 none

private theorem exampleTree_inv : LctInv pathPayload exampleTree := by
  refine ⟨[.node 1 .leaf .leaf], [], (fun _ => 1), ?_⟩
  exact (lctInit_spec pathPayload_laws 1 none).1

private theorem exampleTree_fits : pathTreeFits 1 4 exampleTree := by
  intro x hx
  change x ≤ 2 at hx
  interval_cases x <;>
    (change True ∧ (Num.Fits 1 4 0 ∧ Num.Fits 1 4 0 ∧ True) ∧
      Num.Fits 1 4 0 ∧ Num.Fits 1 4 0
     unfold Num.Fits
     decide)

private theorem exampleTree_expose_fits : pathTreeFits 1 4 (lctExpose pathPayload exampleTree 1) := by
  intro x hx
  change x ≤ 2 at hx
  interval_cases x <;>
    (change True ∧ (Num.Fits 1 4 0 ∧ Num.Fits 1 4 0 ∧ True) ∧
      Num.Fits 1 4 0 ∧ Num.Fits 1 4 0
     unfold Num.Fits
     decide)

private theorem exampleTree_active : pathTreeActive exampleTree 1 := by
  refine ⟨[.node 1 .leaf .leaf], [], (fun _ => 1), (lctInit_spec pathPayload_laws 1 none).1, ?_⟩
  simp [AuxTree.toList]

private theorem exampleTree_no_ready : ¬ ∃ x, pathTreeReady exampleTree x := by
  rintro ⟨x, hx⟩
  have he := hx.1
  change 1 + 1 ≤ x ∧ x < 2 * 1 at he
  omega

/-- Initialization, point readout, and empty detection are consistent on
one actual link-cut tree state. No generic machine implementation is assumed here. -/
theorem pathTreeMachineContract_example :
    ∃ (fmt : Num.Format 8) (s t : PathTreeState),
      let D := pathTreeMachineContract fmt 4 1024 (fun _ _ _ => 16)
      D.initPre [1, 4, 4] (fun _ => 0) ∧ D.initPost [1, 4, 4] (fun _ => 0) s (fun _ => 0) ∧
      D.pre 4 s [0, 1, 4] (fun _ => 0) ∧ D.post 4 s [0, 1, 4] (fun _ => 0) t (fun _ => 0) ∧
      D.pre 6 s [0, 4] (fun _ => 0) ∧ D.post 6 s [0, 4] (fun _ => 0) s (fun _ => 0) := by
  let fmt : Num.Format 8 := ⟨1, 0, by decide, by decide, by decide⟩
  refine ⟨fmt, exampleTree, lctExpose pathPayload exampleTree 1, ?_⟩
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_⟩
  · exact ⟨1, 4, rfl, by decide, by decide, by decide, by decide⟩
  · refine ⟨exampleTree_inv, exampleTree_fits, by decide, by decide, 0, 1, 4, rfl, exampleTree_active,
      exampleTree_expose_fits⟩
  · refine ⟨rfl, ?_⟩
    have hv : ((lctExpose pathPayload exampleTree 1).splay.nodes 1).val = none := by rfl
    change PathEdgeAt (fun _ => 0) 4 1 4 ((lctExpose pathPayload exampleTree 1).splay.nodes 1).val
    rw [hv]
    rfl
  · refine ⟨exampleTree_inv, exampleTree_fits, by decide, by decide, 0, 4, rfl, ?_⟩
    intro x hx
    exact False.elim (exampleTree_no_ready ⟨x, hx⟩)
  · exact Or.inl ⟨rfl, rfl, exampleTree_no_ready⟩

end MinCostFlow.MinRatio

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut

/-- A ready answer uses an active, nonzero edge slot. -/
theorem pathTreeReady_bounds {s : PathTreeState} {x : ℕ} (hx : pathTreeReady s x) :
    x ≠ 0 ∧ x < 2 * s.n := by
  have he := hx.1
  change s.n + 1 ≤ x ∧ x < 2 * s.n at he
  exact ⟨by omega, he.2⟩

/-- A path-update answer is the link-cut tree model applied to the tag
specified by the numeric argument layout. -/
theorem pathTreeMachineContract_apply_state {w : ℕ} {fmt : Num.Format w} {L constant : ℕ}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {s s' : PathTreeState}
    {handle u v a heap : ℕ} {mem mem' : ℕ → ℕ} {tag : PathTag}
    (ht : PathTagAt mem a fmt.limbBits L tag)
    (hp : (pathTreeMachineContract fmt L constant allocation).post 2 s
      [handle, u, v, a, heap] mem s' mem') : s' = lctPathApply pathPayload s u v tag := by
  change s' = lctPathApply pathPayload s u v (readPathTag mem a fmt.limbBits L) at hp
  rw [readPathTag_eq ht] at hp
  exact hp

/-- A Link answer uses exactly the edge value specified by its input layout. -/
theorem pathTreeMachineContract_link_state {w : ℕ} {fmt : Num.Format w} {L constant : ℕ}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {s s' : PathTreeState}
    {handle u v a heap : ℕ} {mem mem' : ℕ → ℕ} {value : Option PathEdgeValue}
    (hv : PathEdgeAt mem a fmt.limbBits L value)
    (hp : (pathTreeMachineContract fmt L constant allocation).post 0 s
      [handle, u, v, a, heap] mem s' mem') : s' = lctLink pathPayload s u v value := by
  have hs := hp.1
  change s' = lctLink pathPayload s u v (readPathEdge mem a fmt.limbBits L) at hs
  rw [readPathEdge_eq hv] at hs
  exact hs

/-- A path-summary readout decodes to the exact answer of the link-cut tree model. -/
theorem pathTreeMachineContract_summary_read {w : ℕ} {fmt : Num.Format w} {L constant : ℕ}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {s s' : PathTreeState}
    {handle u v heap : ℕ} {mem mem' : ℕ → ℕ}
    (hp : (pathTreeMachineContract fmt L constant allocation).post 3 s
      [handle, u, v, heap] mem s' mem') :
    readPathSummary mem' heap fmt.limbBits L = (lctPathSummary pathPayload s u v).2 := by
  exact readPathSummary_eq hp.2

/-- A zero answer to FindReady means precisely that no ready edge remains. -/
theorem pathTreeMachineContract_find_zero {w : ℕ} {fmt : Num.Format w} {L constant : ℕ}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {s s' : PathTreeState}
    {handle heap : ℕ} {mem mem' : ℕ → ℕ}
    (hp : (pathTreeMachineContract fmt L constant allocation).post 6 s
      [handle, heap] mem s' mem') (hz : mem' heap = 0) : s' = s ∧ ¬ ∃ x, pathTreeReady s x := by
  rcases hp with ⟨_, hs, hn⟩ | ⟨x, hx, hready, _⟩
  · exact ⟨hs, hn⟩
  · change mem' heap = x at hx
    have hx0 : x = 0 := hx.symm.trans hz
    exact False.elim ((pathTreeReady_bounds hready).1 hx0)

/-- A nonzero FindReady answer identifies the exposed ready slot. -/
theorem pathTreeMachineContract_find_nonzero {w : ℕ} {fmt : Num.Format w} {L constant : ℕ}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {s s' : PathTreeState}
    {handle heap : ℕ} {mem mem' : ℕ → ℕ}
    (hp : (pathTreeMachineContract fmt L constant allocation).post 6 s
      [handle, heap] mem s' mem') (hz : mem' heap ≠ 0) :
    pathTreeReady s (mem' heap) ∧ s' = lctExpose pathPayload s (mem' heap) := by
  rcases hp with ⟨hzero, _, _⟩ | ⟨x, hx, hr, hs⟩
  · exact (hz hzero).elim
  · change mem' heap = x at hx
    rw [hx]
    exact ⟨hr, hs⟩

end MinCostFlow.MinRatio
