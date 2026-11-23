module

public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.Spanner.Embedding
public import MinCostFlow.Spanner.Tools
public import MinCostFlow.Spanner.Subgraph
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Algorithm 4 (`Sparsify`) model

This file formalizes Algorithm 4 (`Sparsify(H', J, Π_{J → H'})`, `spanner.tex`, page 42) over
`Cited.Graph` with `LocalSpannerTools` / `SpannerTools` as parameters:

- **Pre-step**: separate self-loops of `J` (`stripLoops J`); self-loops are embedded as
  `Walk.empty` (`jtree_appendix.tex`, line 63).
- **Task 1** (`buildWitness`, lines 76–81): decompose `stripLoops J` via `Decompose`, construct
  witness expanders `W_{J_i[X]}` (`i > 0`) via `ConstructExpander`, and assemble `W` with edge
  weights `φ_dec · 2^i`.
- **Task 2** (`task2`, lines 84–103): embed `W` into `J` in rounds (`η₁`) with `PathDS` on each
  `J_i[X]`, deleting all active edges whose `Π_{J → H'}` path visits any vertex `x ∈ V(H')`
  reaching `vcong(Π_{J → H'} ∘ Π_{W → J}, x) ≥ η₁ · τ₁`.
- **Task 3** (`task3`, lines 105–121): embed `J` into `W` in rounds (`η₂`) with `PathDS` on each
  `W_{J_i[X]}`, deleting any undeleted edge `e' ∈ E(W_{J_i[X]})` reaching
  `econg(Π_{J → W}, e') ≥ η₂ · τ₂`.
- **Return** (line 122): `J̃ = Π_{W → J}(W)` and `Π_{J → J̃} = Π_{W → J̃} ∘ Π_{J → W}`, together
  with explicit tool-call and step counters `SparsifyStats`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## Generic bounded loop combinators -/

/-- Bounded while loop: repeats `step` while `cond s = true`, up to `fuel` iterations. -/
def whileFuel {α : Type*} (fuel : ℕ) (cond : α → Bool) (step : α → α) (s : α) : α :=
  match fuel with
  | 0 => s
  | k + 1 => if cond s then whileFuel k cond step (step s) else s

/-- Bounded do-while loop: executes `step` once, then repeats while `cond` holds. -/
def doWhileFuel {α : Type*} (fuel : ℕ) (cond : α → Bool) (step : α → α) (s : α) : α :=
  whileFuel fuel cond step (step s)

theorem whileFuel_inv {α : Type*} (P : α → Prop) (cond : α → Bool) (step : α → α)
    (hstep : ∀ s, P s → cond s = true → P (step s)) :
    ∀ fuel s, P s → P (whileFuel fuel cond step s) := by
  intro fuel
  induction fuel with
  | zero => intro s hs; exact hs
  | succ k ih =>
    intro s hs
    unfold whileFuel
    split_ifs with hc
    · exact ih (step s) (hstep s hs hc)
    · exact hs

theorem whileFuel_monotone {α : Type*} (P : α → Prop) (R : α → α → Prop)
    (hrefl : ∀ s, R s s) (htrans : ∀ a b c, R a b → R b c → R a c)
    (cond : α → Bool) (step : α → α)
    (hstep : ∀ s, P s → cond s = true → P (step s) ∧ R s (step s)) :
    ∀ fuel s, P s → R s (whileFuel fuel cond step s) := by
  intro fuel
  induction fuel with
  | zero => intro s _; exact hrefl s
  | succ k ih =>
    intro s hs
    unfold whileFuel
    split_ifs with hc
    · have ⟨hP', hR⟩ := hstep s hs hc
      exact htrans _ _ _ hR (ih (step s) hP')
    · exact hrefl s

theorem whileFuel_done {α : Type*} (P : α → Prop) (meas : α → ℕ)
    (cond : α → Bool) (step : α → α)
    (hstep : ∀ s, P s → cond s = true → P (step s) ∧ meas (step s) < meas s) :
    ∀ fuel s, P s → meas s ≤ fuel → cond (whileFuel fuel cond step s) = false := by
  intro fuel
  induction fuel with
  | zero =>
    intro s hs hle
    have h0 : meas s = 0 := Nat.eq_zero_of_le_zero hle
    by_contra hc
    have hlt := (hstep s hs (Bool.eq_true_of_not_eq_false hc)).2
    omega
  | succ k ih =>
    intro s hs hle
    unfold whileFuel
    split_ifs with hc
    · have ⟨hP', hlt⟩ := hstep s hs hc
      exact ih (step s) hP' (by omega)
    · exact Bool.eq_false_iff.mpr hc

/-! ## Task 1: Witness graph construction (lines 76–81) -/

/-- Metadata for a single nontrivial connected component `X` of `J_i` (`i > 0`). -/
structure CompInfo where
  /-- Decomposition level `i > 0`. -/
  level : ℕ
  /-- Vertex subset `X ⊆ V(J)` of the component. -/
  X : Finset ℕ
  /-- Sorted vertex list `X.sort (· ≤ ·)` identifying `{0, …, |X| - 1}` with `X`. -/
  verts : List ℕ
  /-- Induced subgraph `J_i[X]` on `{0, …, |X| - 1}`. -/
  J_sub : Graph
  /-- Map from edge index in `J_sub` to edge index in `J`. -/
  jSubOrigEdges : List ℕ
  /-- Witness expander `W_{J_i[X]}` on `{0, …, |X| - 1}`. -/
  W_sub : Graph
  /-- Starting edge index of `W_sub` inside `W`. -/
  wStart : ℕ

/-- Default dummy `CompInfo` for `List.getD`. -/
def defaultCompInfo : CompInfo :=
  ⟨1, ∅, [], ⟨0, []⟩, [], ⟨0, []⟩, 0⟩

/-- Origin of an edge in the witness graph `W`. -/
inductive WEdgeSource where
  | fromJ0 (jOrig : ℕ)
  | fromComp (compIdx eLocal : ℕ)
  deriving DecidableEq

/-- Origin of an edge in `J`. -/
inductive JEdgeSource where
  | isLoop
  | inJ0 (eW : ℕ)
  | inComp (compIdx jLocal : ℕ)
  deriving DecidableEq

/-- Data produced by Task 1 (`Decompose` and witness graph construction). -/
structure WitnessData where
  /-- Input graph `J` with self-loops removed. -/
  J0_strip : Graph
  /-- Map from edge index in `J0_strip` to edge index in `J`. -/
  nlIdx : List ℕ
  /-- Output of `Decompose(J0_strip)`. -/
  decomp : DecomposeOutput
  /-- Conductance parameter `φ_dec = φ_dec(J0_strip)`. -/
  φ_dec : ℝ
  /-- Degree multiplier `c_deg` of `ConstructExpander`. -/
  c_deg : ℝ
  /-- Expander constant `φ_Const` of `ConstructExpander`. -/
  φ_Const : ℝ
  /-- Edge indices in `J` assigned to `J_0`. -/
  j0Edges : List ℕ
  /-- Components `(i, X)` for `0 < i ≤ decomp.ℓ`. -/
  comps : List CompInfo
  /-- Witness graph `W` on `J.n` vertices. -/
  W : Graph
  /-- Weight function on edges of `W` (`φ_dec · 2^i`). -/
  wW : ℕ → ℝ
  /-- Origin of each edge of `W`. -/
  wSources : List WEdgeSource
  /-- Origin of each edge of `J`. -/
  jSources : List JEdgeSource
  /-- Edge-count cap `M_W` used when initializing `PathDS` on `W_{J_i[X]}`. -/
  M_W : ℕ
  /-- Unified `φ_ds` parameter for `PathDS` on both `J_i[X]` and `W_{J_i[X]}`. -/
  φ_ds : ℝ
  /-- Unified `γ_ExpPath` parameter. -/
  γ_ExpPath : ℝ
  /-- Unified `γ_del` parameter. -/
  γ_del : ℝ
  /-- Threshold `τ₁` (`Algorithm 4`, line 74). -/
  τ₁ : ℝ
  /-- Threshold `τ₂` (`Algorithm 4`, line 74). -/
  τ₂ : ℝ

/-- Build `CompInfo` list from `rawComps : List (ℕ × Finset ℕ)` starting at edge offset `offset`
in `W`. -/
noncomputable def buildComps {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (J0_strip : Graph) (nlIdx : List ℕ)
    (decomp : DecomposeOutput) (φ_dec : ℝ) :
    ℕ → List (ℕ × Finset ℕ) → List CompInfo
  | _, [] => []
  | offset, (i, X) :: rest =>
    let J_i := decomp.graphAt J0_strip i
    let vs := vertsOf X
    let J_sub := inducedSubgraph J_i X
    let jLevelEdges := decomp.edgesAt J0_strip i
    let jSubOrigEdges := (insideIndices J_i X).map fun a => nlIdx.getD (jLevelEdges.getD a 0) 0
    let wVec : ℕ → ℝ := fun k => (J_i.degIn X (vs.getD k 0) : ℝ) / (φ_dec * (2 ^ i : ℝ))
    let W_sub := tools.constructExpander.construct X.card wVec
    let c : CompInfo :=
      { level := i
        X := X
        verts := vs
        J_sub := J_sub
        jSubOrigEdges := jSubOrigEdges
        W_sub := W_sub
        wStart := offset }
    c :: buildComps tools J0_strip nlIdx decomp φ_dec (offset + W_sub.m) rest

/-- Build the `W`-edges contributed by `c : CompInfo` (lifting vertices back via `c.verts`). -/
def compWEdges (c : CompInfo) : List (ℕ × ℕ) :=
  c.W_sub.edges.map fun e => (c.verts.getD e.1 0, c.verts.getD e.2 0)

/-- Compute the `W`-weight function for an edge index `eW` from `j0Len` and `comps`. -/
noncomputable def witnessWeight (φ_dec : ℝ) (j0Len : ℕ) (comps : List CompInfo) (eW : ℕ) : ℝ :=
  if eW < j0Len then φ_dec
  else match comps.find? (fun c => decide (c.wStart ≤ eW ∧ eW < c.wStart + c.W_sub.m)) with
    | some c => φ_dec * (2 ^ c.level : ℝ)
    | none => 0

/-- Find the `CompInfo` index and local edge index of an edge `jOrig` in `J`, if it lies in a
component `c` with `level > 0`. -/
def findJCompEdge (jOrig : ℕ) : List CompInfo → ℕ → Option (ℕ × ℕ)
  | [], _ => none
  | c :: cs, idx =>
    if jOrig ∈ c.jSubOrigEdges then some (idx, c.jSubOrigEdges.idxOf jOrig)
    else findJCompEdge jOrig cs (idx + 1)

/-- **Task 1** of Algorithm 4 (`spanner.tex`, lines 74–81): decompose `stripLoops J`, construct
witness expanders `W_{J_i[X]}` (`i > 0`), build `W`, and set parameters `τ₁, τ₂`. -/
noncomputable def buildWitness {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk) : WitnessData :=
  let J0_strip := stripLoops J
  let nlIdx := nonloopIndices J
  let decomp := tools.decompose.decompose J0_strip
  let φ_dec := tools.decompose.φ_dec J0_strip
  let c_deg := tools.constructExpander.c_deg
  let φ_Const := tools.constructExpander.φ_Const
  let j0Edges := (decomp.edgesAt J0_strip 0).map fun k => nlIdx.getD k 0
  let rawComps := (List.range decomp.ℓ).flatMap fun i' =>
    (decomp.comps (i' + 1)).map fun X => (i' + 1, X)
  let comps := buildComps tools J0_strip nlIdx decomp φ_dec j0Edges.length rawComps
  let wJ0Edges := j0Edges.map fun jOrig => J.edges.getD jOrig (0, 0)
  let wCompEdges := comps.flatMap compWEdges
  let W : Graph := ⟨J.n, wJ0Edges ++ wCompEdges⟩
  let wW := witnessWeight φ_dec j0Edges.length comps
  let wSourcesJ0 := j0Edges.map WEdgeSource.fromJ0
  let wSourcesComps := comps.zipIdx.flatMap fun (c, ci) =>
    (List.range c.W_sub.m).map fun eLocal => WEdgeSource.fromComp ci eLocal
  let wSources := wSourcesJ0 ++ wSourcesComps
  let jSources := (List.range J.m).map fun eJ =>
    if eJ ∈ j0Edges then JEdgeSource.inJ0 (j0Edges.idxOf eJ)
    else match findJCompEdge eJ comps 0 with
      | some (ci, jLocal) => JEdgeSource.inComp ci jLocal
      | none => JEdgeSource.isLoop
  let M_W := Nat.ceil (c_deg * (J0_strip.m : ℝ) / φ_dec) + 1
  let φ_J := tools.pathDS.φ_out φ_dec J0_strip.m
  let φ_W := tools.pathDS.φ_out φ_Const M_W
  let φ_ds := min φ_J φ_W
  let γ_ExpPath := max (tools.pathDS.γ_ExpPath φ_dec J0_strip.m) (tools.pathDS.γ_ExpPath φ_Const M_W)
  let γ_del := max (tools.pathDS.γ_del φ_dec J0_strip.m) (tools.pathDS.γ_del φ_Const M_W)
  let τ₁ := 2 * γ_ExpPath * (length J embJH : ℝ) * γ_del *
    (vcong J H' (fun _ => 1) embJH + (maxDeg J : ℝ)) / φ_ds
  let τ₂ := γ_ExpPath * γ_del / φ_ds
  { J0_strip := J0_strip
    nlIdx := nlIdx
    decomp := decomp
    φ_dec := φ_dec
    c_deg := c_deg
    φ_Const := φ_Const
    j0Edges := j0Edges
    comps := comps
    W := W
    wW := wW
    wSources := wSources
    jSources := jSources
    M_W := M_W
    φ_ds := φ_ds
    γ_ExpPath := γ_ExpPath
    γ_del := γ_del
    τ₁ := τ₁
    τ₂ := τ₂ }

/-! ## Task 2: Embed `W` into `J` (lines 84–103) -/

/-- Lift a walk in `c.J_sub` back to `J` using `c.verts` and `c.jSubOrigEdges`. -/
def liftJSubWalk (c : CompInfo) (P : Walk) : Walk :=
  ⟨P.verts.map (fun k => c.verts.getD k 0), P.edges.map (fun b => c.jSubOrigEdges.getD b 0)⟩

/-- Lift a walk in `c.W_sub` back to `W` using `c.verts` and `c.wStart`. -/
def liftWSubWalk (c : CompInfo) (P : Walk) : Walk :=
  ⟨P.verts.map (fun k => c.verts.getD k 0), P.edges.map (fun eL => c.wStart + eL)⟩

/-- State of Task 2 (embedding `W` into `J`). -/
structure Task2State (DSState : Type) where
  η₁ : ℕ
  embWJ : ℕ → Option Walk
  dsJ : List DSState
  processedVerts : Finset ℕ
  initCountJ : ℕ
  initEdgesJ : ℕ
  getPathCountJ : ℕ
  deleteCountJ : ℕ
  vcongUpdates : ℕ
  middleIters1 : ℕ
  innerIters1 : ℕ

/-- Initial state before Task 2's do-while loop (Algorithm 4, line 84). -/
def task2Init {DSState : Type} (J : Graph) (wd : WitnessData) : Task2State DSState :=
  let embWJ : ℕ → Option Walk := fun eW =>
    if eW < wd.W.m then
      match wd.wSources.getD eW (WEdgeSource.fromJ0 0) with
      | WEdgeSource.fromJ0 jOrig =>
        let e := J.edges.getD jOrig (0, 0)
        some (Walk.single e.1 e.2 jOrig)
      | WEdgeSource.fromComp _ _ => none
    else none
  ⟨0, embWJ, [], ∅, 0, 0, 0, 0, 0, 0, 0⟩

/-- Find a vertex `x ∈ V(H') \ processedVerts` whose vertex congestion in
`Π_{J → H'} ∘ Π_{W → J}` is at least `η₁ · τ₁` (Algorithm 4, line 98). -/
noncomputable def findCongestedVertex {DSState : Type} (H' J : Graph) (embJH : ℕ → Walk)
    (wd : WitnessData) (s : Task2State DSState) : Option ℕ :=
  letI := Classical.propDecidable
  (List.range H'.n).find? fun x =>
    decide (x ∉ s.processedVerts ∧
      (s.η₁ : ℝ) * wd.τ₁ ≤ vcongAt wd.W wd.wW (compose J embJH (partialToWalk s.embWJ)) x)

/-- Condition for Task 2's inner while loop (Algorithm 4, line 98). -/
noncomputable def task2InnerCond {DSState : Type} (H' J : Graph) (embJH : ℕ → Walk)
    (wd : WitnessData) (s : Task2State DSState) : Bool :=
  (findCongestedVertex H' J embJH wd s).isSome

/-- Delete from one `ds` all active edges `b < c.J_sub.m` whose `Π_{J → H'}` path visits `x`. -/
noncomputable def deleteEdgesAtVertex (pathDS : PathDSTool) (embJH : ℕ → Walk) (x : ℕ)
    (c : CompInfo) (ds : pathDS.State) : pathDS.State × ℕ :=
  letI := Classical.propDecidable
  let toDel := (List.range c.J_sub.m).filter fun b =>
    decide (b ∉ pathDS.deleted ds ∧ x ∈ (embJH (c.jSubOrigEdges.getD b 0)).verts)
  toDel.foldl (fun (acc : pathDS.State × ℕ) b =>
    let res := pathDS.delete acc.1 b
    (res.1, acc.2 + 1)) (ds, 0)

/-- One iteration of Task 2's inner while loop (Algorithm 4, lines 98–101). -/
noncomputable def task2InnerStep (pathDS : PathDSTool) (H' J : Graph) (embJH : ℕ → Walk)
    (wd : WitnessData) (s : Task2State pathDS.State) : Task2State pathDS.State :=
  match findCongestedVertex H' J embJH wd s with
  | none => s
  | some x =>
    let updated := (wd.comps.zip s.dsJ).map fun (c, ds) =>
      deleteEdgesAtVertex pathDS embJH x c ds
    let dsJ' := updated.map Prod.fst
    let dels := (updated.map Prod.snd).sum
    { s with
      dsJ := dsJ'
      processedVerts := insert x s.processedVerts
      deleteCountJ := s.deleteCountJ + dels
      innerIters1 := s.innerIters1 + 1 }

/-- Find an unembedded edge `eW < W.m` whose endpoints in its component `(ci, c)` lie in
`X \ V̂_{J_i[X]}` (Algorithm 4, line 94). -/
noncomputable def findReadyWEdge (pathDS : PathDSTool) (wd : WitnessData)
    (s : Task2State pathDS.State) : Option (ℕ × ℕ × ℕ) :=
  letI := Classical.propDecidable
  let dsDefault := pathDS.init wd.φ_dec wd.J0_strip.m ⟨0, []⟩
  ((List.range wd.W.m).filterMap fun eW =>
    if (s.embWJ eW).isNone then
      match wd.wSources.getD eW (WEdgeSource.fromJ0 0) with
      | WEdgeSource.fromJ0 _ => none
      | WEdgeSource.fromComp ci eLocal =>
        let c := wd.comps.getD ci defaultCompInfo
        let ds := s.dsJ.getD ci dsDefault
        let eLoc := c.W_sub.edges.getD eLocal (0, 0)
        if eLoc.1 ∉ pathDS.Vhat ds ∧ eLoc.2 ∉ pathDS.Vhat ds then
          some (eW, ci, eLocal)
        else none
    else none).head?

/-- Condition for Task 2's middle while loop (Algorithm 4, line 94). -/
noncomputable def task2MiddleCond (pathDS : PathDSTool) (wd : WitnessData)
    (s : Task2State pathDS.State) : Bool :=
  (findReadyWEdge pathDS wd s).isSome

/-- One iteration of Task 2's middle while loop (Algorithm 4, lines 94–102). -/
noncomputable def task2MiddleStep (pathDS : PathDSTool) (H' J : Graph) (embJH : ℕ → Walk)
    (wd : WitnessData) (s : Task2State pathDS.State) : Task2State pathDS.State :=
  match findReadyWEdge pathDS wd s with
  | none => s
  | some (eW, ci, eLocal) =>
    let dsDefault := pathDS.init wd.φ_dec wd.J0_strip.m ⟨0, []⟩
    let c := wd.comps.getD ci defaultCompInfo
    let ds := s.dsJ.getD ci dsDefault
    let eLoc := c.W_sub.edges.getD eLocal (0, 0)
    let P_sub := pathDS.getPath ds eLoc.1 eLoc.2
    let P_J := liftJSubWalk c P_sub
    let updVerts := (P_J.edges.map fun e' => (embJH e').verts.length).sum
    let s1 : Task2State pathDS.State :=
      { s with
        embWJ := Function.update s.embWJ eW (some P_J)
        getPathCountJ := s.getPathCountJ + 1
        vcongUpdates := s.vcongUpdates + updVerts
        middleIters1 := s.middleIters1 + 1 }
    whileFuel H'.n (task2InnerCond H' J embJH wd) (task2InnerStep pathDS H' J embJH wd) s1

/-- One round of Task 2's outer do-while loop (Algorithm 4, lines 86–103). -/
noncomputable def task2Round (pathDS : PathDSTool) (H' J : Graph) (embJH : ℕ → Walk)
    (wd : WitnessData) (s : Task2State pathDS.State) : Task2State pathDS.State :=
  let dsInit := wd.comps.map fun c => pathDS.init wd.φ_dec wd.J0_strip.m c.J_sub
  let initEdges := (wd.comps.map fun c => c.J_sub.m).sum
  let s1 : Task2State pathDS.State :=
    { s with
      η₁ := s.η₁ + 1
      dsJ := dsInit
      processedVerts := ∅
      initCountJ := s.initCountJ + wd.comps.length
      initEdgesJ := s.initEdgesJ + initEdges }
  whileFuel wd.W.m (task2MiddleCond pathDS wd) (task2MiddleStep pathDS H' J embJH wd) s1

/-- Condition for Task 2's outer do-while loop (Algorithm 4, line 103). -/
def task2OuterCond {DSState : Type} (wd : WitnessData) (s : Task2State DSState) : Bool :=
  (List.range wd.W.m).any fun eW => (s.embWJ eW).isNone

/-- Full Task 2 execution (Algorithm 4, lines 84–103). -/
noncomputable def task2 (pathDS : PathDSTool) (H' J : Graph) (embJH : ℕ → Walk)
    (wd : WitnessData) : Task2State pathDS.State :=
  doWhileFuel wd.W.m (task2OuterCond wd) (task2Round pathDS H' J embJH wd) (task2Init J wd)

/-! ## Task 3: Embed `J` into `W` (lines 105–121) -/

/-- State of Task 3 (embedding `J` into `W`). -/
structure Task3State (DSState : Type) where
  η₂ : ℕ
  embJW : ℕ → Option Walk
  dsW : List DSState
  initCountW : ℕ
  initEdgesW : ℕ
  getPathCountW : ℕ
  deleteCountW : ℕ
  econgUpdates : ℕ
  middleIters2 : ℕ
  innerIters2 : ℕ

/-- Initial state before Task 3's do-while loop (Algorithm 4, line 105; self-loops map to
`Walk.empty`). -/
def task3Init {DSState : Type} (J : Graph) (wd : WitnessData) : Task3State DSState :=
  let embJW : ℕ → Option Walk := fun eJ =>
    if eJ < J.m then
      match wd.jSources.getD eJ JEdgeSource.isLoop with
      | JEdgeSource.isLoop => some Walk.empty
      | JEdgeSource.inJ0 eW =>
        let e := wd.W.edges.getD eW (0, 0)
        some (Walk.single e.1 e.2 eW)
      | JEdgeSource.inComp _ _ => none
    else none
  ⟨0, embJW, [], 0, 0, 0, 0, 0, 0, 0⟩

/-- Find an undeleted edge `(ci, eLocal)` in some `W_{J_i[X]}` whose edge congestion in
`Π_{J → W}` is at least `η₂ · τ₂` (Algorithm 4, line 117). -/
noncomputable def findCongestedWEdge (pathDS : PathDSTool) (J : Graph) (wd : WitnessData)
    (s : Task3State pathDS.State) : Option (ℕ × ℕ) :=
  letI := Classical.propDecidable
  let dsDefault := pathDS.init wd.φ_Const wd.M_W ⟨0, []⟩
  (wd.comps.zipIdx.flatMap fun (c, ci) =>
    let ds := s.dsW.getD ci dsDefault
    (List.range c.W_sub.m).filterMap fun eLocal =>
      if eLocal ∉ pathDS.deleted ds ∧
          (s.η₂ : ℝ) * wd.τ₂ ≤ econgAt J (fun _ => 1) wd.wW (partialToWalk s.embJW)
            (c.wStart + eLocal) then
        some (ci, eLocal)
      else none).head?

/-- Condition for Task 3's inner while loop (Algorithm 4, line 117). -/
noncomputable def task3InnerCond (pathDS : PathDSTool) (J : Graph) (wd : WitnessData)
    (s : Task3State pathDS.State) : Bool :=
  (findCongestedWEdge pathDS J wd s).isSome

/-- One iteration of Task 3's inner while loop (Algorithm 4, lines 117–118). -/
noncomputable def task3InnerStep (pathDS : PathDSTool) (J : Graph) (wd : WitnessData)
    (s : Task3State pathDS.State) : Task3State pathDS.State :=
  match findCongestedWEdge pathDS J wd s with
  | none => s
  | some (ci, eLocal) =>
    let dsDefault := pathDS.init wd.φ_Const wd.M_W ⟨0, []⟩
    let ds := s.dsW.getD ci dsDefault
    let res := pathDS.delete ds eLocal
    { s with
      dsW := s.dsW.set ci res.1
      deleteCountW := s.deleteCountW + 1
      innerIters2 := s.innerIters2 + 1 }

/-- Find an unembedded edge `eJ < J.m` whose endpoints in its component `(ci, c)` lie in
`X \ V̂_{W_{J_i[X]}}` (Algorithm 4, line 114). -/
noncomputable def findReadyJEdge (pathDS : PathDSTool) (J : Graph) (wd : WitnessData)
    (s : Task3State pathDS.State) : Option (ℕ × ℕ × ℕ) :=
  letI := Classical.propDecidable
  let dsDefault := pathDS.init wd.φ_Const wd.M_W ⟨0, []⟩
  ((List.range J.m).filterMap fun eJ =>
    if (s.embJW eJ).isNone then
      match wd.jSources.getD eJ JEdgeSource.isLoop with
      | JEdgeSource.isLoop => none
      | JEdgeSource.inJ0 _ => none
      | JEdgeSource.inComp ci jLocal =>
        let c := wd.comps.getD ci defaultCompInfo
        let ds := s.dsW.getD ci dsDefault
        let eLoc := c.J_sub.edges.getD jLocal (0, 0)
        if eLoc.1 ∉ pathDS.Vhat ds ∧ eLoc.2 ∉ pathDS.Vhat ds then
          some (eJ, ci, jLocal)
        else none
    else none).head?

/-- Condition for Task 3's middle while loop (Algorithm 4, line 114). -/
noncomputable def task3MiddleCond (pathDS : PathDSTool) (J : Graph) (wd : WitnessData)
    (s : Task3State pathDS.State) : Bool :=
  (findReadyJEdge pathDS J wd s).isSome

/-- One iteration of Task 3's middle while loop (Algorithm 4, lines 114–119). -/
noncomputable def task3MiddleStep (pathDS : PathDSTool) (J : Graph) (wd : WitnessData)
    (s : Task3State pathDS.State) : Task3State pathDS.State :=
  match findReadyJEdge pathDS J wd s with
  | none => s
  | some (eJ, ci, jLocal) =>
    let dsDefault := pathDS.init wd.φ_Const wd.M_W ⟨0, []⟩
    let c := wd.comps.getD ci defaultCompInfo
    let ds := s.dsW.getD ci dsDefault
    let eLoc := c.J_sub.edges.getD jLocal (0, 0)
    let P_sub := pathDS.getPath ds eLoc.1 eLoc.2
    let P_W := liftWSubWalk c P_sub
    let s1 : Task3State pathDS.State :=
      { s with
        embJW := Function.update s.embJW eJ (some P_W)
        getPathCountW := s.getPathCountW + 1
        econgUpdates := s.econgUpdates + P_W.edges.length
        middleIters2 := s.middleIters2 + 1 }
    whileFuel wd.W.m (task3InnerCond pathDS J wd) (task3InnerStep pathDS J wd) s1

/-- One round of Task 3's outer do-while loop (Algorithm 4, lines 107–121). -/
noncomputable def task3Round (pathDS : PathDSTool) (J : Graph) (wd : WitnessData)
    (s : Task3State pathDS.State) : Task3State pathDS.State :=
  let dsInit := wd.comps.map fun c => pathDS.init wd.φ_Const wd.M_W c.W_sub
  let initEdges := (wd.comps.map fun c => c.W_sub.m).sum
  let s1 : Task3State pathDS.State :=
    { s with
      η₂ := s.η₂ + 1
      dsW := dsInit
      initCountW := s.initCountW + wd.comps.length
      initEdgesW := s.initEdgesW + initEdges }
  whileFuel J.m (task3MiddleCond pathDS J wd) (task3MiddleStep pathDS J wd) s1

/-- Condition for Task 3's outer do-while loop (Algorithm 4, line 121). -/
def task3OuterCond {DSState : Type} (J : Graph) (s : Task3State DSState) : Bool :=
  (List.range J.m).any fun eJ => (s.embJW eJ).isNone

/-- Full Task 3 execution (Algorithm 4, lines 105–121). -/
noncomputable def task3 (pathDS : PathDSTool) (J : Graph) (wd : WitnessData) :
    Task3State pathDS.State :=
  doWhileFuel J.m (task3OuterCond J) (task3Round pathDS J wd) (task3Init J wd)

/-! ## Output & Work Statistics (`Sparsify`, line 122) -/

/-- Explicit step and tool-call counters of a run of Algorithm 4 (`Theorem 8.1`, conclusion 4). -/
structure SparsifyStats where
  decomposeCalls : ℕ
  constructCalls : ℕ
  constructVerts : ℕ
  constructWeightSum : ℝ
  η₁ : ℕ
  η₂ : ℕ
  dsInitCountJ : ℕ
  dsInitEdgesJ : ℕ
  dsGetPathCountJ : ℕ
  dsDeleteCountJ : ℕ
  vcongUpdates : ℕ
  middleIters1 : ℕ
  innerIters1 : ℕ
  dsInitCountW : ℕ
  dsInitEdgesW : ℕ
  dsGetPathCountW : ℕ
  dsDeleteCountW : ℕ
  econgUpdates : ℕ
  middleIters2 : ℕ
  innerIters2 : ℕ

/-- Output of `Sparsify(H', J, Π_{J → H'})` (`Algorithm 4`, line 122). -/
structure SparsifyOutput where
  /-- Witness data from Task 1 (exposed for Theorems/Claims). -/
  wd : WitnessData
  /-- Final `W → J` embedding. -/
  embWJ : ℕ → Walk
  /-- Final `J → W` embedding. -/
  embJW : ℕ → Walk
  /-- Edge numbers of `J` kept in `J̃` (deduplicated). -/
  keptEdges : List ℕ
  /-- The sparsifier `J̃ ⊆ J`. -/
  Jtilde : Graph
  /-- `W → J̃` embedding. -/
  embWJtilde : ℕ → Walk
  /-- Output embedding `Π_{J → J̃} = Π_{W → J̃} ∘ Π_{J → W}`. -/
  embJJtilde : ℕ → Walk
  /-- Explicit step and tool-call statistics. -/
  stats : SparsifyStats

/-- **Algorithm 4** (`Sparsify(H', J, Π_{J → H'})`, `spanner.tex`, page 42) parameterized by
`LocalSpannerTools`. -/
noncomputable def sparsifyLocal {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk) : SparsifyOutput :=
  let wd := buildWitness tools H' J embJH
  let s2 := task2 tools.pathDS H' J embJH wd
  let s3 := task3 tools.pathDS J wd
  let embWJ := partialToWalk s2.embWJ
  let embJW := partialToWalk s3.embJW
  let keptEdges := ((List.range wd.W.m).flatMap fun eW => (embWJ eW).edges).dedup
  let Jtilde : Graph := ⟨J.n, keptEdges.map fun j => J.edges.getD j (0, 0)⟩
  let embWJtilde : ℕ → Walk := fun eW => (embWJ eW).mapEdges keptEdges.idxOf
  let embJJtilde : ℕ → Walk := compose wd.W embWJtilde embJW
  let constructWeightSum : ℝ :=
    (wd.comps.map fun c =>
      ∑ k ∈ Finset.range c.X.card,
        ((wd.decomp.graphAt wd.J0_strip c.level).degIn c.X (c.verts.getD k 0) : ℝ) /
          (wd.φ_dec * (2 ^ c.level : ℝ))).sum
  let stats : SparsifyStats :=
    { decomposeCalls := 1
      constructCalls := wd.comps.length
      constructVerts := (wd.comps.map fun c => c.X.card).sum
      constructWeightSum := constructWeightSum
      η₁ := s2.η₁
      η₂ := s3.η₂
      dsInitCountJ := s2.initCountJ
      dsInitEdgesJ := s2.initEdgesJ
      dsGetPathCountJ := s2.getPathCountJ
      dsDeleteCountJ := s2.deleteCountJ
      vcongUpdates := s2.vcongUpdates
      middleIters1 := s2.middleIters1
      innerIters1 := s2.innerIters1
      dsInitCountW := s3.initCountW
      dsInitEdgesW := s3.initEdgesW
      dsGetPathCountW := s3.getPathCountW
      dsDeleteCountW := s3.deleteCountW
      econgUpdates := s3.econgUpdates
      middleIters2 := s3.middleIters2
      innerIters2 := s3.innerIters2 }
  { wd := wd
    embWJ := embWJ
    embJW := embJW
    keptEdges := keptEdges
    Jtilde := Jtilde
    embWJtilde := embWJtilde
    embJJtilde := embJJtilde
    stats := stats }

/-- **Algorithm 4** (`Sparsify(H', J, Π_{J → H'})`, `spanner.tex`, page 42) parameterized by
`SpannerTools`. -/
noncomputable def sparsify (tools : SpannerTools) (H' J : Graph) (embJH : ℕ → Walk) :
    SparsifyOutput :=
  let J0_strip := stripLoops J
  let φ_dec := tools.decompose.φ_dec J0_strip
  sparsifyLocal (tools.toLocal J.n (2 * (J.m : ℝ) / φ_dec)) H' J embJH

end MinCostFlow.Spanner
