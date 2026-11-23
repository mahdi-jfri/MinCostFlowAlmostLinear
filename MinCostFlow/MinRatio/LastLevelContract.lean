module

public import MinCostFlow.MinRatio.Layouts
public import MinCostFlow.Chain.SparseCoreTool
public import WordRAM.DataStructure

/-!
# Machine contract of the last-level builder

Definition 5.8 (pages 19–20) builds the last collection of low-stretch
forests from scratch. Section 6 (page 26) rebuilds it after each update.
The abstract state is exactly the pair returned by `LastLevelTool.build`.
Initialization takes `[graph, lengths, heap]` and writes the collection at
`heap`. Operation 0 takes `[handle, branch, heap]` and exposes the four-word
LSF header at `heap`, with the state unchanged. Its pointers may refer to
cells owned by the data structure, as allowed by `DSRep`.

The graph and name capacities are parameters of this contract family.
Numeric tables are zero outside the graph's active edge set. The numeric
cost multiplier and allocation bounds are parameters of the implementation.
No correctness property of the builder is made a field of its state.
The runtime interface also passes the limb count and precision in the
initialization words and requires enough capacity for the stretch grid.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM DynSpanner.Program Chain

/-- Decode the active fixed-point entries, with zero extension off the graph. -/
noncomputable def readEdgeValues (mem : ℕ → ℕ) (a h L P : ℕ) (E : Finset ℕ) : ℕ → ℝ :=
  fun e => if e ∈ E then Num.fixVal mem (a + e * L) h L P else 0

/-- Machine interface for the static last-level tool (Definition 5.8,
pages 19–20). The time multiplier accounts for multiword arithmetic.
The readout operation writes four pointers, rather than copying forests. -/
noncomputable def lastLevelMachineContract {w : ℕ} (fmt : Num.Format w) (L : ℕ)
    (tool : LastLevelTool) (G : MGraph) (vCap eCap multiplier : ℕ)
    (allocation : ℕ → List ℕ → ℕ) : DataStructure (ℕ × (ℕ → LSF)) where
  initPre args mem := ∃ graph lengths heap,
    args = [graph, lengths, heap] ∧
    DynGraphAt mem graph vCap eCap G ∧
    graph + dynGraphSize vCap eCap ≤ heap ∧ lengths + eCap * L ≤ heap ∧
    (∀ e ∈ G.E, Num.Valid mem (lengths + e * L) fmt.limbBits L) ∧
    ∀ e ∈ G.E, 0 < readEdgeValues mem lengths fmt.limbBits L fmt.precision G.E e
  initPost args mem s mem' :=
    s = tool.build G
      (readEdgeValues mem (args.getD 1 0) fmt.limbBits L fmt.precision G.E) ∧
    LSFCollectionAt mem' (heapArg args) vCap eCap fmt.limbBits L fmt.precision G.E s
  initCost _ _ := multiplier * (tool.cost G + 1)
  initSpace args _ := allocation 1 args
  pre i s args _ := i = 0 ∧ ∃ handle branch heap,
    args = [handle, branch, heap] ∧ branch < s.1
  post i s args _ s' mem' := i = 0 ∧ s' = s ∧
    LSFAt mem' (heapArg args) vCap eCap fmt.limbBits L fmt.precision G.E
      (s.2 (args.getD 1 0))
  cost _ _ _ _ := 64
  space _ _ _ _ := 4

/-- A path uses at most the sum of the live edge lengths. The extra two
units cover the additive one in tree stretch and upward rounding. -/
noncomputable def lastLevelStretchBound (G : MGraph) (length : ℕ → ℝ) (e : ℕ) : ℝ :=
  2 + (∑ f ∈ G.E, length f) / length e

/-- The runtime initialization interface for Definition 5.8 (pages 19–20).
The limb count and memory precision are argument words. The stretch grid
precision belongs to the graph and the tool. The caller uses four-bit
limbs and its precision fits the limb budget. Each live edge has enough
signed block capacity for its upward-rounded stretch. -/
noncomputable def lastLevelRuntimeMachineContract {w : ℕ} (fmt : Num.Format w) (L : ℕ)
    (tool : LastLevelTool) (G : MGraph) (vCap eCap multiplier stretchPrecision : ℕ)
    (allocation : ℕ → List ℕ → ℕ) : DataStructure (ℕ × (ℕ → LSF)) :=
  { lastLevelMachineContract fmt L tool G vCap eCap multiplier allocation with
    initPre := fun args mem => ∃ graph lengths heap,
      args = [graph, lengths, L, fmt.precision, heap] ∧ fmt.limbBits = 4 ∧ fmt.precision ≤ 4 * L ∧
      (lastLevelMachineContract fmt L tool G vCap eCap multiplier allocation).initPre
        [graph, lengths, heap] mem ∧
      let length := readEdgeValues mem lengths fmt.limbBits L fmt.precision G.E
      ∀ e ∈ G.E, 2 * (2 : ℝ)^stretchPrecision * lastLevelStretchBound G length e <
        Num.capacity fmt.limbBits L }

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM DynSpanner.Program Chain

/-- Decoding a valid table gives its represented values on all active edges. -/
theorem readEdgeValues_eq {mem : ℕ → ℕ} {a h L P : ℕ} {E : Finset ℕ}
    {values : ℕ → ℝ} (hv : EdgeValuesAt mem a h L P E values) {e : ℕ} (he : e ∈ E) :
    readEdgeValues mem a h L P E e = values e := by
  simp only [readEdgeValues, he, ↓reduceIte]
  exact (hv e he).2

/-- A live-edge table decodes the exact total model function when
the model uses zero outside its active edge domain. -/
theorem readEdgeValues_eq_of_support {mem : ℕ → ℕ} {a h L P : ℕ} {E : Finset ℕ}
    {values : ℕ → ℝ} (hv : EdgeValuesAt mem a h L P E values)
    (hz : ∀ e ∉ E, values e = 0) :
    readEdgeValues mem a h L P E = values := by
  funext e
  by_cases he : e ∈ E
  · exact readEdgeValues_eq hv he
  · simp only [readEdgeValues, he, ite_false, hz e he]

/-- A live-edge table recovers a total input function exactly if its
off-graph values agree with the decoder's zero extension. -/
theorem readEdgeValues_eq_iff_support {mem : ℕ → ℕ} {a h L P : ℕ}
    {E : Finset ℕ} {values : ℕ → ℝ} (hv : EdgeValuesAt mem a h L P E values) :
    readEdgeValues mem a h L P E = values ↔ ∀ e ∉ E, values e = 0 := by
  refine ⟨?_, readEdgeValues_eq_of_support hv⟩
  intro heq e he
  simpa [readEdgeValues, he] using (congrFun heq e).symm

/-- Initialization creates precisely the model builder's state. -/
theorem lastLevelMachineContract_init_state {w : ℕ} {fmt : Num.Format w}
    {L : ℕ} {tool : LastLevelTool} {G : MGraph} {vCap eCap multiplier : ℕ}
    {allocation : ℕ → List ℕ → ℕ} {args : List ℕ} {mem mem' : ℕ → ℕ}
    {s : ℕ × (ℕ → LSF)}
    (hs : (lastLevelMachineContract fmt L tool G vCap eCap multiplier allocation).initPost
      args mem s mem') :
    s = tool.build G
      (readEdgeValues mem (args.getD 1 0) fmt.limbBits L fmt.precision G.E) := hs.1

/-- Exposing an LSF leaves the model state unchanged. -/
theorem lastLevelMachineContract_readout_state {w : ℕ} {fmt : Num.Format w}
    {L : ℕ} {tool : LastLevelTool} {G : MGraph} {vCap eCap multiplier : ℕ}
    {allocation : ℕ → List ℕ → ℕ} {args : List ℕ} {mem mem' : ℕ → ℕ}
    {i : ℕ} {s s' : ℕ × (ℕ → LSF)}
    (hs : (lastLevelMachineContract fmt L tool G vCap eCap multiplier allocation).post
      i s args mem s' mem') : s' = s := hs.2.1

/-- The initialization budget has the model's quadratic last-level bound,
with the supplied numeric multiplier and one unit for call overhead.
This is a bound on the contract budget. A program must still prove
`DSRep.Implements` to turn it into a bound on runs. -/
theorem lastLevelMachineContract_initCost_le {w : ℕ} (fmt : Num.Format w)
    (L : ℕ) (tool : LastLevelTool) (G : MGraph) (vCap eCap multiplier : ℕ)
    (allocation : ℕ → List ℕ → ℕ) (params : LastLevelParams)
    (hTool : tool.IsSpec params) (lengths : ℕ → ℝ) (hG : G.IsValid)
    (hLengths : ∀ e ∈ G.E, 0 < lengths e) (args : List ℕ) (mem : ℕ → ℕ) :
    (((lastLevelMachineContract fmt L tool G vCap eCap multiplier allocation).initCost
      args mem : ℕ) : ℝ) ≤
      (multiplier : ℝ) * (params.c_last * ((G.m : ℝ) + 1) ^ 2 *
        (Real.log ((G.m : ℝ) + (G.n : ℝ) + 2)) ^ params.p_last + 1) := by
  have hCost := (hTool G lengths hG hLengths).2.2.2.2
  change ((multiplier * (tool.cost G + 1) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  exact mul_le_mul_of_nonneg_left (add_le_add hCost (le_refl 1)) (Nat.cast_nonneg multiplier)

end MinCostFlow.MinRatio
