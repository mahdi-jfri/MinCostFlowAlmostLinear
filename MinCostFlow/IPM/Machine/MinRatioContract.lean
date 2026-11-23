module

public import MinCostFlow.IPM.Machine.Layout

/-!
# Machine contract for Definition 4.5 with failure

Definition 4.5 (page 14), with the recorded failure correction to
Theorem 4.6 (page 15), is exposed as a `WordRAM.DataStructure`.
The abstract state is exactly the state of a model implementation.
This specialization is for the IPM's fixed graph: batches refresh
coefficients by deleting and reinserting edges with their original ends.
It does not restrict the graph updates used internally by Theorem 5.1.

Initialization takes `[graph,gradient,length,L,P,heap]`. Operation 0 is
Update `[handle,batch,gradient,length,eta,heap]`, operation 1 is
Query `[handle,edge,heap]`, and operation 2 is Detect `[handle,heap]`.
Init carries the block width and scale. They are fixed for the lifetime of a structure.
Update writes a success bit at the old heap, followed by a `2L`-limb
actual normalization at precision `2P`. The requested normalization
and the gradient, length and flow blocks use `L` limbs at precision `P`.
The doubled scale represents an exact gradient--increment product. Query writes one scalar there. Detect writes the
count-prefixed list of `Layout`. No circulation vector is materialized:
as in the paper, Update applies it within the structure.

Only the scalar normalization is rounded. The actual normalization is
between half and twice the requested one. The resulting increment is
an exact common multiple of a circulation, so rounding preserves routing.
The later admissibility proof must combine this interval with the
stored-residual error before applying Lemma 9.3. Coordinatewise rounding
of unrelated edge increments is not allowed by this contract.

Update also records how the IPM calls it. The state was just returned by a
Detect on a state reached by a valid history, and the gradient and length
arrays agree with that history outside the edges the batch inserts
(`MinRatioDetectedWith`). So no Update follows another one without a Detect,
and an implementation needs to read only the entries of the batch. A batch
has at most `2 * m` entries, one deletion and one insertion per edge.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Formats are shared with the numerics of `MinCostFlow.Num`. The stronger carry margin is
needed by division. The caller selects the precision and the range. -/
structure MinRatioFormat (w : ℕ) where
  fmt : Num.Format w
  limbs : ℕ
  rangeExponent : ℕ
  divide_fits : 3*fmt.limbBits+2 ≤ w
  width : fmt.precision+5*rangeExponent+30 ≤ fmt.limbBits*limbs
  parameters_fit : limbs < 2^w ∧ fmt.precision < 2^w ∧ rangeExponent < 2^w

/-- A scalar has a fitting fixed-point encoding. This is a representation
predicate, not a numerical approximation or correctness assertion. -/
def ScalarFits (h L P : ℕ) (x : ℝ) : Prop :=
  ∃ z : ℤ, Num.Fits h L z ∧ x = (z : ℝ)/(2 : ℝ)^P

/-- All coordinates exposed by Query fit the selected format. -/
def MinRatioStateFits (A : MinRatioDataStructureWithFailure) (G : MGraph) (h L P : ℕ)
    (s : A.State) : Prop := ∀ e ∈ G.E, ScalarFits h L P (A.query s e)

/-- A coefficient refresh on the fixed IPM graph uses only deletion and
reinsertion at the original ends. Vertex splitting belongs inside the DS. -/
def RefreshBatch (G : MGraph) (U : List MinCostFlow.Update) : Prop :=
  G.BatchIsValid U ∧ G.applyBatch U = G ∧
    ∀ u ∈ U, match u with
      | .delete e => e ∈ G.E
      | .insert e v w => e ∈ G.E ∧ v = G.tail e ∧ w = G.head e
      | .split _ _ _ _ => False

/-- Update's actual normalization may vary by a factor two in either
 direction. The increment itself must be exact for that normalization. -/
def NormalizationWithin (requested actual : ℝ) : Prop :=
  requested/2 ≤ actual ∧ actual ≤ 2*requested

/-- The output header bit says exactly whether the model Update succeeded. -/
def AnswerAt (mem : ℕ → ℕ) (a : ℕ) (answer : Option (ℕ → ℝ)) : Prop :=
  mem a = if answer.isSome then 1 else 0

/-- The state `s` is reached by a valid history of Definition 4.5 (page 14) on the
graph `G` in at most `2 * G.m` stages, and the vectors `g` and `l` are the history's
current gradient and lengths on the edges of `G`. -/
def MinRatioReachedWith (A : MinRatioDataStructureWithFailure) (G : MGraph)
    (s : A.State) (g l : ℕ → ℝ) : Prop :=
  ∃ (D : DynamicInstance) (η : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ),
    MinRatioHistoryValid D op T ∧ D.G T = G ∧ s = minRatioState A.eraseFailure D η op T ∧
    (∀ e ∈ G.E, g e = D.g T e ∧ l e = D.ℓ T e) ∧
    T ≤ 2 * G.m

/-- The state `s` is the one returned by a Detect from a state reached with
gradient `g₀` and lengths `l₀`, and the vectors `g` and `l` keep those values on
every edge of `G` that is not `changed`. The IPM calls Update only in this
situation: Detect comes first in each iteration, and only the returned edges get
new coefficients. -/
def MinRatioDetectedWith (A : MinRatioDataStructureWithFailure) (G : MGraph)
    (s : A.State) (changed : ℕ → Prop) (g l : ℕ → ℝ) : Prop :=
  ∃ (s₀ : A.State) (g₀ l₀ : ℕ → ℝ), MinRatioReachedWith A G s₀ g₀ l₀ ∧
    s = (A.detect s₀).2 ∧ ∀ e ∈ G.E, ¬ changed e → g e = g₀ e ∧ l e = l₀ e

/-- The state passed to Update is a Detect output. -/
theorem MinRatioDetectedWith.detected {A : MinRatioDataStructureWithFailure} {G : MGraph}
    {s : A.State} {changed : ℕ → Prop} {g l : ℕ → ℝ}
    (h : MinRatioDetectedWith A G s changed g l) : ∃ s₀, s = (A.detect s₀).2 := by
  obtain ⟨s₀, _, _, _, hs, _⟩ := h
  exact ⟨s₀, hs⟩

/-- The state passed to Update is the Detect output of a state reached by a valid history
in at most `2 * G.m` stages. -/
theorem MinRatioDetectedWith.stages_le {A : MinRatioDataStructureWithFailure} {G : MGraph}
    {s : A.State} {changed : ℕ → Prop} {g l : ℕ → ℝ}
    (h : MinRatioDetectedWith A G s changed g l) :
    ∃ (D : DynamicInstance) (η : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ),
      MinRatioHistoryValid D op T ∧ D.G T = G ∧
      s = (A.detect (minRatioState A.eraseFailure D η op T)).2 ∧ T ≤ 2 * G.m := by
  obtain ⟨s₀, _, _, ⟨D, η, op, T, hV, hG, hs₀, _, hT⟩, hs, _⟩ := h
  exact ⟨D, η, op, T, hV, hG, hs₀ ▸ hs, hT⟩

/-- Allowing more edges to change keeps the condition. -/
theorem MinRatioDetectedWith.mono {A : MinRatioDataStructureWithFailure} {G : MGraph}
    {s : A.State} {changed changed' : ℕ → Prop} {g l : ℕ → ℝ}
    (h : MinRatioDetectedWith A G s changed g l) (himp : ∀ e ∈ G.E, changed e → changed' e) :
    MinRatioDetectedWith A G s changed' g l := by
  obtain ⟨s₀, g₀, l₀, hr, hs, hagree⟩ := h
  exact ⟨s₀, g₀, l₀, hr, hs, fun e he hn => hagree e he (fun hc => hn (himp e he hc))⟩

/-- The condition depends on the vectors only at the edges of `G`. -/
theorem MinRatioDetectedWith.congr {A : MinRatioDataStructureWithFailure} {G : MGraph}
    {s : A.State} {changed : ℕ → Prop} {g l g' l' : ℕ → ℝ}
    (h : MinRatioDetectedWith A G s changed g l)
    (hg : ∀ e ∈ G.E, g' e = g e) (hl : ∀ e ∈ G.E, l' e = l e) :
    MinRatioDetectedWith A G s changed g' l' := by
  obtain ⟨s₀, g₀, l₀, hr, hs, hagree⟩ := h
  refine ⟨s₀, g₀, l₀, hr, hs, fun e he hn => ?_⟩
  rw [hg e he, hl e he]
  exact hagree e he hn

/-- A Detect from a reached state, with vectors that agree with the reached ones
outside `changed`, gives the Update condition. -/
theorem MinRatioReachedWith.detectedWith {A : MinRatioDataStructureWithFailure} {G : MGraph}
    {s : A.State} {g₀ l₀ g l : ℕ → ℝ} {changed : ℕ → Prop}
    (h : MinRatioReachedWith A G s g₀ l₀)
    (hagree : ∀ e ∈ G.E, ¬ changed e → g e = g₀ e ∧ l e = l₀ e) :
    MinRatioDetectedWith A G (A.detect s).2 changed g l :=
  ⟨s, g₀, l₀, h, rfl, hagree⟩

/-- The initial state is reached by the history that never changes. -/
theorem minRatioReachedWith_init (A : MinRatioDataStructureWithFailure) (G : MGraph)
    (g l : ℕ → ℝ) (hG : G.IsValid) (hl : ∀ e ∈ G.E, 0 < l e) :
    MinRatioReachedWith A G (A.init G g l) g l := by
  refine ⟨⟨fun _ => G, fun _ => [], fun _ => g, fun _ => l⟩, fun _ => 0, fun _ => false, 0,
    ⟨?_, ?_, ?_, ?_⟩, rfl, rfl, fun _ _ => ⟨rfl, rfl⟩, Nat.zero_le _⟩
  · intro t ht ht'
    omega
  · intro t _
    exact ⟨hG, hl⟩
  · intro t ht ht' _
    omega
  · intro t ht ht' _ _ _
    omega

/-- Default 6-argument Init precondition (`[graph, g, l, F.limbs, F.fmt.precision, heap]`). -/
def minRatioInitPre {w : ℕ} (F : MinRatioFormat w) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ graph g l heap,
    args = [graph,g,l,F.limbs,F.fmt.precision,heap] ∧ (2 : ℝ)^(-(F.rangeExponent : ℤ)) ≤ κ*α ∧
    5*F.rangeExponent+Nat.size m+30 ≤ F.fmt.precision ∧ GraphAt mem graph G ∧ (∀ x ∈ graphWords G, x < 2^w) ∧ G.IsValid ∧
    (∀ e ∈ G.E, e < m) ∧ graph+(graphWords G).length ≤ heap ∧
    g+m*F.limbs ≤ heap ∧ l+m*F.limbs ≤ heap ∧
    (∀ e < m, Num.Valid mem (g+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (l+e*F.limbs) F.fmt.limbBits F.limbs) ∧
    (∀ e ∈ G.E, 0 < readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m e) ∧
    LengthsWithin G F.rangeExponent (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m)

/-- Parametric 7-argument Init precondition passing `V` (`[graph, g, l, F.limbs, F.fmt.precision, V, heap]`). -/
def minRatioInitPreWithV {w : ℕ} (F : MinRatioFormat w) (G : MGraph) (m V : ℕ) (κ α : ℝ)
    (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ graph g l heap,
    args = [graph,g,l,F.limbs,F.fmt.precision,V,heap] ∧ args.getD 5 0 = V ∧
    (2 : ℝ)^(-(F.rangeExponent : ℤ)) ≤ κ*α ∧
    5*F.rangeExponent+Nat.size m+30 ≤ F.fmt.precision ∧ GraphAt mem graph G ∧ (∀ x ∈ graphWords G, x < 2^w) ∧ G.IsValid ∧
    (∀ e ∈ G.E, e < m) ∧ graph+(graphWords G).length ≤ heap ∧
    g+m*F.limbs ≤ heap ∧ l+m*F.limbs ≤ heap ∧
    (∀ e < m, Num.Valid mem (g+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (l+e*F.limbs) F.fmt.limbBits F.limbs) ∧
    (∀ e ∈ G.E, 0 < readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m e) ∧
    LengthsWithin G F.rangeExponent (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m) ∧
    (∀ e ∈ G.E, |readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m e| ≤ (2 : ℝ)^F.rangeExponent)

/-- Shared min-ratio contract parameterized by its Init precondition so operation proofs
apply uniformly to both the 6-argument and `V`-passing Init interfaces. -/
def minRatioMachineContractAt {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (initPre : List ℕ → (ℕ → ℕ) → Prop) : DataStructure A.State where
  initPre := initPre
  initPost args mem s _ :=
    s = A.init G
      (readVector mem (args.getD 1 0) F.fmt.limbBits F.limbs F.fmt.precision m)
      (readVector mem (args.getD 2 0) F.fmt.limbBits F.limbs F.fmt.precision m) ∧
    MinRatioStateFits A G F.fmt.limbBits F.limbs F.fmt.precision s
  initCost _ _ := rate m*(m+1)
  initSpace args _ := allocation 3 args
  pre i s args mem :=
    MinRatioStateFits A G F.fmt.limbBits F.limbs F.fmt.precision s ∧
    match i with
    | 0 => ∃ handle batch g l eta heap U,
        args = [handle,batch,g,l,eta,heap] ∧
        (2 : ℝ)^(-(F.rangeExponent : ℤ)) ≤ κ*α ∧
        5*F.rangeExponent+Nat.size m+30 ≤ F.fmt.precision ∧
        (∀ e ∈ G.E, |A.query s e| ≤ (2 : ℝ)^F.rangeExponent) ∧ BatchAt mem batch U ∧ (∀ x ∈ batchWords U, x < 2^w) ∧ RefreshBatch G U ∧
        batch+(batchWords U).length ≤ heap ∧ g+m*F.limbs ≤ heap ∧ l+m*F.limbs ≤ heap ∧
        eta+F.limbs ≤ heap ∧ Num.Valid mem eta F.fmt.limbBits F.limbs ∧
        (2 : ℝ)^(-(F.rangeExponent : ℤ)) ≤
          Num.fixVal mem eta F.fmt.limbBits F.limbs F.fmt.precision ∧
        Num.fixVal mem eta F.fmt.limbBits F.limbs F.fmt.precision ≤ (2 : ℝ)^F.rangeExponent ∧
        (∀ e < m, Num.Valid mem (g+e*F.limbs) F.fmt.limbBits F.limbs ∧
          Num.Valid mem (l+e*F.limbs) F.fmt.limbBits F.limbs) ∧
        (∀ e ∈ G.E,
          |readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m e| ≤ (2 : ℝ)^F.rangeExponent ∧
          (2 : ℝ)^(-(F.rangeExponent : ℤ)) ≤
            readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m e ∧
          readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m e ≤ (2 : ℝ)^F.rangeExponent) ∧
        U.length ≤ 2*m ∧
        MinRatioDetectedWith A G s (fun e => ∃ u ∈ U, u.Inserts e)
          (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
          (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m)
    | 1 => ∃ handle e heap, args = [handle,e,heap] ∧ e ∈ G.E ∧ e < m
    | 2 => ∃ handle heap, args = [handle,heap]
    | _ => False
  post i s args mem s' mem' :=
    match i with
    | 0 => ∃ actual,
        ScalarAt mem' (heapArg args+1) F.fmt.limbBits (2*F.limbs) (2*F.fmt.precision) actual ∧
        NormalizationWithin
          (Num.fixVal mem (args.getD 4 0) F.fmt.limbBits F.limbs F.fmt.precision) actual ∧
        MinRatioStateFits A G F.fmt.limbBits F.limbs F.fmt.precision s' ∧
        ∀ U, BatchAt mem (args.getD 1 0) U →
          let result := A.update s U
            (readVector mem (args.getD 2 0) F.fmt.limbBits F.limbs F.fmt.precision m)
            (readVector mem (args.getD 3 0) F.fmt.limbBits F.limbs F.fmt.precision m) actual
          s' = result.1 ∧ AnswerAt mem' (heapArg args) result.2
    | 1 => s' = s ∧ ScalarAt mem' (heapArg args) F.fmt.limbBits F.limbs F.fmt.precision
        (A.query s (args.getD 1 0))
    | 2 => s' = (A.detect s).2 ∧ DetectAt mem' (heapArg args) (A.detect s).1 ∧
        MinRatioStateFits A G F.fmt.limbBits F.limbs F.fmt.precision s'
    | _ => False
  cost i s args mem := rate m * match i with
    | 0 => 1+mem (args.getD 1 0)
    | 1 => 1
    | 2 => 1+(A.detect s).1.card
    | _ => 0
  space i _ args _ := allocation i args

/-- Machine specification of the IPM's fixed-graph use of Definition 4.5.
`rate m` is the amortized per-update/query/output rate of Theorem 5.1;
initialization costs `rate m*(m+1)`. The space function is supplied by
its implementation and is independent of its time bound. Model
correctness is separately `MinRatioSpecWithFailure A ...`.

A successful Update must leave representable flow coordinates, including
when the input has no hidden witness. Failure changes no flow according
to the model contract and terminates this target test. The postcondition
uses the actual normalization returned in the header, not the requested
normalization as an exact-real substitute for the machine computation. -/
def minRatioMachineContract {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) : DataStructure A.State where
  initPre args mem :=
    ∃ graph g l heap,
      args = [graph,g,l,F.limbs,F.fmt.precision,heap] ∧ (2 : ℝ)^(-(F.rangeExponent : ℤ)) ≤ κ*α ∧
      5*F.rangeExponent+Nat.size m+30 ≤ F.fmt.precision ∧ GraphAt mem graph G ∧ (∀ x ∈ graphWords G, x < 2^w) ∧ G.IsValid ∧
      (∀ e ∈ G.E, e < m) ∧ graph+(graphWords G).length ≤ heap ∧
      g+m*F.limbs ≤ heap ∧ l+m*F.limbs ≤ heap ∧
      (∀ e < m, Num.Valid mem (g+e*F.limbs) F.fmt.limbBits F.limbs ∧
        Num.Valid mem (l+e*F.limbs) F.fmt.limbBits F.limbs) ∧
      (∀ e ∈ G.E, 0 < readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m e) ∧
      LengthsWithin G F.rangeExponent (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m)
  initPost args mem s _ :=
    s = A.init G
      (readVector mem (args.getD 1 0) F.fmt.limbBits F.limbs F.fmt.precision m)
      (readVector mem (args.getD 2 0) F.fmt.limbBits F.limbs F.fmt.precision m) ∧
    MinRatioStateFits A G F.fmt.limbBits F.limbs F.fmt.precision s
  initCost _ _ := rate m*(m+1)
  initSpace args _ := allocation 3 args
  pre i s args mem :=
    MinRatioStateFits A G F.fmt.limbBits F.limbs F.fmt.precision s ∧
    match i with
    | 0 => ∃ handle batch g l eta heap U,
        args = [handle,batch,g,l,eta,heap] ∧
        (2 : ℝ)^(-(F.rangeExponent : ℤ)) ≤ κ*α ∧
        5*F.rangeExponent+Nat.size m+30 ≤ F.fmt.precision ∧
        (∀ e ∈ G.E, |A.query s e| ≤ (2 : ℝ)^F.rangeExponent) ∧ BatchAt mem batch U ∧ (∀ x ∈ batchWords U, x < 2^w) ∧ RefreshBatch G U ∧
        batch+(batchWords U).length ≤ heap ∧ g+m*F.limbs ≤ heap ∧ l+m*F.limbs ≤ heap ∧
        eta+F.limbs ≤ heap ∧ Num.Valid mem eta F.fmt.limbBits F.limbs ∧
        (2 : ℝ)^(-(F.rangeExponent : ℤ)) ≤
          Num.fixVal mem eta F.fmt.limbBits F.limbs F.fmt.precision ∧
        Num.fixVal mem eta F.fmt.limbBits F.limbs F.fmt.precision ≤ (2 : ℝ)^F.rangeExponent ∧
        (∀ e < m, Num.Valid mem (g+e*F.limbs) F.fmt.limbBits F.limbs ∧
          Num.Valid mem (l+e*F.limbs) F.fmt.limbBits F.limbs) ∧
        (∀ e ∈ G.E,
          |readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m e| ≤ (2 : ℝ)^F.rangeExponent ∧
          (2 : ℝ)^(-(F.rangeExponent : ℤ)) ≤
            readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m e ∧
          readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m e ≤ (2 : ℝ)^F.rangeExponent) ∧
        U.length ≤ 2*m ∧
        MinRatioDetectedWith A G s (fun e => ∃ u ∈ U, u.Inserts e)
          (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
          (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m)
    | 1 => ∃ handle e heap, args = [handle,e,heap] ∧ e ∈ G.E ∧ e < m
    | 2 => ∃ handle heap, args = [handle,heap]
    | _ => False
  post i s args mem s' mem' :=
    match i with
    | 0 => ∃ actual,
        ScalarAt mem' (heapArg args+1) F.fmt.limbBits (2*F.limbs) (2*F.fmt.precision) actual ∧
        NormalizationWithin
          (Num.fixVal mem (args.getD 4 0) F.fmt.limbBits F.limbs F.fmt.precision) actual ∧
        MinRatioStateFits A G F.fmt.limbBits F.limbs F.fmt.precision s' ∧
        ∀ U, BatchAt mem (args.getD 1 0) U →
          let result := A.update s U
            (readVector mem (args.getD 2 0) F.fmt.limbBits F.limbs F.fmt.precision m)
            (readVector mem (args.getD 3 0) F.fmt.limbBits F.limbs F.fmt.precision m) actual
          s' = result.1 ∧ AnswerAt mem' (heapArg args) result.2
    | 1 => s' = s ∧ ScalarAt mem' (heapArg args) F.fmt.limbBits F.limbs F.fmt.precision
        (A.query s (args.getD 1 0))
    | 2 => s' = (A.detect s).2 ∧ DetectAt mem' (heapArg args) (A.detect s).1 ∧
        MinRatioStateFits A G F.fmt.limbBits F.limbs F.fmt.precision s'
    | _ => False
  cost i s args mem := rate m * match i with
    | 0 => 1+mem (args.getD 1 0)
    | 1 => 1
    | 2 => 1+(A.detect s).1.card
    | _ => 0
  space i _ args _ := allocation i args

theorem minRatioMachineContract_eq_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) :
    minRatioMachineContract F A G m κ α rate allocation =
      minRatioMachineContractAt F A G m κ α rate allocation (minRatioInitPre F G m κ α) :=
  rfl

/-- Version of `minRatioMachineContract` that passes `V` as the 6th Init argument:
`[graph, g, l, F.limbs, F.fmt.precision, V, heap]` with `args.getD 5 0 = V`. -/
def minRatioMachineContractWithV {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m V : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) : DataStructure A.State :=
  minRatioMachineContractAt F A G m κ α rate allocation (minRatioInitPreWithV F G m V κ α)

theorem minRatioMachineContractWithV_eq_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m V : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) :
    minRatioMachineContractWithV F A G m V κ α rate allocation =
      minRatioMachineContractAt F A G m κ α rate allocation
        (minRatioInitPreWithV F G m V κ α) :=
  rfl

theorem minRatioMachineContractWithV_arg5 {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m V : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    {args : List ℕ} {mem : ℕ → ℕ}
    (hpre : (minRatioMachineContractWithV F A G m V κ α rate allocation).initPre args mem) :
    args.getD 5 0 = V := by
  obtain ⟨_, _, _, _, _, h5, _⟩ := hpre
  exact h5

/-- Every successful machine Query produces a dyadic coordinate. Thus
fixed-point representation follows from the output layout, not from a
rationality hypothesis about arbitrary real model outputs. -/
theorem minRatioMachine_query_dyadic {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (s s' : A.State) (args : List ℕ) (mem mem' : ℕ → ℕ)
    (hq : (minRatioMachineContract F A G m κ α rate allocation).post 1 s args mem s' mem') :
    ∃ z : ℤ, A.query s (args.getD 1 0) = (z : ℝ)/(2 : ℝ)^F.fmt.precision :=
  hq.2.exists_dyadic

/-- The Update charge is linear in the input batch count, plus one call.
Theorem 5.1 supplies the subpolynomial rate; no such algorithm is assumed
as a new cited result. -/
theorem minRatioMachine_update_cost {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (s : A.State) (args : List ℕ) (mem : ℕ → ℕ) (U : List MinCostFlow.Update)
    (hu : BatchAt mem (args.getD 1 0) U) :
    (minRatioMachineContract F A G m κ α rate allocation).cost 0 s args mem = rate m*(1+U.length) := by
  have hc := hu 0 (by simp [batchWords])
  simp only [batchWords, List.getElem_cons_zero, Nat.add_zero] at hc
  change rate m*(1+mem (args.getD 1 0)) = _
  rw [hc]

end MinCostFlow.IPM.Machine
