module

public import MinCostFlow.Basic.Hidden
public import MinCostFlow.Basic.Forest
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# The dynamic min-ratio cycle interface

Definition 4.5 (page 14) of arXiv:2309.16629v1 asks for a data structure
with Update, Query, and Detect. Update returns a circulation of ratio at
most `-κα` whenever the instance prefix has the hidden stability property
of Definition 4.4. It adds `-η Δ / ⟨g, Δ⟩` to the maintained flow.
Query reads that flow. Detect returns exactly the edges whose accumulated
absolute flow changes since their last report exceed its threshold.

The implementation state is abstract. An execution interleaves updates
and detections, and queries are pure reads of any execution state.
A detection adds an unchanged instance stage. The history contains only
past inputs, so no operation can inspect a future instance or a hidden
witness. In Detect, the update vector means the actual scaled flow
increment, as in the scaled vector of Chen et al., arXiv:2203.00671v2,
Algorithm 7 (Section 9, page 69). Off-graph coordinates are extended by
zero for each increment. No running-time assertion is part of this spec.

The extended interface `MinRatioSpecWithFailure` implements the restated
Definition 4.5: Update may fail only on a non-hidden prefix, in which case
it adds no flow and the IPM terminates that target test. The never-failing
interface remains available as the mathematical projection used by the
epoch proofs.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM

/-- The operations of Definition 4.5 (page 14). The state after an Update
is returned together with its chosen, unscaled circulation. -/
structure MinRatioDataStructure where
  State : Type
  init : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → State
  update : State → List MinCostFlow.Update → (ℕ → ℝ) → (ℕ → ℝ) → ℝ → State × (ℕ → ℝ)
  query : State → ℕ → ℝ
  detect : State → Finset ℕ × State

/-- Valid input history for Definition 4.5. A true schedule entry is an
Update. A false entry is Detect, which leaves the dynamic instance
unchanged. Only explicitly inserted edges receive new gradients and
lengths, so an edge-value change is represented by deletion and insertion. -/
def MinRatioHistoryValid (D : DynamicInstance) (isUpdate : ℕ → Bool) (T : ℕ) : Prop :=
  D.IsValid T ∧
  (∀ t ≤ T, (D.G t).IsValid ∧ ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) ∧
  (∀ t, 1 ≤ t → t ≤ T → isUpdate t = false →
    D.U t = [] ∧ D.g t = D.g (t-1) ∧ D.ℓ t = D.ℓ (t-1)) ∧
  (∀ t, 1 ≤ t → t ≤ T → ∀ e ∈ (D.G t).E,
    D.NotInsertedBetween e (t-1) t →
      D.g t e = D.g (t-1) e ∧ D.ℓ t e = D.ℓ (t-1) e)

/-- Every shorter prefix of a valid operation history is valid. -/
theorem MinRatioHistoryValid.mono (D : DynamicInstance) (op : ℕ → Bool) (T S : ℕ)
    (h : MinRatioHistoryValid D op T) (hST : S ≤ T) : MinRatioHistoryValid D op S := by
  exact ⟨fun t ht ht' => h.1 t ht (ht'.trans hST),
    fun t ht => h.2.1 t (ht.trans hST),
    fun t ht ht' hop => h.2.2.1 t ht (ht'.trans hST) hop,
    fun t ht ht' e he hnot => h.2.2.2 t ht (ht'.trans hST) e he hnot⟩

/-- State reached after a prefix of Update and Detect operations. -/
def minRatioState (A : MinRatioDataStructure) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) : ℕ → A.State
  | 0 => A.init (D.G 0) (D.g 0) (D.ℓ 0)
  | t+1 => if isUpdate (t+1) then
      (A.update (minRatioState A D η isUpdate t) (D.U (t+1))
        (D.g (t+1)) (D.ℓ (t+1)) (η (t+1))).1
    else (A.detect (minRatioState A D η isUpdate t)).2

/-- The unscaled circulation returned by an Update at stage `t+1`. -/
def minRatioDirection (A : MinRatioDataStructure) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (t : ℕ) : ℕ → ℝ :=
  (A.update (minRatioState A D η isUpdate t) (D.U (t+1))
    (D.g (t+1)) (D.ℓ (t+1)) (η (t+1))).2

/-- Actual scaled flow increment: the minus sign is the one in
Definition 4.5, Update (page 14). Detect stages have zero increment. -/
def minRatioIncrement (A : MinRatioDataStructure) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | t+1, e => if isUpdate (t+1) ∧ e ∈ (D.G (t+1)).E then
      -(η (t+1) / (D.G (t+1)).inner (D.g (t+1)) (minRatioDirection A D η isUpdate t)) *
        minRatioDirection A D η isUpdate t e
    else 0

/-- Flow initialized at zero and updated by the scaled increments. -/
def minRatioFlow (A : MinRatioDataStructure) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (t e : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (t+1), minRatioIncrement A D η isUpdate s e

/-- The last Detect stage at which an edge was returned, or zero when
there has been no such stage. This is `last_e` in Definition 4.5. -/
def minRatioLast (A : MinRatioDataStructure) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | t+1, e => if isUpdate (t+1) = false ∧
      e ∈ (A.detect (minRatioState A D η isUpdate t)).1 then t+1
    else minRatioLast A D η isUpdate t e

/-- Definition 4.5's exact Detect output (page 14), using the current
length and the absolute actual flow increments since the last report. -/
def minRatioDetectSet (A : MinRatioDataStructure) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (ε : ℝ) (t : ℕ) : Finset ℕ :=
  (D.G (t+1)).E.filter fun e => ε ≤ D.ℓ (t+1) e *
    ∑ s ∈ Finset.Ioc (minRatioLast A D η isUpdate t e) (t+1),
      |minRatioIncrement A D η isUpdate s e|

/-- The Query, Update and Detect guarantees of Definition 4.5 (page 14)
for one prefix of a valid history. -/
def MinRatioSpecOn (A : MinRatioDataStructure) (κ α Ψ ε : ℝ)
    (D : DynamicInstance) (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (T : ℕ) : Prop :=
    (∀ t ≤ T, ∀ e ∈ (D.G t).E,
      A.query (minRatioState A D η isUpdate t) e = minRatioFlow A D η isUpdate t e) ∧
    (∀ t, t+1 ≤ T → isUpdate (t+1) = true →
      (D.G (t+1)).IsCirculation (minRatioDirection A D η isUpdate t) ∧
      (D.HiddenStable (t+1) α Ψ →
        (D.G (t+1)).inner (D.g (t+1)) (minRatioDirection A D η isUpdate t) /
          (D.G (t+1)).lnorm (D.ℓ (t+1)) (minRatioDirection A D η isUpdate t) ≤ -κ*α)) ∧
    (∀ t, t+1 ≤ T → isUpdate (t+1) = false →
      (A.detect (minRatioState A D η isUpdate t)).1 = minRatioDetectSet A D η isUpdate ε t)

/-- Definition 4.5 (page 14), the contract consumed by Theorem 4.6 and
provided by Theorem 5.1. Ratio correctness is conditional only on hidden
stability of the prefix ending at that operation. Query and Detect
correctness hold on all valid histories, including prefixes without a
hidden witness. The constants `α`, `Ψ`, and `ε` are fixed parameters. -/
def MinRatioSpec (A : MinRatioDataStructure) (κ α Ψ ε : ℝ) : Prop :=
  ∀ (D : DynamicInstance) (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (T : ℕ),
    MinRatioHistoryValid D isUpdate T → MinRatioSpecOn A κ α Ψ ε D η isUpdate T

/-- The specified initial flow is zero. -/
theorem minRatioFlow_zero (A : MinRatioDataStructure) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (e : ℕ) :
    minRatioFlow A D η isUpdate 0 e = 0 := by
  simp only [minRatioFlow, Nat.zero_add, Finset.range_one, Finset.sum_singleton, minRatioIncrement]

/-- The specified flow changes by exactly the scaled Update increment. -/
theorem minRatioFlow_succ (A : MinRatioDataStructure) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (t e : ℕ) :
    minRatioFlow A D η isUpdate (t+1) e =
      minRatioFlow A D η isUpdate t e + minRatioIncrement A D η isUpdate (t+1) e := by
  exact Finset.sum_range_succ _ (t+1)

/-- `last_e` never lies after the present stage. -/
theorem minRatioLast_le (A : MinRatioDataStructure) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (t e : ℕ) :
    minRatioLast A D η isUpdate t e ≤ t := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    simp only [minRatioLast]
    split_ifs
    · exact le_rfl
    · exact Nat.le_succ_of_le ih

/-- Definition 4.5 with the failure answer in the restatement of
Theorem 4.6 (page 15). Failure is `none`; success returns the unscaled
circulation. The returned state has processed the graph/coefficient
batch, but a failure adds no flow. The IPM stops that target test before
any further call. Query and Detect retain their unconditional semantics.
This differs from requiring the entire abstract state to be unchanged:
metadata for the applied batch may change, while the flow does not. -/
structure MinRatioDataStructureWithFailure where
  State : Type
  init : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → State
  update : State → List MinCostFlow.Update → (ℕ → ℝ) → (ℕ → ℝ) → ℝ →
    State × Option (ℕ → ℝ)
  query : State → ℕ → ℝ
  detect : State → Finset ℕ × State

/-- A mathematical projection used to reuse the flow-history lemmas.
It interprets a failed Update as a zero increment. This does not tell
the actual IPM to continue after failure: its target test checks the
option before calling Detect or Query. -/
def MinRatioDataStructureWithFailure.eraseFailure (A : MinRatioDataStructureWithFailure) :
    MinRatioDataStructure where
  State := A.State
  init := A.init
  update s U g ℓ η :=
    let result := A.update s U g ℓ η
    (result.1, result.2.getD (fun _ => 0))
  query := A.query
  detect := A.detect

/-- Add a success answer to every Update of a structure that never fails. -/
def MinRatioDataStructure.withFailureAnswer (A : MinRatioDataStructure) :
    MinRatioDataStructureWithFailure where
  State := A.State
  init := A.init
  update s U g ℓ η :=
    let result := A.update s U g ℓ η
    (result.1, some result.2)
  query := A.query
  detect := A.detect

/-- Erasing the success answers of a never-failing structure changes
none of its operations or states. -/
theorem eraseFailure_withFailureAnswer (A : MinRatioDataStructure) :
    A.withFailureAnswer.eraseFailure = A := by
  cases A
  rfl

/-- The actual success-or-failure result at one Update in its causal
input history. No future instance or hidden witness is an operation input. -/
def minRatioFailureDirection (A : MinRatioDataStructureWithFailure) (D : DynamicInstance)
    (η : ℕ → ℝ) (op : ℕ → Bool) (t : ℕ) : Option (ℕ → ℝ) :=
  (A.update (minRatioState A.eraseFailure D η op t) (D.U (t+1))
    (D.g (t+1)) (D.ℓ (t+1)) (η (t+1))).2

/-- Extended Definition 4.5. The projected history supplies the same
unconditional circulation, Query and Detect clauses as before, with
zero increment on failure. In addition, failure is forbidden on every
hidden-stable input prefix. On success there the ratio is at most
`-κα`. The target test stops at its first failure.
The change is the explicit failure answer required by the restatement
of Theorem 4.6, not a stronger ratio guarantee. -/
def MinRatioSpecWithFailure (A : MinRatioDataStructureWithFailure) (κ α Ψ ε : ℝ) : Prop :=
  MinRatioSpec A.eraseFailure κ α Ψ ε ∧
    ∀ (D : DynamicInstance) (η : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ),
      MinRatioHistoryValid D op T →
      ∀ t, t+1 ≤ T → op (t+1) = true → D.HiddenStable (t+1) α Ψ →
        (minRatioFailureDirection A D η op t).isSome = true

/-- The edge and vertex bounds on a history prefix used by Theorem 5.1
(page 15). Every graph through the final stage satisfies both bounds. -/
def MinRatioHistoryBounded (D : DynamicInstance) (T M N : ℕ) : Prop :=
  (∀ t ≤ T, (D.G t).m ≤ M) ∧ (∀ t ≤ T, (D.G t).n ≤ N)

/-- Definition 4.5 (page 14) with failure, on graphs within the size
limits of Theorem 5.1 (page 15). Query and Detect retain their original
guarantees on every valid history within those limits. -/
def MinRatioSpecWithFailureUpTo (A : MinRatioDataStructureWithFailure)
    (κ α Ψ ε : ℝ) (M N : ℕ) : Prop :=
  ∀ (D : DynamicInstance) (η : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ),
    MinRatioHistoryValid D op T →
    MinRatioHistoryBounded D T M N →
    MinRatioSpecOn A.eraseFailure κ α Ψ ε D η op T ∧
    (∀ t, t+1 ≤ T → op (t+1) = true → D.HiddenStable (t+1) α Ψ →
      (minRatioFailureDirection A D η op t).isSome = true)

/-- Graph connectedness invariant along dynamic min-ratio histories. -/
def MinRatioGraphConnected (G : MGraph) : Prop :=
  ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v

/-- The length range of Definition 4.4, item 5 (page 14): `|log ℓ_e| ≤ Ψ` on every edge of the
graph `G`. Hidden stability asks this at every stage, and Algorithm 2 sets its parameter `Ψ` from it
(`jtree.tex`, Algorithm 2, lines 290–291). -/
def MinRatioLengthsInRange (Ψ : ℝ) (G : MGraph) (ℓ : ℕ → ℝ) : Prop :=
  ∀ e ∈ G.E, |Real.log (ℓ e)| ≤ Ψ

/-- The length range `MinRatioLengthsInRange Ψ` at every stage of a history through stage `T`. -/
def MinRatioHistoryLengthsInRange (D : DynamicInstance) (T : ℕ) (Ψ : ℝ) : Prop :=
  ∀ t ≤ T, MinRatioLengthsInRange Ψ (D.G t) (D.ℓ t)

/-- Every length on the edges of `G` lies in `[2^{-E}, 2^E]`. The machine IPM's
checked coefficient scan accepts exactly this range (`checkedUpdateCalls_input_ranges`). -/
def LengthsWithin (G : MGraph) (E : ℕ) (l : ℕ → ℝ) : Prop :=
  ∀ e ∈ G.E, (2:ℝ)^(-(E:ℤ)) ≤ l e ∧ l e ≤ (2:ℝ)^E

/-- The stage invariant `P` holds at the graph `G` for all lengths in `[2^{-E}, 2^E]`. -/
def StageAdmits (P : MGraph → (ℕ → ℝ) → Prop) (G : MGraph) (E : ℕ) : Prop :=
  ∀ l, LengthsWithin G E l → P G l

/-- Every stage through `T` has its lengths in `[2^{-E}, 2^E]`. -/
def HistoryLengthsWithin (D : DynamicInstance) (T E : ℕ) : Prop :=
  ∀ t ≤ T, LengthsWithin (D.G t) E (D.ℓ t)

/-- On a fixed-graph history with lengths in range, an admitted stage invariant holds at
every stage. -/
theorem StageAdmits.history {P : MGraph → (ℕ → ℝ) → Prop} {G : MGraph} {E : ℕ}
    (hP : StageAdmits P G E) {D : DynamicInstance} {T : ℕ} (hG : ∀ t ≤ T, D.G t = G)
    (hL : HistoryLengthsWithin D T E) : ∀ t ≤ T, P (D.G t) (D.ℓ t) := by
  intro t ht
  have h := hL t ht
  rw [hG t ht] at h ⊢
  exact hP _ h

/-- The trivial stage invariant is admitted at every graph. -/
theorem stageAdmits_true (G : MGraph) (E : ℕ) : StageAdmits (fun _ _ => True) G E :=
  fun _ _ => trivial

/-- Lengths in `[2^{-E}, 2^E]` satisfy `|log ℓ_e| ≤ Ψ` once `E ≤ Ψ`, since `log 2 ≤ 1`. -/
theorem MinRatioLengthsInRange.of_lengthsWithin {G : MGraph} {E : ℕ} {Ψ : ℝ} {l : ℕ → ℝ}
    (hE : (E : ℝ) ≤ Ψ) (h : LengthsWithin G E l) : MinRatioLengthsInRange Ψ G l := by
  intro e he
  obtain ⟨hlo, hhi⟩ := h e he
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hpos : 0 < l e := lt_of_lt_of_le (zpow_pos h2 _) hlo
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos h2
    linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hEnn : (0 : ℝ) ≤ E := Nat.cast_nonneg E
  have hEl : (E : ℝ) * Real.log 2 ≤ E := by nlinarith
  rw [abs_le]
  constructor
  · have hl := Real.log_le_log (zpow_pos h2 _) hlo
    rw [Real.log_zpow] at hl
    push_cast at hl
    linarith
  · have hl := Real.log_le_log hpos hhi
    rw [Real.log_pow] at hl
    linarith

/-- Definition 4.5 (page 14) with failure, restricted to histories whose stages `(G, ℓ)`
satisfy `P` within the size limits `(M, N)`. A stage predicate can carry both a graph invariant
and the length range of Definition 4.4, item 5 (page 14). -/
def MinRatioSpecWithFailureUpToOn (P : MGraph → (ℕ → ℝ) → Prop)
    (A : MinRatioDataStructureWithFailure) (κ α Ψ ε : ℝ) (M N : ℕ) : Prop :=
  ∀ (D : DynamicInstance) (η : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ),
    MinRatioHistoryValid D op T →
    MinRatioHistoryBounded D T M N →
    (∀ t ≤ T, P (D.G t) (D.ℓ t)) →
    MinRatioSpecOn A.eraseFailure κ α Ψ ε D η op T ∧
    (∀ t, t+1 ≤ T → op (t+1) = true → D.HiddenStable (t+1) α Ψ →
      (minRatioFailureDirection A D η op t).isSome = true)

/-- Connected-graph specialization of `MinRatioSpecWithFailureUpToOn`, matching
the connectedness precondition of Theorem 5.1 (`concrete_theorem_5_1`). -/
abbrev MinRatioSpecWithFailureConnectedUpTo (A : MinRatioDataStructureWithFailure)
    (κ α Ψ ε : ℝ) (M N : ℕ) : Prop :=
  MinRatioSpecWithFailureUpToOn (fun G _ => MinRatioGraphConnected G) A κ α Ψ ε M N

/-- An unrestricted size-bounded implementation restricts to any stage property `P`. -/
theorem MinRatioSpecWithFailureUpTo.upToOn {P : MGraph → (ℕ → ℝ) → Prop}
    {A : MinRatioDataStructureWithFailure} {κ α Ψ ε : ℝ} {M N : ℕ}
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ ε M N) :
    MinRatioSpecWithFailureUpToOn P A κ α Ψ ε M N :=
  fun D η op T hvalid hsize _ => hA D η op T hvalid hsize

/-- Specialization to connected histories within the size limits. -/
theorem MinRatioSpecWithFailureUpTo.connectedUpTo
    {A : MinRatioDataStructureWithFailure} {κ α Ψ ε : ℝ} {M N : ℕ}
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ ε M N) :
    MinRatioSpecWithFailureConnectedUpTo A κ α Ψ ε M N :=
  hA.upToOn

/-- Taking the trivial stage invariant recovers the unrestricted bounded specification. -/
theorem MinRatioSpecWithFailureUpToOn.toUpTo
    {A : MinRatioDataStructureWithFailure} {κ α Ψ ε : ℝ} {M N : ℕ}
    (hA : MinRatioSpecWithFailureUpToOn (fun _ _ => True) A κ α Ψ ε M N) :
    MinRatioSpecWithFailureUpTo A κ α Ψ ε M N :=
  fun D η op T hvalid hsize => hA D η op T hvalid hsize (fun _ _ => trivial)

/-- Monotonicity of `MinRatioSpecWithFailureUpToOn` in the stage invariant. -/
theorem MinRatioSpecWithFailureUpToOn.mono {P Q : MGraph → (ℕ → ℝ) → Prop}
    (hPQ : ∀ G ℓ, Q G ℓ → P G ℓ) {A : MinRatioDataStructureWithFailure}
    {κ α Ψ ε : ℝ} {M N : ℕ}
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ ε M N) :
    MinRatioSpecWithFailureUpToOn Q A κ α Ψ ε M N :=
  fun D η op T hvalid hsize hQ => hA D η op T hvalid hsize (fun t ht => hPQ _ _ (hQ t ht))

/-- An all-history implementation satisfies the contract at any pair of size limits. -/
theorem MinRatioSpecWithFailure.upTo {A : MinRatioDataStructureWithFailure}
    {κ α Ψ ε : ℝ} (hA : MinRatioSpecWithFailure A κ α Ψ ε) (M N : ℕ) :
    MinRatioSpecWithFailureUpTo A κ α Ψ ε M N := by
  intro D η op T hvalid _
  exact ⟨hA.1 D η op T hvalid, hA.2 D η op T hvalid⟩

/-- An all-history implementation satisfies the connected contract at any pair of size limits. -/
theorem MinRatioSpecWithFailure.connectedUpTo {A : MinRatioDataStructureWithFailure}
    {κ α Ψ ε : ℝ} (hA : MinRatioSpecWithFailure A κ α Ψ ε) (M N : ℕ) :
    MinRatioSpecWithFailureConnectedUpTo A κ α Ψ ε M N :=
  (hA.upTo M N).connectedUpTo

/-- Every implementation of the original contract implements the
extended contract by answering success on every Update. This carries
the existing reference implementation and its examples over unchanged. -/
theorem MinRatioSpec.withFailureAnswer (A : MinRatioDataStructure) (κ α Ψ ε : ℝ)
    (hA : MinRatioSpec A κ α Ψ ε) :
    MinRatioSpecWithFailure A.withFailureAnswer κ α Ψ ε := by
  constructor
  · simpa only [eraseFailure_withFailureAnswer] using hA
  · intro D η op T hvalid t ht hop hhidden
    rfl

/-- A successful answer projects to its actual circulation. -/
theorem minRatioDirection_of_success (A : MinRatioDataStructureWithFailure) (D : DynamicInstance)
    (η : ℕ → ℝ) (op : ℕ → Bool) (t : ℕ) (d : ℕ → ℝ)
    (h : minRatioFailureDirection A D η op t = some d) :
    minRatioDirection A.eraseFailure D η op t = d := by
  change (minRatioFailureDirection A D η op t).getD (fun _ => 0) = d
  rw [h]
  rfl

/-- A failed answer projects to zero and therefore contributes no flow. -/
theorem minRatioDirection_of_failure (A : MinRatioDataStructureWithFailure) (D : DynamicInstance)
    (η : ℕ → ℝ) (op : ℕ → Bool) (t : ℕ)
    (h : minRatioFailureDirection A D η op t = none) :
    minRatioDirection A.eraseFailure D η op t = fun _ => 0 := by
  change (minRatioFailureDirection A D η op t).getD (fun _ => 0) = _
  rw [h]
  rfl

/-- The represented flow is unchanged on a failed Update, even though
the returned state may record the new graph and coefficients. -/
theorem minRatioFlow_of_failure (A : MinRatioDataStructureWithFailure) (D : DynamicInstance)
    (η : ℕ → ℝ) (op : ℕ → Bool) (t e : ℕ)
    (h : minRatioFailureDirection A D η op t = none) :
    minRatioFlow A.eraseFailure D η op (t+1) e = minRatioFlow A.eraseFailure D η op t e := by
  rw [minRatioFlow_succ]
  have hz : minRatioIncrement A.eraseFailure D η op (t+1) e = 0 := by
    simp only [minRatioIncrement]
    split_ifs
    · rw [minRatioDirection_of_failure A D η op t h]
      simp only [mul_zero]
    · rfl
  rw [hz, add_zero]

/-- An explicit failure certifies that this input prefix is not hidden
stable. No ratio, Query or Detect property is assumed from that failure. -/
theorem MinRatioSpecWithFailure.not_hiddenStable_of_failure
    (A : MinRatioDataStructureWithFailure) (κ α Ψ ε : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ ε)
    (D : DynamicInstance) (η : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (ht : t+1 ≤ T) (hop : op (t+1) = true)
    (hfail : minRatioFailureDirection A D η op t = none) :
    ¬ D.HiddenStable (t+1) α Ψ := by
  intro hhidden
  have hh := hA.2 D η op T hvalid t ht hop hhidden
  rw [hfail] at hh
  contradiction

/-- Success always returns a circulation. On a hidden-stable prefix its
ratio meets exactly the `-κα` bound, with no strengthened approximation. -/
theorem MinRatioSpecWithFailure.success_properties
    (A : MinRatioDataStructureWithFailure) (κ α Ψ ε : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ ε)
    (D : DynamicInstance) (η : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (ht : t+1 ≤ T) (hop : op (t+1) = true)
    (d : ℕ → ℝ) (hsuccess : minRatioFailureDirection A D η op t = some d) :
    (D.G (t+1)).IsCirculation d ∧
      (D.HiddenStable (t+1) α Ψ →
        (D.G (t+1)).inner (D.g (t+1)) d / (D.G (t+1)).lnorm (D.ℓ (t+1)) d ≤ -κ*α) := by
  have hh := (hA.1 D η op T hvalid).2.1 t ht hop
  rw [minRatioDirection_of_success A D η op t d hsuccess] at hh
  exact hh

end MinCostFlow.IPM
