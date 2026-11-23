module

public import MinCostFlow.HierPaths.LiveSupport
public import MinCostFlow.HierPaths.LossCountersRun

/-!
# The state of `Delete`

The operation `Delete(e)` of the path data structure works on arrays
that `Init` builds once:

* the connector system `C` of `HierPaths/Live.lean`, on the terminals `0, …, 2 ^ x - 1`;
* for each input edge `e`, the reverse list `revList e` of the designated endpoints of the
  connector occurrences on `e`;
* for each terminal `t`, the list `termConns t` of its connectors;
* the connector arrays `pairConns p` of the pairs of children, numbered `p < numPairs`, and for
  each connector the number `pairOf c` of its pair;
* the support arrays of `HierPaths/LiveSupport.lean`.

`StaticArrays` holds these arrays, and `StaticArrays.Spec` their specifications. The dynamic
state `DelState` holds the loss counters (`LossState`), the deleted edges, the set of connectors
whose eligibility bit is cleared, and the cursors of the support arrays and the pair arrays.

`DelInv` is the invariant that `Delete` keeps: the counters are correct for the directly failed
terminals (`LossInv`), each failed terminal comes from the reverse list of a deleted edge, the
reverse-index rule holds, the cleared bits are exactly the ineligible connectors, and every cursor
satisfies `CurInv`: the entries before it are invalid, and the entry under it, if any, is valid.
`delInv_init` shows that the initial state satisfies it.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

/-- The arrays of the static structure that `Delete` reads. -/
structure StaticArrays where
  /-- The connector system. -/
  C : ConnectorSystem
  /-- The terminals are `0, …, 2 ^ x - 1`. -/
  x : ℕ
  /-- The branching is `2 ^ b`. -/
  b : ℕ
  /-- The designated endpoints of the connector occurrences on each input edge. -/
  revList : ℕ → List ℕ
  /-- The connectors of each terminal. -/
  termConns : ℕ → List ℕ
  /-- The number of pairs of children. -/
  numPairs : ℕ
  /-- The connector array of each pair of children. -/
  pairConns : ℕ → List ℕ
  /-- The pair of children of each connector. -/
  pairOf : ℕ → ℕ

/-- The specification of the static arrays for the input graph `G`, with `ξ` bounding the reverse
lists and `κ` the connector lists of the terminals. -/
structure StaticArrays.Spec (A : StaticArrays) (G : Graph) (ξ κ : ℕ) : Prop where
  numTerm_eq : A.C.numTerm = 2 ^ A.x
  b_pos : 0 < A.b
  fits : A.C.FitsGraph G
  rev_lt : ∀ e, ∀ t ∈ A.revList e, t < A.C.numTerm
  rev_mem : ∀ c < A.C.numConn, ∀ e ∈ (A.C.walk c).edges, A.C.desig c ∈ A.revList e
  rev_length : ∀ e, (A.revList e).length ≤ ξ
  mem_termConns : ∀ t < A.C.numTerm, ∀ c,
    c ∈ A.termConns t ↔ c < A.C.numConn ∧ (A.C.endA c = t ∨ A.C.endB c = t)
  termConns_nodup : ∀ t, (A.termConns t).Nodup
  termConns_length : ∀ t, (A.termConns t).length ≤ κ
  pairConns_nodup : ∀ p, (A.pairConns p).Nodup
  mem_pairConns : ∀ p, ∀ c ∈ A.pairConns p, c < A.C.numConn ∧ A.pairOf c = p
  pairOf_lt : ∀ c < A.C.numConn, A.pairOf c < A.numPairs

/-- The dynamic state of the data structure. -/
structure DelState where
  /-- The loss counters, with the directly failed and the globally lost terminals. -/
  loss : LossState
  /-- The deleted edges. -/
  deleted : Finset ℕ
  /-- The connectors whose eligibility bit is cleared. -/
  inelig : Finset ℕ
  /-- The cursor of the support array of each vertex. -/
  supCur : ℕ → ℕ
  /-- The cursor of the connector array of each pair of children. -/
  pairCur : ℕ → ℕ

namespace StaticArrays

variable (A : StaticArrays)

/-- The surviving terminals: those not globally lost. -/
def surv (st : DelState) : Finset ℕ :=
  Finset.range A.C.numTerm \ st.loss.glob

/-- Validity of the entries of the support array of `w` for the surviving terminals `S`. -/
def supValid (S : Finset ℕ) (w : ℕ) (i : ℕ) : Bool :=
  A.C.entryLive S ((A.C.supportArray w).getD i default)

/-- Validity of the entries of the connector array of pair `p`: the connector is eligible. -/
def pairValid (S : Finset ℕ) (p : ℕ) (i : ℕ) : Bool :=
  decide (A.C.Eligible S ((A.pairConns p).getD i 0))

end StaticArrays

/-- The initial state: nothing deleted or failed, all cursors at the start. -/
def DelState.init : DelState :=
  ⟨LossState.init, ∅, ∅, fun _ => 0, fun _ => 0⟩

/-- The cursor invariant for an array of length `len` with validity `valid`: the cursor `c` is in
the array, the entries before it are invalid, and the entry under it, if any, is valid. -/
def CurInv (valid : ℕ → Bool) (len c : ℕ) : Prop :=
  c ≤ len ∧ (∀ i < c, valid i = false) ∧ (c < len → valid c = true)

namespace StaticArrays

variable (A : StaticArrays)

/-- The invariant of the dynamic state for the input graph `G`. -/
structure DelInv (G : Graph) (st : DelState) : Prop where
  loss : LossInv A.x A.b st.loss.failed st.loss
  failed_sub : st.loss.failed ⊆ st.deleted.biUnion fun e => (A.revList e).toFinset
  rule : A.C.ReverseIndexRule st.deleted (A.surv st)
  inelig_eq : st.inelig = (Finset.range A.C.numConn).filter fun c => ¬ A.C.Eligible (A.surv st) c
  supCur : ∀ w < G.n, CurInv (A.supValid (A.surv st) w) (A.C.supportArray w).length (st.supCur w)
  pairCur : ∀ p < A.numPairs,
    CurInv (A.pairValid (A.surv st) p) (A.pairConns p).length (st.pairCur p)

end StaticArrays

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

public section

/-! ### Cursors -/

/-- A cursor whose entries before it stay invalid, refreshed with `advance`, satisfies the cursor
invariant. -/
theorem curInv_advance {valid : ℕ → Bool} {len c : ℕ} (hc : c ≤ len)
    (hbefore : ∀ i < c, valid i = false) : CurInv valid len (advance valid len c) := by
  refine ⟨advance_le valid hc, fun i hi => ?_, advance_valid valid len c⟩
  rcases Nat.lt_or_ge i c with h | h
  · exact hbefore i h
  · exact advance_invalid valid len c i h hi

/-- A cursor that is not refreshed keeps its invariant when the validity only shrinks and the
entry under it stays valid. -/
theorem CurInv.of_le {valid valid' : ℕ → Bool} {len c : ℕ} (h : CurInv valid len c)
    (hmono : ∀ i, valid' i = true → valid i = true) (hc : c < len → valid' c = true) :
    CurInv valid' len c := by
  refine ⟨h.1, fun i hi => ?_, hc⟩
  cases hv : valid' i
  · rfl
  · have := h.2.1 i hi
    rw [hmono i hv] at this
    exact absurd this (by decide)

/-- Under the cursor invariant, the cursor is at the end exactly when all entries are invalid. -/
theorem CurInv.eq_len_iff {valid : ℕ → Bool} {len c : ℕ} (h : CurInv valid len c) :
    c = len ↔ ∀ i < len, valid i = false := by
  constructor
  · rintro rfl
    exact h.2.1
  · intro hall
    rcases Nat.lt_or_ge c len with hlt | hge
    · have := h.2.2 hlt
      rw [hall c hlt] at this
      exact absurd this (by decide)
    · exact le_antisymm h.1 hge

namespace StaticArrays

variable (A : StaticArrays)

theorem surv_subset (st : DelState) : A.surv st ⊆ Finset.range A.C.numTerm :=
  Finset.sdiff_subset

theorem mem_surv {st : DelState} {t : ℕ} :
    t ∈ A.surv st ↔ t < A.C.numTerm ∧ t ∉ st.loss.glob := by
  rw [surv, Finset.mem_sdiff, Finset.mem_range]

/-- The support cursor of a vertex of `G` is at the end exactly when the vertex is pruned. -/
theorem supCur_eq_len_iff {G : Graph} {st : DelState} (hinv : A.DelInv G st) {w : ℕ}
    (hw : w < G.n) :
    st.supCur w = (A.C.supportArray w).length ↔ w ∈ A.C.prunedSet G (A.surv st) := by
  rw [(hinv.supCur w hw).eq_len_iff, ConnectorSystem.mem_prunedSet,
    ← A.C.exists_live_entry_iff (A.surv_subset st) hw]
  constructor
  · rintro hall
    refine ⟨hw, ?_⟩
    rintro ⟨y, hy, hl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    have := hall i hi
    rw [supValid, List.getD_eq_getElem _ _ hi, hl] at this
    exact absurd this (by decide)
  · rintro ⟨_, hno⟩ i hi
    rw [supValid, List.getD_eq_getElem _ _ hi]
    cases h : A.C.entryLive (A.surv st) (A.C.supportArray w)[i]
    · rfl
    · exact (hno ⟨_, List.getElem_mem hi, h⟩).elim

/-- The initial state satisfies the invariant. -/
theorem delInv_init {G : Graph} {ξ κ : ℕ} (hA : A.Spec G ξ κ) : A.DelInv G DelState.init := by
  have hsurv : A.surv DelState.init = Finset.range A.C.numTerm := by
    simp [surv, DelState.init, LossState.init]
  have helig : ∀ c < A.C.numConn, A.C.Eligible (A.surv DelState.init) c := by
    intro c hc
    rw [hsurv]
    obtain ⟨ha, hb, _⟩ := hA.fits.2 c hc
    exact ⟨hc, Finset.mem_range.mpr ha, Finset.mem_range.mpr hb⟩
  refine ⟨lossInv_init, by simp [DelState.init, LossState.init], ?_, ?_, ?_, ?_⟩
  · intro c _ e _ he; simp [DelState.init] at he
  · ext c
    rw [Finset.mem_filter, Finset.mem_range]
    simp only [DelState.init, Finset.notMem_empty, false_iff, not_and, not_not]
    exact helig c
  · intro w _
    refine ⟨Nat.zero_le _, fun i hi => absurd hi (Nat.not_lt_zero _), fun hlt => ?_⟩
    change 0 < _ at hlt
    change A.supValid _ w 0 = true
    have hmem : (A.C.supportArray w)[0] ∈ A.C.supportArray w := List.getElem_mem hlt
    rw [supValid, List.getD_eq_getElem _ _ hlt]
    rcases (A.C.mem_supportArray).mp hmem with ⟨t, ht, _, he⟩ | ⟨c, hc, pos, _, he⟩
    · rw [he]; simp [ConnectorSystem.entryLive, hsurv, ht]
    · rw [he]; simpa [ConnectorSystem.entryLive] using helig c hc
  · intro p _
    refine ⟨Nat.zero_le _, fun i hi => absurd hi (Nat.not_lt_zero _), fun hlt => ?_⟩
    change 0 < _ at hlt
    change A.pairValid _ p 0 = true
    rw [pairValid, List.getD_eq_getElem _ _ hlt]
    simpa using helig _ (hA.mem_pairConns p _ (List.getElem_mem hlt)).1

end StaticArrays

end

end MinCostFlow.HierPaths
