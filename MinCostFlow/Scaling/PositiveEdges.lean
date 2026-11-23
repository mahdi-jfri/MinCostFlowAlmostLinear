module

public import MinCostFlow.Scaling.Circulation
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup

/-!
# Removing zero-capacity edge slots

The size bounds in the reductions of Appendix C of Chen et al.,
arXiv:2203.00671v2, count actual positive-capacity edges. Zero-capacity slots
can be removed before a solver call. Their flow is forced to zero, so the
remaining flow coordinates preserve the objective and every vertex balance.
The retained indices remain in their original order.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Scan original edge indices and retain precisely those with positive capacity. -/
def positiveEdges (I : Circulation) : List (Fin I.m) :=
  (List.finRange I.m).filter (fun e => 0 < I.capacity e)

/-- The retained edge indices have no repetitions. -/
theorem positiveEdges_nodup (I : Circulation) : I.positiveEdges.Nodup :=
  (List.nodup_finRange I.m).filter _

/-- Membership means exactly positive capacity. -/
theorem mem_positiveEdges_iff (I : Circulation) (e : Fin I.m) :
    e ∈ I.positiveEdges ↔ 0 < I.capacity e := by
  simp [positiveEdges]

/-- The retained-index list has at most the original number of entries. -/
theorem positiveEdges_length_le (I : Circulation) : I.positiveEdges.length ≤ I.m := by
  have h := List.length_filter_le (fun e => 0 < I.capacity e) (List.finRange I.m)
  simpa only [positiveEdges, List.length_finRange] using h

/-- The explicit map from retained edge slots to original edge slots. -/
def positiveIndex (I : Circulation) (e : Fin I.positiveEdges.length) : Fin I.m :=
  I.positiveEdges[e.val]

/-- Retained edge slots map injectively into the original edge slots. -/
theorem positiveIndex_injective (I : Circulation) : Function.Injective I.positiveIndex := by
  intro a b h
  apply Fin.ext
  exact I.positiveEdges_nodup.getElem_inj_iff.mp h

/-- The graph whose edge slots all have positive capacity. -/
abbrev withoutZeroEdges (I : Circulation) : Circulation where
  n := I.n
  m := I.positiveEdges.length
  tail := fun e => I.tail (I.positiveIndex e)
  head := fun e => I.head (I.positiveIndex e)
  capacity := fun e => I.capacity (I.positiveIndex e)
  cost := fun e => I.cost (I.positiveIndex e)

/-- Restrict a flow to the retained edge coordinates. -/
def restrictPositive (I : Circulation) (f : Fin I.m → ℝ) :
    Fin I.positiveEdges.length → ℝ := fun e => f (I.positiveIndex e)

private theorem sum_list_get {α : Type} (es : List α) (a : α → ℝ) :
    (∑ i : Fin es.length, a es[i.val]) = (es.map a).sum := by
  rw [← Fin.sum_ofFn]
  have h : List.ofFn (fun i : Fin es.length => a es[i.val]) = es.map a := by
    change List.ofFn (a ∘ es.get) = es.map a
    rw [← List.map_ofFn]
    congr 1
    exact List.ofFn_get es
  rw [h]

private theorem sum_filter_eq {α : Type} (es : List α) (p : α → Bool) (a : α → ℝ)
    (h : ∀ e ∈ es, p e = false → a e = 0) :
    ((es.filter p).map a).sum = (es.map a).sum := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have ht : ∀ k ∈ es, p k = false → a k = 0 := by
      intro k hk
      exact h k (List.mem_cons_of_mem _ hk)
    cases hp : p e with
    | false =>
      have he := h e List.mem_cons_self hp
      simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte, List.map_cons,
        List.sum_cons, he, zero_add]
      exact ih ht
    | true =>
      simp only [List.filter_cons, hp, ↓reduceIte, List.map_cons, List.sum_cons]
      rw [ih ht]

/-- Summing over retained indices preserves every sum supported on positive
capacity edges. -/
theorem sum_positiveIndex (I : Circulation) (a : Fin I.m → ℝ)
    (ha : ∀ e, I.capacity e = 0 → a e = 0) :
    (∑ e : Fin I.positiveEdges.length, a (I.positiveIndex e)) = ∑ e, a e := by
  change (∑ e : Fin I.positiveEdges.length, a I.positiveEdges[e.val]) = _
  rw [sum_list_get]
  rw [positiveEdges]
  rw [sum_filter_eq]
  · exact (Fin.sum_univ_def a).symm
  · intro e _ h
    apply ha e
    have hn : ¬ 0 < I.capacity e := by simpa only [decide_eq_false_iff_not] using h
    omega

/-- Restriction preserves balances when the removed edge slots have zero flow. -/
theorem restrictPositive_balance (I : Circulation) (f : Fin I.m → ℝ)
    (hf : ∀ e, I.capacity e = 0 → f e = 0) (v : Fin I.n) :
    I.withoutZeroEdges.balance (I.restrictPositive f) v = I.balance f v := by
  apply I.sum_positiveIndex (fun e => I.incidence e v * f e)
  intro e he
  rw [hf e he, mul_zero]

/-- Restriction preserves the objective when the removed slots have zero flow. -/
theorem restrictPositive_objective (I : Circulation) (f : Fin I.m → ℝ)
    (hf : ∀ e, I.capacity e = 0 → f e = 0) :
    I.withoutZeroEdges.objective (I.restrictPositive f) = I.objective f := by
  apply I.sum_positiveIndex (fun e => (I.cost e : ℝ) * f e)
  intro e he
  rw [hf e he, mul_zero]

/-- Every feasible original flow restricts to a feasible positive-capacity flow. -/
theorem restrictPositive_feasible (I : Circulation) (f : Fin I.m → ℝ)
    (hf : I.Feasible f) : I.withoutZeroEdges.Feasible (I.restrictPositive f) := by
  have hz : ∀ e, I.capacity e = 0 → f e = 0 := by
    intro e he
    have h := (hf.2 e).2
    rw [he, Nat.cast_zero] at h
    exact le_antisymm h (hf.2 e).1
  constructor
  · intro v
    rw [restrictPositive_balance I f hz v]
    exact hf.1 v
  · intro e
    exact hf.2 (I.positiveIndex e)

/-- Find the retained slot of an original edge whose capacity is positive. -/
def positiveSlot (I : Circulation) (e : Fin I.m) (he : 0 < I.capacity e) :
    Fin I.positiveEdges.length :=
  ⟨I.positiveEdges.idxOf e, List.idxOf_lt_length_of_mem ((I.mem_positiveEdges_iff e).mpr he)⟩

/-- The retained-slot map is a right inverse on positive-capacity original edges. -/
theorem positiveIndex_positiveSlot (I : Circulation) (e : Fin I.m)
    (he : 0 < I.capacity e) : I.positiveIndex (I.positiveSlot e he) = e := by
  exact List.getElem_idxOf _

/-- The retained-slot map is also a left inverse on retained edges. -/
theorem positiveSlot_positiveIndex (I : Circulation) (e : Fin I.positiveEdges.length)
    (he : 0 < I.capacity (I.positiveIndex e)) :
    I.positiveSlot (I.positiveIndex e) he = e := by
  apply I.positiveIndex_injective
  exact I.positiveIndex_positiveSlot _ he

/-- Reinsert zero coordinates for removed edge slots. -/
def extendPositive (I : Circulation) (f : Fin I.positiveEdges.length → ℝ)
    (e : Fin I.m) : ℝ :=
  if he : 0 < I.capacity e then f (I.positiveSlot e he) else 0

/-- Every removed slot is zero in the extended flow. -/
theorem extendPositive_zero (I : Circulation) (f : Fin I.positiveEdges.length → ℝ)
    (e : Fin I.m) (he : I.capacity e = 0) : I.extendPositive f e = 0 := by
  simp only [extendPositive, he, Nat.lt_irrefl, ↓reduceDIte]

/-- Restricting after extending returns the original retained flow. -/
theorem restrictPositive_extendPositive (I : Circulation)
    (f : Fin I.positiveEdges.length → ℝ) :
    I.restrictPositive (I.extendPositive f) = f := by
  funext e
  have he : 0 < I.capacity (I.positiveIndex e) :=
    (I.mem_positiveEdges_iff _).mp (List.getElem_mem e.isLt)
  simp only [restrictPositive, extendPositive, he, ↓reduceDIte,
    positiveSlot_positiveIndex]

/-- Extending a feasible retained flow yields a feasible original circulation. -/
theorem extendPositive_feasible (I : Circulation)
    (f : Fin I.positiveEdges.length → ℝ) (hf : I.withoutZeroEdges.Feasible f) :
    I.Feasible (I.extendPositive f) := by
  constructor
  · intro v
    have h := I.restrictPositive_balance (I.extendPositive f) (I.extendPositive_zero f) v
    rw [restrictPositive_extendPositive] at h
    exact h.symm.trans (hf.1 v)
  · intro e
    by_cases he : 0 < I.capacity e
    · simp only [extendPositive, he, ↓reduceDIte]
      have h := hf.2 (I.positiveSlot e he)
      simpa only [withoutZeroEdges, positiveIndex_positiveSlot] using h
    · have hz : I.capacity e = 0 := by omega
      rw [I.extendPositive_zero f e hz, hz]
      simp only [Nat.cast_zero, le_refl, and_self]

/-- An optimum of the graph without zero-capacity edges extends to an exact
optimum of the original graph, still comparing with all feasible real flows. -/
theorem extendPositive_optimal (I : Circulation)
    (f : Fin I.positiveEdges.length → ℝ) (hf : I.withoutZeroEdges.Optimal f) :
    I.Optimal (I.extendPositive f) := by
  refine ⟨I.extendPositive_feasible f hf.1, ?_⟩
  intro g hg
  have hz : ∀ e, I.capacity e = 0 → g e = 0 := by
    intro e he
    have h := (hg.2 e).2
    rw [he, Nat.cast_zero] at h
    exact le_antisymm h (hg.2 e).1
  have hc := hf.2 (I.restrictPositive g) (I.restrictPositive_feasible g hg)
  rw [I.restrictPositive_objective g hz] at hc
  have he := I.restrictPositive_objective (I.extendPositive f) (I.extendPositive_zero f)
  rw [restrictPositive_extendPositive] at he
  rw [← he]
  exact hc

end MinCostFlow.Scaling.Circulation
