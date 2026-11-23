module

public import MinCostFlow.MinRatio.FreshInsert
public import MinCostFlow.MinRatio.FreshDelete

/-!
# The fresh-name tables after one update

The name tables represent the two maps and the next fresh name used by
Algorithm 2's batch translator. An insertion changes exactly two entries
and advances the counter. The model theorem then gives the fresh-name
invariant on the updated graphs. A deletion leaves the tables alone.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

/-- The memory representation of the two bounded tables and counter. -/
def FreshTablesAt (mem : ℕ → ℕ) (forward inverse counter extCap intCap : ℕ)
    (e2i i2e : ℕ → ℕ) (next : ℕ) : Prop :=
  mem counter = next ∧ (∀ e < extCap, mem (forward + e) = e2i e) ∧
    ∀ e < intCap, mem (inverse + e) = i2e e

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open Chain

/-- An insertion realizes both function updates in `translateUpdate`.
Disjoint name tables below the heap ensure that an untouched entry does
not overlap any of the other writes. -/
theorem freshInsert_tables {w e u v fwd inv counter heap ret next extCap intCap : ℕ}
    {e2i i2e : ℕ → ℕ} {mem mem' : ℕ → ℕ}
    (hbefore : FreshTablesAt mem fwd inv counter extCap intCap e2i i2e next)
    (he : e < extCap) (hn : next < intCap)
    (hf : fwd + extCap ≤ heap) (hi : inv + intCap ≤ heap)
    (hdisjoint : fwd + extCap ≤ inv ∨ inv + intCap ≤ fwd)
    (hfc : counter < fwd ∨ fwd + extCap ≤ counter)
    (hic : counter < inv ∨ inv + intCap ≤ counter)
    (hout : (freshInsertContract w e u v next).post [e, u, v, fwd, inv, counter, heap] mem ret mem') :
    FreshTablesAt mem' fwd inv counter extCap intCap
      (Function.update e2i e next) (Function.update i2e next e) (next + 1) := by
  obtain ⟨fwd', inv', ctr', heap', hargs, _, hforward, hinverse, hcounter, _, hframe, _⟩ := hout
  have hf' : fwd = fwd' := congrArg (fun l : List ℕ => l.getD 3 0) hargs
  have hi' : inv = inv' := congrArg (fun l : List ℕ => l.getD 4 0) hargs
  have hctr' : counter = ctr' := congrArg (fun l : List ℕ => l.getD 5 0) hargs
  have hh' : heap = heap' := congrArg (fun l : List ℕ => l.getD 6 0) hargs
  subst fwd' inv' ctr' heap'
  refine ⟨hcounter, ?_, ?_⟩
  · intro j hj
    by_cases hje : j = e
    · subst j
      simpa using hforward
    · rw [Function.update_of_ne hje]
      exact (hframe _ (by omega) (by omega) (by omega) (by omega)).trans (hbefore.2.1 j hj)
  · intro j hj
    by_cases hjn : j = next
    · subst j
      simpa using hinverse
    · rw [Function.update_of_ne hjn]
      exact (hframe _ (by omega) (by omega) (by omega) (by omega)).trans (hbefore.2.2 j hj)

/-- A deletion preserves all table cells, provided they lie below the
output. Its model transition changes only the current graphs. -/
theorem freshDelete_tables {w external src fwd inv counter heap ret next extCap intCap : ℕ}
    {e2i i2e : ℕ → ℕ} {mem mem' : ℕ → ℕ}
    (hbefore : FreshTablesAt mem fwd inv counter extCap intCap e2i i2e next)
    (hf : fwd + extCap ≤ heap) (hi : inv + intCap ≤ heap) (hc : counter < heap)
    (hout : (freshDeleteContract w external (e2i external)).post [src, fwd, heap] mem ret mem') :
    FreshTablesAt mem' fwd inv counter extCap intCap e2i i2e next := by
  have hframe : ∀ a < heap, mem' a = mem a := hout.2.2.2.1
  refine ⟨(hframe _ hc).trans hbefore.1, ?_, ?_⟩
  · intro e he
    exact (hframe _ (by omega)).trans (hbefore.2.1 e he)
  · intro e he
    exact (hframe _ (by omega)).trans (hbefore.2.2 e he)

end MinCostFlow.MinRatio
