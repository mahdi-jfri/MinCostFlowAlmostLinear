module

public import MinCostFlow.LastLevelProgram.IndexGraph
public import MinCostFlow.Scaling.SortCapacitiesProgram

/-!
# Ordering active names for the last-level rebuild

A named graph can store its live names in any order. Sorting a duplicate-free
name array produces the canonical ordering expected by the compact inputs
to Theorem 2.2 (page 7). This uses the shared verified word sorter.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Scaling Scaling.Machine

private theorem sortCapacities_eq_finsetSort (xs : List ℕ) (hxs : xs.Nodup) :
    (sortCapacities xs).1 = xs.toFinset.sort := by
  have hperm := sortCapacities_perm xs
  have hset : (sortCapacities xs).1.toFinset = xs.toFinset := by
    ext x
    simpa only [List.mem_toFinset] using hperm.mem_iff (a := x)
  have hn := hperm.nodup_iff.mpr hxs
  have hsorted := (List.toFinset_sort (r := (· ≤ ·)) hn).2 (sortCapacities_sorted xs)
  rw [hset] at hsorted
  exact hsorted.symm

/-- Sorting a duplicate-free enumeration writes the canonical name list
and uses the shared sorter's linear-logarithmic cost bound. -/
theorem sortNames_runs {w b : ℕ} {p : Program} (hp : p.HasAt b (sortCapacitiesModule b))
    (xs : List ℕ) (hxs : xs.Nodup) (names : Finset ℕ) (hset : xs.toFinset = names)
    (src heap pos : ℕ) (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hwords : ∀ a ∈ [src, xs.length, heap], a < 2 ^ w)
    (hpre : (sortCapacitiesContract w xs).pre [src, xs.length, heap] mem) :
    ∃ body, p.procs[b]? = some body ∧ ∃ o st c,
      Runs w p ω body (startState [src, xs.length, heap] mem pos) o st c ∧
      heap + xs.length ≤ o.value ∧ ListAt st.mem (o.value - xs.length) names.sort ∧
      (∀ a < heap, st.mem a = mem a) ∧ ZeroFrom st.mem o.value ∧
      c ≤ 2440 * (Nat.clog 2 (xs.length + 1) + 1) * (xs.length + 1) + 900 := by
  obtain ⟨body, hb, o, st, c, hr, hpost, hc⟩ :=
    sortCapacities_meetsContract hp xs [src, xs.length, heap] mem pos ω hwords hpre
  obtain ⟨⟨_, _, hframe, hzero, _⟩, hroom, hout⟩ := hpost
  change ListAt st.mem (o.value - xs.length) (sortCapacities xs).1 at hout
  rw [sortCapacities_eq_finsetSort xs hxs, hset] at hout
  exact ⟨body, hb, o, st, c, hr, hroom, hout, hframe, hzero, hc.trans (sortCapacities_cost_le w _ _ xs)⟩

/-- A sorted list of edge names supplies the lookup used by the packing passes. -/
theorem sortedEdgeNames_at {H : MGraph} {mem : ℕ → ℕ} {a : ℕ}
    (h : ListAt mem a H.E.sort) : ∀ i < H.m, mem (a + i) = edgeName H i := by
  intro i hi
  have hi' : i < H.E.sort.length := by simpa [Finset.length_sort, MGraph.m] using hi
  rw [edgeName, dite_eq_left hi, Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_apply]
  exact h i hi'

/-- A sorted list of vertex names supplies the canonical index-to-name map. -/
theorem sortedVertexNames_at {H : MGraph} {mem : ℕ → ℕ} {a : ℕ}
    (h : ListAt mem a H.V.sort) : ∀ i < H.n, mem (a + i) = vertexName H i := by
  intro i hi
  have hi' : i < H.V.sort.length := by simpa [Finset.length_sort, MGraph.n] using hi
  rw [vertexName, dite_eq_left hi, Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_apply]
  exact h i hi'

end MinCostFlow.LastLevelProgram
