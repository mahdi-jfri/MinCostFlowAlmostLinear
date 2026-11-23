module

public import MinCostFlow.IPM.Machine.InitialAuxiliaryPrefix
public import MinCostFlow.IPM.Machine.InitialDeficitModel
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.OfFn

/-!
# The order of auxiliary edges agrees with Lemma 4.12

The machine scans vertices in increasing order and emits a record only
at nonzero deficit. The existing construction in Lemma 4.12 (Chen et al.,
arXiv:2203.00671v2, page 31 and Appendix B.1 page 92) uses the increasing
bijection `deficitIndex`. This file identifies the two orders. Thus
compacting the emitted records does not silently permute auxiliary edges.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

private theorem ordered_records {α β : Type} [LinearOrder α] (s : Finset α) (f : α → β) :
    List.ofFn (fun j : Fin s.card => f (s.orderIsoOfFin rfl j).val) = (s.sort (· ≤ ·)).map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_map]
    rfl

private theorem sorted_selected {α : Type} [LinearOrder α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (s.filter p).sort (· ≤ ·) = (s.sort (· ≤ ·)).filter (fun x => decide (p x)) := by
  apply (s.filter p).sortedLT_sort.eq_of_mem_iff
    (List.Pairwise.filter _ s.sortedLT_sort.pairwise).sortedLT
  intro x
  simp

/-- Increasing array enumeration equals a filtered scan of the vertices
when skipped vertices would produce empty records. -/
theorem ordered_vertex_records {β : Type} {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (f : Fin n → List β) (hskip : ∀ v, ¬ p v → f v = []) :
    let S := Finset.univ.filter p
    (List.finRange n).flatMap f =
      (List.ofFn (fun j : Fin S.card => f (S.orderIsoOfFin rfl j).val)).flatten := by
  dsimp only
  rw [ordered_records, sorted_selected, Fin.sort_univ]
  have hfilter (xs : List (Fin n)) : xs.flatMap f =
      (xs.filter (fun x => decide (p x))).flatMap f := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      by_cases hx : p x
      · simp [hx, List.flatMap_cons, ih]
      · simp [hx, hskip x hx, List.flatMap_cons, ih]
  exact hfilter _

private theorem prefix_flatMap (incoming outgoing : ℕ → ℕ) (n penalty k : ℕ) :
    initialAuxiliaryPrefix incoming outgoing n penalty k =
      (List.range k).flatMap (fun v => initialAuxiliaryWords v n (incoming v) (outgoing v) penalty) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [initialAuxiliaryPrefix,List.range_succ,List.flatMap_append,ih]
    simp

private theorem remove_zero_records {α : Type} (xs : List α) (incoming outgoing : α → ℕ)
    (f : α → List ℕ) (hz : ∀ x, incoming x = outgoing x → f x = []) :
    xs.flatMap f = (xs.filter (fun x => decide (incoming x ≠ outgoing x))).flatMap f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases he : incoming x = outgoing x
    · simp [he,hz x he,List.flatMap_cons,ih]
    · simp [he,List.flatMap_cons,ih]

/-- The emitted prefix enumerates exactly the nonzero-deficit vertices
in the same increasing order as the source's finite-set index map. -/
theorem initialAuxiliaryPrefix_ordered (incoming outgoing : ℕ → ℕ) (n penalty : ℕ) :
    let S := Finset.univ.filter (fun v : Fin n => incoming v ≠ outgoing v)
    initialAuxiliaryPrefix incoming outgoing n penalty n =
      (List.ofFn (fun j : Fin S.card =>
        let v := (S.orderIsoOfFin rfl j).val
        initialAuxiliaryWords v n (incoming v) (outgoing v) penalty)).flatten := by
  dsimp only
  let S := Finset.univ.filter (fun v : Fin n => incoming v ≠ outgoing v)
  let f := fun v : Fin n => initialAuxiliaryWords v n (incoming v) (outgoing v) penalty
  have hrange : List.range n = (List.finRange n).map Fin.val := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [prefix_flatMap,hrange,List.flatMap_map]
  change (List.finRange n).flatMap f =
    (List.ofFn (fun j : Fin S.card => f (S.orderIsoOfFin rfl j).val)).flatten
  rw [ordered_records S f]
  change (List.finRange n).flatMap f =
    (((Finset.univ.filter (fun v : Fin n => incoming v ≠ outgoing v)).sort (· ≤ ·)).map f).flatten
  rw [sorted_selected,Fin.sort_univ]
  have hh := remove_zero_records (List.finRange n) (fun v : Fin n => incoming v)
    (fun v => outgoing v) f (fun v hv => by simp [f,initialAuxiliaryWords,hv])
  simpa only [List.flatMap,Function.comp_apply] using hh

/-- The machine's selected vertex set is exactly `deficitVertices` on
the circulation instance. The integer difference loses no sign or half
unit when selecting the nonzero deficits. -/
theorem selected_vertices_eq_deficitVertices (J : Scaling.Circulation) :
    Finset.univ.filter (fun v : Fin J.n => incomingCapacity J v ≠ outgoingCapacity J v) =
      deficitVertices J.toInstance := by
  ext v
  simp [deficitVertices,twiceDeficit_eq_capacity_difference,sub_eq_zero]

/-- The actual auxiliary scan records agree, in order and field by field,
with the auxiliary part of `initialEdgeArray` in Lemma 4.12. -/
theorem initialAuxiliaryPrefix_eq_initial_stars (J : Scaling.Circulation) (penalty : ℕ) :
    initialAuxiliaryPrefix (incomingCapacity J) (outgoingCapacity J) J.n penalty J.n =
      (List.ofFn (fun j : Fin (deficitVertices J.toInstance).card =>
        let v := (deficitIndex J.toInstance j).val
        let e := starEdge J.n v (twiceDeficit J.toInstance v) penalty
        [e.tail,e.head,e.upper.toNat,0,penalty])).flatten := by
  have ho := initialAuxiliaryPrefix_ordered (incomingCapacity J) (outgoingCapacity J) J.n penalty
  dsimp only at ho
  rw [selected_vertices_eq_deficitVertices J] at ho
  refine ho.trans ?_
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  let v := (deficitIndex J.toInstance j).val
  have hv : v ∈ deficitVertices J.toInstance := (deficitIndex J.toInstance j).property
  have hz : twiceDeficit J.toInstance v ≠ 0 := (Finset.mem_filter.mp hv).2
  have hne : incomingCapacity J v ≠ outgoingCapacity J v := by
    intro he
    apply hz
    rw [twiceDeficit_eq_capacity_difference,he,sub_self]
  have hh := initialAuxiliaryWords_starEdge J.n v (incomingCapacity J v) (outgoingCapacity J v)
    penalty v.isLt hne
  rw [← twiceDeficit_eq_capacity_difference J v] at hh
  exact hh

end MinCostFlow.IPM.Machine
