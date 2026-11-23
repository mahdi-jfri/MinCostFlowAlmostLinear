module

public import MinCostFlow.LSF.Program.CongScatter
public import MinCostFlow.LSF.Program.T0Rooted
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

/-!
# The congestion keys

`congScatterProc` puts, for each graph edge `t`, the value `q t` at both endpoints and `-2 q t`
at their lowest common ancestor; `subtreeSumProc` then sums over subtrees. Here we show what
comes out at a vertex `y`:

* `subtree_scatter_sum`: the subtree sum at `y` is the sum of `q t` over the edges with exactly
  one endpoint below `y` (`congKey`). An endpoint pair with both ends below `y` has its lowest
  common ancestor below `y` too, so its three terms cancel.
* `congKey_eq_sum`: when the arrays describe `(T₀, r₀)` and `y ≠ r`, these are the edges whose
  tree path uses the parent edge of `y` (`parentEdge_mem_walkEdges_iff`). So the key of `y` is
  the floored congestion sum of the parent edge of `y` that `approxCongOrder_of_floor` sorts by.
-/

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF

@[expose] public section

open Classical in
/-- The key of vertex `y`: the sum of `q t` over the edges `t` with exactly one endpoint below
`y`. -/
noncomputable def congKey (par dep : ℕ → ℕ) (eu ev q : ℕ → ℕ) (m0 y : ℕ) : ℕ :=
  ∑ t ∈ Finset.range m0,
    if (AncOf par dep y (eu t) ↔ AncOf par dep y (ev t)) then 0 else q t

lemma congKey_le (par dep : ℕ → ℕ) (eu ev q : ℕ → ℕ) (m0 y : ℕ) :
    congKey par dep eu ev q m0 y ≤ ∑ t ∈ Finset.range m0, q t := by
  unfold congKey
  exact Finset.sum_le_sum fun t _ => by split_ifs <;> omega

/-- The key only depends on the arrays at the indices that matter. -/
lemma congKey_congr {n tM r : ℕ} {tl hd par pe dep par' dep' : ℕ → ℕ}
    (hR : RootedArrays n tM r tl hd par pe dep) {m0 : ℕ} {eu ev q eu' ev' q' : ℕ → ℕ}
    (hpar : ∀ x < n, par x = par' x) (hdep : ∀ x < n, dep x = dep' x)
    (hends : ∀ t < m0, eu t < n ∧ ev t < n) (heu : ∀ t < m0, eu t = eu' t)
    (hev : ∀ t < m0, ev t = ev' t) (hq : ∀ t < m0, q t = q' t) (y : ℕ) :
    congKey par dep eu ev q m0 y = congKey par' dep' eu' ev' q' m0 y := by
  unfold congKey
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  rw [ancOf_congr hpar hdep hR.par_lt (hends t ht).1, ancOf_congr hpar hdep hR.par_lt
    (hends t ht).2, heu t ht, hev t ht, hq t ht]

/-- The subtree sum of the scattered values at `y` is the key of `y`. -/
theorem subtree_scatter_sum {n tM r : ℕ} {tl hd par pe dep : ℕ → ℕ}
    (hR : RootedArrays n tM r tl hd par pe dep) {m0 : ℕ} {eu ev lc q : ℕ → ℕ}
    (hends : ∀ t < m0, eu t < n ∧ ev t < n)
    (hlc : ∀ t < m0, IsLcaOf par dep (lc t) (eu t) (ev t) ∧ lc t < n) (y : ℕ) :
    (open Classical in ∑ z ∈ Finset.range n,
      if AncOf par dep y z then
        ∑ t ∈ Finset.range m0, (q t : ℤ) * scatterWeight eu ev lc t z else 0) =
      (congKey par dep eu ev q m0 y : ℤ) := by
  classical
  -- one indicator summed over the subtree
  have hone : ∀ a < n, (∑ z ∈ Finset.range n,
      if AncOf par dep y z then (if a = z then (1 : ℤ) else 0) else 0) =
      if AncOf par dep y a then 1 else 0 := by
    intro a ha
    rw [Finset.sum_congr rfl (fun z _ => show (if AncOf par dep y z then
        (if a = z then (1 : ℤ) else 0) else 0) = if a = z then (if AncOf par dep y z then 1 else 0)
        else 0 by split_ifs <;> simp_all)]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr ha)]
  have hswap : (∑ z ∈ Finset.range n,
      if AncOf par dep y z then
        ∑ t ∈ Finset.range m0, (q t : ℤ) * scatterWeight eu ev lc t z else 0) =
      ∑ t ∈ Finset.range m0, (q t : ℤ) * ∑ z ∈ Finset.range n,
        if AncOf par dep y z then scatterWeight eu ev lc t z else 0 := by
    rw [Finset.sum_congr rfl (fun z _ => show (if AncOf par dep y z then
        ∑ t ∈ Finset.range m0, (q t : ℤ) * scatterWeight eu ev lc t z else 0) =
        ∑ t ∈ Finset.range m0, (q t : ℤ) * (if AncOf par dep y z then
          scatterWeight eu ev lc t z else 0) by
      split_ifs <;> simp)]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun t _ => by rw [Finset.mul_sum]
  rw [hswap, congKey]
  push_cast
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  obtain ⟨hu, hv⟩ := hends t ht
  obtain ⟨hl, hln⟩ := hlc t ht
  have hsplit : (∑ z ∈ Finset.range n, if AncOf par dep y z then scatterWeight eu ev lc t z
      else 0) =
      (∑ z ∈ Finset.range n, if AncOf par dep y z then (if eu t = z then (1 : ℤ) else 0) else 0) +
      (∑ z ∈ Finset.range n, if AncOf par dep y z then (if ev t = z then (1 : ℤ) else 0) else 0) -
      2 * (∑ z ∈ Finset.range n, if AncOf par dep y z then (if lc t = z then (1 : ℤ) else 0)
        else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    unfold scatterWeight
    split_ifs <;> ring
  rw [hsplit, hone _ hu, hone _ hv, hone _ hln]
  -- the ancestor of both endpoints are the ancestors of the lowest common ancestor
  have hlca : AncOf par dep y (lc t) ↔ AncOf par dep y (eu t) ∧ AncOf par dep y (ev t) :=
    ⟨fun h => ⟨h.trans hR hu hl.1, h.trans hR hv hl.2.1⟩, fun ⟨h1, h2⟩ => hl.2.2 y h1 h2⟩
  by_cases h1 : AncOf par dep y (eu t) <;> by_cases h2 : AncOf par dep y (ev t) <;>
    simp [h1, h2, hlca]

/-- A value modulo the capacity that is known to be in range is exact. -/
lemma eq_of_emod_eq {u S c : ℕ} (hu : u < c) (hS : S < c)
    (h : (u : ℤ) % (c : ℤ) = (S : ℤ) % (c : ℤ)) : u = S := by
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at h
  exact_mod_cast h

/-- A sum over the positions of a list is the sum over its entries. -/
lemma sum_range_getD {α : Type*} [AddCommMonoid α] (g : ℕ → α) :
    ∀ l : List ℕ, ∑ t ∈ Finset.range l.length, g (l.getD t 0) = (l.map g).sum
  | [] => by simp
  | a :: l => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons,
      ← sum_range_getD g l]
    simp [add_comm]

/-- The key of `y ≠ r` is the sum of `Q e` over the graph edges `e` whose tree path uses the
parent edge of `y`. -/
theorem congKey_eq_sum {G₀ T₀ : MGraph} {vList eList : List ℕ} {tM r : ℕ}
    {fid tl hd par pe dep : ℕ → ℕ} {eu ev : ℕ → ℕ} {Q : ℕ → ℕ}
    (hT₀ : IsRootedTree T₀ (vList.getD r 0))
    (hA : T0IndexArrays T₀ vList tM fid tl hd) (hnd : vList.Nodup)
    (hR : RootedArrays vList.length tM r tl hd par pe dep) (hr : r < vList.length)
    (hVT : ∀ i < vList.length, vList.getD i 0 ∈ T₀.V)
    (hend : eList.Nodup) (hEl : ∀ e, e ∈ eList ↔ e ∈ G₀.E)
    (heu : ∀ t < eList.length, eu t < vList.length ∧
      vList.getD (eu t) 0 = G₀.tail (eList.getD t 0))
    (hev : ∀ t < eList.length, ev t < vList.length ∧
      vList.getD (ev t) 0 = G₀.head (eList.getD t 0))
    {y : ℕ} (hy : y < vList.length) (hyr : y ≠ r) :
    congKey par dep eu ev (fun t => Q (eList.getD t 0)) eList.length y =
      (open Classical in ∑ e ∈ G₀.E,
        if fid (pe y) ∈ walkEdges (T₀.forestPath (G₀.tail e) (G₀.head e)) then Q e else 0) := by
  classical
  have hyV := hVT y hy
  have hVyr : vList.getD y 0 ≠ vList.getD r 0 := by
    intro h
    rw [List.getD_eq_getElem _ _ hy, List.getD_eq_getElem _ _ hr] at h
    exact hyr ((hnd.getElem_inj_iff).mp h)
  have hpe : parentEdge T₀ (vList.getD r 0) (vList.getD y 0) = fid (pe y) :=
    ((t0Rooted_spec hT₀.isForest hA hnd hR hr hy).2 hyr).2
  have hGE : G₀.E = eList.toFinset := by ext e; simp [hEl]
  rw [hGE, List.sum_toFinset _ hend, ← sum_range_getD, congKey]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  obtain ⟨hu, hut⟩ := heu t ht
  obtain ⟨hv, hvt⟩ := hev t ht
  rw [← hut, ← hvt, ← hpe]
  have hiff := parentEdge_mem_walkEdges_iff hT₀ hyV hVyr (hVT _ hu) (hVT _ hv)
  rw [t0Rooted_isAncestor_iff hT₀.isForest hA hnd hR hr hu hy,
    t0Rooted_isAncestor_iff hT₀.isForest hA hnd hR hr hv hy] at hiff
  unfold AncOf
  by_cases hc : (∃ k ≤ dep (eu t), par^[k] (eu t) = y) ↔ (∃ k ≤ dep (ev t), par^[k] (ev t) = y)
  · rw [if_pos hc, if_neg (fun h => (hiff.mp h) hc)]
  · rw [if_neg hc, if_pos (hiff.mpr hc)]

end

end MinCostFlow.LSF.Program
