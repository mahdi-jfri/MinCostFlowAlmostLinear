module

public import MinCostFlow.LowStretch.PSums
public import MinCostFlow.LowStretch.ProgCSR

/-!
# Sums over the arcs of a node

In the petal graph the arcs of node `u` are the items with tail `u`, grouped by `csrB`, and then
the slot of `u`. A sum over the arcs of `u` before its slot is a sum over the items with tail `u`
(`csr_sum`), so by `sum_items` a sum over the entries at `u`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open Classical

theorem sum_range_getD (l : List ℕ) (G : ℕ → ℕ) :
    ∑ i ∈ Finset.range l.length, G (l.getD i 0) = (l.map G).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih, List.map_cons, List.sum_cons]
    omega

/-- A sum over the list of the items below `M` with a property is a sum over the finite set. -/
theorem sum_grp (M : ℕ) (p : ℕ → Prop) [DecidablePred p] (G : ℕ → ℕ) :
    ∑ i ∈ Finset.range ((List.range M).filter (fun o => decide (p o))).length,
        G (((List.range M).filter (fun o => decide (p o))).getD i 0) =
      ∑ o ∈ (Finset.range M).filter p, G o := by
  rw [sum_range_getD, ← List.sum_toFinset G ((List.nodup_range).filter _)]
  congr 1
  ext o
  simp

/-- **The arcs of `u` before its slot.** Here `ord` is the order of `csrB`, item `2j` of the pair
items goes from `ea j` to `eb j` (head `hdA`), item `2j + 1` back, and item `2nA + u` is the slot
of `u`. -/
theorem csr_sum {f ord hdA ea eb : ℕ → ℕ} {nA s u : ℕ}
    (hord : ∀ j < (grp f (2 * nA + s) u).length,
      ord (offOf f (2 * nA + s) u + j) = (grp f (2 * nA + s) u).getD j 0)
    (hg : grp f (2 * nA + s) u = grp f (2 * nA) u ++ [2 * nA + u])
    (hf : ∀ o < 2 * nA, f o = itl ea eb o) (hh : ∀ o < 2 * nA, hdA o = ihd ea eb o)
    (F : ℕ → ℕ → ℕ) :
    ∑ k ∈ Finset.Ico (offOf f (2 * nA + s) u) (offOf f (2 * nA + s) (u + 1) - 1),
        F (hdA (ord k)) (ord k / 2) =
      ∑ j ∈ (Finset.range nA).filter (ea · = u), F (eb j) j +
      ∑ j ∈ (Finset.range nA).filter (eb · = u), F (ea j) j := by
  set g := grp f (2 * nA) u with hgdef
  have hlen : (grp f (2 * nA + s) u).length = g.length + 1 := by rw [hg]; simp
  rw [offOf_succ, hlen, show offOf f (2 * nA + s) u + (g.length + 1) - 1 =
    offOf f (2 * nA + s) u + g.length by omega, Finset.sum_Ico_eq_sum_range,
    show offOf f (2 * nA + s) u + g.length - offOf f (2 * nA + s) u = g.length by omega]
  have hmem : ∀ i < g.length, g.getD i 0 < 2 * nA := by
    intro i hi
    have : g.getD i 0 ∈ g := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    simp only [hgdef, grp, List.mem_filter, List.mem_range] at this
    exact this.1
  have e1 : ∀ i ∈ Finset.range g.length,
      F (hdA (ord (offOf f (2 * nA + s) u + i))) (ord (offOf f (2 * nA + s) u + i) / 2) =
        (fun o => F (ihd ea eb o) (o / 2)) (g.getD i 0) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have ho := hord i (by omega)
    rw [hg, List.getD_append _ _ _ _ hi'] at ho
    rw [ho, hh _ (hmem i hi')]
  rw [Finset.sum_congr rfl e1]
  have hgf : g = (List.range (2 * nA)).filter (fun o => decide (itl ea eb o = u)) := by
    simp only [hgdef, grp]
    apply List.filter_congr
    intro o ho
    rw [hf o (List.mem_range.mp ho)]
  rw [hgf]
  exact (sum_grp (2 * nA) (fun o => itl ea eb o = u) (fun o => F (ihd ea eb o) (o / 2))).trans
    (sum_items ea eb nA u F)

end MinCostFlow.LowStretch
