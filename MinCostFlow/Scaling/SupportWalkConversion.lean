module

public import MinCostFlow.Scaling.SupportCycle

/-!
# Interpreting support walks in the original graph

The cycle decomposition used by capacity scaling in Appendix C of Chen et al.,
arXiv:2203.00671v2, consists of cycles of the original graph. A walk of the
positive support has the same endpoints and edge indices. If the underlying
flow is feasible, every one of those arcs has positive original capacity.
The conversion preserves all edge counts, costs, and lengths.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation
namespace DirectedWalk
variable {I : Circulation} {f : Fin I.m → ℝ}

/-- Retain the edges of a support walk and justify their original capacities. -/
def ofPositiveSupport (hf : I.Feasible f) {a b : Fin I.n} :
    (I.positiveSupport f).DirectedWalk a b → I.DirectedWalk a b
  | .nil v => DirectedWalk.nil (I := I) v
  | .cons e he p =>
    DirectedWalk.cons (I := I) e (by
      have hpos : 0 < f e := by
        change 0 < if 0 < f e then 1 else 0 at he
        split at he
        · assumption
        · contradiction
      have hcap : (0 : ℝ) < I.capacity e := lt_of_lt_of_le hpos (hf.2 e).2
      exact_mod_cast hcap) (ofPositiveSupport hf p)

/-- Conversion preserves each arc's number of occurrences. -/
theorem count_ofPositiveSupport (hf : I.Feasible f) {a b : Fin I.n}
    (p : (I.positiveSupport f).DirectedWalk a b) (e : Fin I.m) :
    (p.ofPositiveSupport hf).count e = p.count e := by
  induction p using DirectedWalk.rec (I := I.positiveSupport f) with
  | nil => rfl
  | cons k hk p ih => simp only [ofPositiveSupport, count, ih]

/-- Conversion preserves walk length. -/
theorem length_ofPositiveSupport (hf : I.Feasible f) {a b : Fin I.n}
    (p : (I.positiveSupport f).DirectedWalk a b) :
    (p.ofPositiveSupport hf).length = p.length := by
  induction p using DirectedWalk.rec (I := I.positiveSupport f) with
  | nil => rfl
  | cons k hk p ih => simp only [ofPositiveSupport, length, ih]

/-- Every used edge of a support walk has positive underlying flow. -/
theorem flow_pos_of_support_count (_hf : I.Feasible f) {a b : Fin I.n}
    (p : (I.positiveSupport f).DirectedWalk a b) (e : Fin I.m) (he : 0 < p.count e) :
    0 < f e := by
  have hh := p.active_of_count_pos e he
  change 0 < if 0 < f e then 1 else 0 at hh
  split at hh
  · assumption
  · contradiction

end DirectedWalk
end MinCostFlow.Scaling.Circulation
