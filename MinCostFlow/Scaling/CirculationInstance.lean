module

public import MinCostFlow.Scaling.Circulation
public import MinCostFlow.Statement.Problem

/-!
# Circulation as an input flow instance

Appendix C of Chen et al., arXiv:2203.00671v2, uses minimum-cost circulation
as the zero-demand special case of general minimum-cost flow. This file gives
the conversion to `Instance` and proves that its feasible flows and objective
are exactly those of the circulation. The edge index map preserves edge numbers.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Store a circulation edge using the general problem's edge format. -/
def inputEdge (I : Circulation) (e : Fin I.m) : Edge where
  tail := I.tail e
  head := I.head e
  lower := 0
  upper := I.capacity e
  cost := I.cost e

/-- The zero-demand flow instance representing a circulation. -/
abbrev toInstance (I : Circulation) : Instance where
  n := I.n
  edges := List.ofFn I.inputEdge
  demand := List.replicate I.n 0

/-- Conversion preserves the number of edges. -/
theorem toInstance_m (I : Circulation) : I.toInstance.m = I.m := by
  simp [Instance.m]

/-- The explicit index map preserves the index value. -/
def inputIndex (I : Circulation) : Fin I.toInstance.m ≃ Fin I.m :=
  finCongr I.toInstance_m

/-- The converted edge at index `e` is exactly the original edge at its index map. -/
theorem toInstance_edge (I : Circulation) (e : Fin I.toInstance.m) :
    I.toInstance.edge e = I.inputEdge (I.inputIndex e) := by
  change (List.ofFn I.inputEdge)[e.val] = I.inputEdge (I.inputIndex e)
  rw [List.getElem_ofFn]
  congr 1

/-- The conversion always produces a well-formed instance. -/
theorem toInstance_valid (I : Circulation) : I.toInstance.IsValid := by
  constructor
  · intro e he
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
    exact ⟨(I.tail j).isLt, (I.head j).isLt⟩
  · simp

/-- Convert a flow by the edge index map. -/
def inputFlow (I : Circulation) (f : Fin I.m → ℝ) : Fin I.toInstance.m → ℝ :=
  fun e => f (I.inputIndex e)

private theorem sum_inputIndex (I : Circulation) (a : Fin I.m → ℝ) :
    (∑ e : Fin I.toInstance.m, a (I.inputIndex e)) = ∑ e, a e := by
  exact Equiv.sum_comp I.inputIndex a

/-- The zero demands in the converted instance are exactly conservation. -/
theorem toInstance_routes_iff (I : Circulation) (f : Fin I.m → ℝ) :
    I.toInstance.Routes (I.inputFlow f) ↔ I.Conserves f := by
  have hi : ∀ (e : Fin I.m) (v : Fin I.n), (I.inputEdge e).b v = I.incidence e v := by
    intro e v
    simp [inputEdge, Edge.b, incidence, Fin.ext_iff]
    rfl
  have hb : ∀ v : Fin I.n,
      (∑ e : Fin I.toInstance.m, (I.toInstance.edge e).b v * I.inputFlow f e) =
        I.balance f v := by
    intro v
    simp only [toInstance_edge, inputFlow]
    simp only [hi]
    exact I.sum_inputIndex (fun e => I.incidence e v * f e)
  have hz : ∀ v : Fin I.n, I.toInstance.d v = 0 := by
    intro v
    simp [Instance.d]
  constructor
  · intro hf v
    have h := hf v
    rw [hb, hz, Int.cast_zero] at h
    exact h
  · intro hf v
    change (∑ e, (I.toInstance.edge e).b v * I.inputFlow f e) = _
    rw [hb, hf v]
    simp [Instance.d]

/-- Feasibility is preserved in both directions, against real flows. -/
theorem toInstance_feasible_iff (I : Circulation) (f : Fin I.m → ℝ) :
    I.toInstance.IsFeasible (I.inputFlow f) ↔ I.Feasible f := by
  unfold Instance.IsFeasible Feasible
  rw [toInstance_routes_iff]
  apply and_congr_right
  intro _
  constructor
  · intro h e
    have he := h (I.inputIndex.symm e)
    simpa only [toInstance_edge, inputFlow, Equiv.apply_symm_apply, inputEdge,
      Int.cast_zero, Int.cast_natCast] using he
  · intro h e
    simpa only [toInstance_edge, inputFlow, inputEdge, Int.cast_zero,
      Int.cast_natCast] using h (I.inputIndex e)

/-- The conversion preserves the objective without any additive constant. -/
theorem toInstance_cost (I : Circulation) (f : Fin I.m → ℝ) :
    I.toInstance.cost (I.inputFlow f) = I.objective f := by
  unfold Instance.cost
  simp only [toInstance_edge, inputFlow, inputEdge]
  exact I.sum_inputIndex (fun e => (I.cost e : ℝ) * f e)

/-- Exact minimum-cost flow and exact minimum-cost circulation agree under
the explicit edge index map `inputIndex`. -/
theorem toInstance_minCostFlow_iff (I : Circulation) (f : Fin I.m → ℝ) :
    I.toInstance.IsMinCostFlow (I.inputFlow f) ↔ I.Optimal f := by
  constructor
  · intro hf
    refine ⟨(I.toInstance_feasible_iff f).mp hf.1, ?_⟩
    intro g hg
    have hc := hf.2 (I.inputFlow g) ((I.toInstance_feasible_iff g).mpr hg)
    simpa only [toInstance_cost] using hc
  · intro hf
    refine ⟨(I.toInstance_feasible_iff f).mpr hf.1, ?_⟩
    intro g hg
    let h : Fin I.m → ℝ := fun e => g (I.inputIndex.symm e)
    have he : I.inputFlow h = g := by
      funext e
      exact congrArg g (I.inputIndex.symm_apply_apply e)
    have hh : I.Feasible h := (I.toInstance_feasible_iff h).mp (he.symm ▸ hg)
    have hc := hf.2 h hh
    rw [← I.toInstance_cost f, ← I.toInstance_cost h, he] at hc
    exact hc

end MinCostFlow.Scaling.Circulation
