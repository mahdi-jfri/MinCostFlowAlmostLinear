module

public import MinCostFlow.IPM.Definitions
public import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases

/-!
# Indexed instance constructions for initialization

Lemma 4.12 (page 31) constructs new instances and flows. These helpers package
finite indexed edge and demand arrays as the lists used by `Instance`.
The edge-index equivalence explicitly transports flows, cost, and routing
between the array description and the resulting instance.
-/

@[expose] public section
namespace MinCostFlow.IPM

/-- An instance described by indexed edges and integral demands. -/
def instanceOfArrays (n m : ℕ) (edges : Fin m → Edge) (demands : Fin n → ℤ) : Instance :=
  ⟨n, List.ofFn edges, List.ofFn demands⟩

/-- The constructed instance has the requested number of edges. -/
theorem instanceOfArrays_m (n m : ℕ) (edges : Fin m → Edge) (demands : Fin n → ℤ) :
    (instanceOfArrays n m edges demands).m = m := by
  simp only [instanceOfArrays, Instance.m, List.length_ofFn]

/-- The edge-index map from the list representation to the array representation. -/
def arrayIndex {n m : ℕ} (edges : Fin m → Edge) (demands : Fin n → ℤ) :
    Fin (instanceOfArrays n m edges demands).m ≃ Fin m :=
  finCongr (instanceOfArrays_m n m edges demands)

/-- The edge data agree under the edge-index map. -/
theorem instanceOfArrays_edge {n m : ℕ} (edges : Fin m → Edge) (demands : Fin n → ℤ)
    (e : Fin (instanceOfArrays n m edges demands).m) :
    (instanceOfArrays n m edges demands).edge e = edges (arrayIndex edges demands e) := by
  simp only [Instance.edge, instanceOfArrays, List.getElem_ofFn]
  rfl

/-- The demand data agree at each original vertex. -/
theorem instanceOfArrays_d {n m : ℕ} (edges : Fin m → Edge) (demands : Fin n → ℤ) (v : Fin n) :
    (instanceOfArrays n m edges demands).d v = demands v := by
  rw [Instance.d, List.getD_eq_getElem _ _ (by simp only [instanceOfArrays, List.length_ofFn]; exact v.2)]
  simp only [instanceOfArrays, List.getElem_ofFn]

/-- Transport an array flow to the constructed instance. -/
def flowOfArray {n m : ℕ} (edges : Fin m → Edge) (demands : Fin n → ℤ)
    (f : Fin m → ℝ) : Fin (instanceOfArrays n m edges demands).m → ℝ :=
  fun e => f (arrayIndex edges demands e)

/-- Transport a flow on the constructed instance back to array coordinates. -/
def flowToArray {n m : ℕ} (edges : Fin m → Edge) (demands : Fin n → ℤ)
    (f : Fin (instanceOfArrays n m edges demands).m → ℝ) : Fin m → ℝ :=
  fun e => f ((arrayIndex edges demands).symm e)

/-- The two flow transports are inverse. -/
theorem flowOfArray_flowToArray {n m : ℕ} (edges : Fin m → Edge) (demands : Fin n → ℤ)
    (f : Fin (instanceOfArrays n m edges demands).m → ℝ) :
    flowOfArray edges demands (flowToArray edges demands f) = f := by
  funext e
  simp only [flowOfArray, flowToArray, Equiv.symm_apply_apply]

/-- Cost of the transported flow is the array dot product. -/
theorem cost_flowOfArray {n m : ℕ} (edges : Fin m → Edge) (demands : Fin n → ℤ)
    (f : Fin m → ℝ) :
    (instanceOfArrays n m edges demands).cost (flowOfArray edges demands f) =
      ∑ e, (edges e).cost*f e := by
  simp only [Instance.cost, instanceOfArrays_edge, flowOfArray]
  exact (arrayIndex edges demands).sum_comp (fun e => ((edges e).cost : ℝ)*f e)

/-- Routing of the transported flow is exactly the array incidence equation. -/
theorem routes_flowOfArray_iff {n m : ℕ} (edges : Fin m → Edge) (demands : Fin n → ℤ)
    (f : Fin m → ℝ) :
    (instanceOfArrays n m edges demands).Routes (flowOfArray edges demands f) ↔
      ∀ v : Fin n, ∑ e, (edges e).b v*f e = (demands v : ℝ) := by
  change (∀ v : Fin n, ∑ e, ((instanceOfArrays n m edges demands).edge e).b v *
      flowOfArray edges demands f e = ((instanceOfArrays n m edges demands).d v : ℝ)) ↔ _
  apply forall_congr'
  intro v
  rw [instanceOfArrays_d]
  simp only [instanceOfArrays_edge, flowOfArray]
  rw [(arrayIndex edges demands).sum_comp (fun e => (edges e).b v*f e)]

/-- Capacity feasibility of the transported flow is exactly the array
capacity condition together with the array routing equation. -/
theorem feasible_flowOfArray_iff {n m : ℕ} (edges : Fin m → Edge) (demands : Fin n → ℤ)
    (f : Fin m → ℝ) :
    (instanceOfArrays n m edges demands).IsFeasible (flowOfArray edges demands f) ↔
      (∀ v : Fin n, ∑ e, (edges e).b v*f e = (demands v : ℝ)) ∧
      ∀ e, ((edges e).lower : ℝ) ≤ f e ∧ f e ≤ (edges e).upper := by
  rw [Instance.IsFeasible, routes_flowOfArray_iff]
  simp only [instanceOfArrays_edge, flowOfArray]
  exact and_congr_right fun _ => (arrayIndex edges demands).forall_congr_left

/-- The array instance is valid when every edge endpoint is a vertex. -/
theorem valid_instanceOfArrays {n m : ℕ} (edges : Fin m → Edge) (demands : Fin n → ℤ)
    (he : ∀ j, (edges j).tail < n ∧ (edges j).head < n) :
    (instanceOfArrays n m edges demands).IsValid := by
  constructor
  · intro e hm
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hm
    exact he j
  · exact List.length_ofFn

end MinCostFlow.IPM
