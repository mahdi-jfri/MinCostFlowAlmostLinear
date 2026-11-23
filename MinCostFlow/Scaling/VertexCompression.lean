module

public import MinCostFlow.Scaling.Circulation
public import MinCostFlow.Scaling.VertexLabels

/-!
# Removing isolated vertices of a circulation

The call-size analysis in Appendix C of Chen et al., arXiv:2203.00671v2,
uses a vertex bound in terms of the number of edges. Scan edge endpoints once,
assigning consecutive positive labels. The resulting graph has at most `2*m`
vertices and exactly the same edges, capacities, costs, and flow vectors. This
file proves that feasibility and exact optimality are preserved in both directions.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- The endpoint scan reads each original edge's tail and head once. -/
def endpoints (I : Circulation) : List (Fin I.n) :=
  List.ofFn I.tail ++ List.ofFn I.head

/-- Consecutive positive labels on precisely the encountered endpoints. -/
def endpointLabels (I : Circulation) : VertexLabels I.n :=
  (VertexLabels.empty I.n).scan I.endpoints

/-- The computed table has bounded and unique positive labels. -/
theorem endpointLabels_valid (I : Circulation) : I.endpointLabels.Valid :=
  VertexLabels.scan_valid _ (VertexLabels.empty_valid _) _

/-- The endpoint scan has exactly twice as many entries as edges. -/
theorem endpoints_length (I : Circulation) : I.endpoints.length = 2 * I.m := by
  simp [endpoints, Nat.two_mul]

/-- There are at most twice as many assigned vertices as edges. -/
theorem endpointLabels_count_le (I : Circulation) : I.endpointLabels.count ≤ 2 * I.m := by
  have h := (VertexLabels.empty I.n).scan_count_le I.endpoints
  simpa only [endpointLabels, VertexLabels.empty, zero_add, endpoints_length] using h

/-- Every tail has been assigned a positive label. -/
theorem tail_label_pos (I : Circulation) (e : Fin I.m) :
    0 < I.endpointLabels.table (I.tail e) := by
  apply VertexLabels.scan_mem_pos
  apply List.mem_append_left
  exact List.mem_ofFn.mpr ⟨e, rfl⟩

/-- Every head has been assigned a positive label. -/
theorem head_label_pos (I : Circulation) (e : Fin I.m) :
    0 < I.endpointLabels.table (I.head e) := by
  apply VertexLabels.scan_mem_pos
  apply List.mem_append_right
  exact List.mem_ofFn.mpr ⟨e, rfl⟩

/-- The map from an encountered vertex to its consecutive zero-based index. -/
def encodeVertex (I : Circulation) (v : Fin I.n)
    (hv : 0 < I.endpointLabels.table v) : Fin I.endpointLabels.count :=
  ⟨I.endpointLabels.table v - 1, by
    have h := I.endpointLabels_valid.1 v
    omega⟩

/-- Equality of assigned indices is exactly equality of the original vertices. -/
theorem encodeVertex_eq_iff (I : Circulation) (v w : Fin I.n)
    (hv : 0 < I.endpointLabels.table v) (hw : 0 < I.endpointLabels.table w) :
    I.encodeVertex v hv = I.encodeVertex w hw ↔ v = w := by
  constructor
  · intro h
    have he := congrArg Fin.val h
    have ht : I.endpointLabels.table v = I.endpointLabels.table w := by
      dsimp only [encodeVertex] at he
      omega
    exact I.endpointLabels_valid.2 v w (Nat.ne_of_gt hv) ht
  · intro h
    subst w
    rfl

/-- The circulation after discarding isolated vertices and relabeling endpoints. -/
abbrev compress (I : Circulation) : Circulation where
  n := I.endpointLabels.count
  m := I.m
  tail := fun e => I.encodeVertex (I.tail e) (I.tail_label_pos e)
  head := fun e => I.encodeVertex (I.head e) (I.head_label_pos e)
  capacity := I.capacity
  cost := I.cost

/-- Net flow at an assigned vertex is unchanged by relabeling. -/
theorem compress_balance (I : Circulation) (f : Fin I.m → ℝ) (v : Fin I.n)
    (hv : 0 < I.endpointLabels.table v) :
    I.compress.balance f (I.encodeVertex v hv) = I.balance f v := by
  classical
  apply Finset.sum_congr rfl
  intro e _
  simp only [incidence, compress, encodeVertex_eq_iff]

/-- Conservation holds before compression exactly when it holds afterwards.
Unassigned original vertices have no incident edges and hence zero net flow. -/
theorem compress_conserves_iff (I : Circulation) (f : Fin I.m → ℝ) :
    I.compress.Conserves f ↔ I.Conserves f := by
  classical
  constructor
  · intro h v
    by_cases hv : 0 < I.endpointLabels.table v
    · rw [← I.compress_balance f v hv]
      exact h _
    · apply Finset.sum_eq_zero
      intro e _
      have ht : v ≠ I.tail e := by
        intro he
        subst v
        exact hv (I.tail_label_pos e)
      have hh : v ≠ I.head e := by
        intro he
        subst v
        exact hv (I.head_label_pos e)
      simp [incidence, ht, hh]
  · intro h k
    by_cases hk : ∃ v : Fin I.n, ∃ hv : 0 < I.endpointLabels.table v,
        I.encodeVertex v hv = k
    · obtain ⟨v, hv, rfl⟩ := hk
      rw [compress_balance]
      exact h v
    · apply Finset.sum_eq_zero
      intro e _
      have ht : k ≠ I.encodeVertex (I.tail e) (I.tail_label_pos e) := by
        intro he
        exact hk ⟨I.tail e, I.tail_label_pos e, he.symm⟩
      have hh : k ≠ I.encodeVertex (I.head e) (I.head_label_pos e) := by
        intro he
        exact hk ⟨I.head e, I.head_label_pos e, he.symm⟩
      simp [incidence, compress, ht, hh]

/-- Relabeling preserves all primal feasibility constraints. -/
theorem compress_feasible_iff (I : Circulation) (f : Fin I.m → ℝ) :
    I.compress.Feasible f ↔ I.Feasible f := by
  exact and_congr (I.compress_conserves_iff f) Iff.rfl

/-- Relabeling preserves exact optimality against every real comparison flow. -/
theorem compress_optimal_iff (I : Circulation) (f : Fin I.m → ℝ) :
    I.compress.Optimal f ↔ I.Optimal f := by
  constructor
  · intro h
    exact ⟨(I.compress_feasible_iff f).mp h.1,
      fun g hg => h.2 g ((I.compress_feasible_iff g).mpr hg)⟩
  · intro h
    exact ⟨(I.compress_feasible_iff f).mpr h.1,
      fun g hg => h.2 g ((I.compress_feasible_iff g).mp hg)⟩

/-- The endpoint scan uses at most ten table/control operations per edge.
Initializing the table adds `n` stores once, before any scaling iterations. -/
theorem endpoint_scan_work_le (I : Circulation) :
    ((VertexLabels.empty I.n).scanWithWork I.endpoints).2 ≤ 10 * I.m := by
  have h := (VertexLabels.empty I.n).scanWithWork_bound I.endpoints
  rw [endpoints_length] at h
  simpa only [← Nat.mul_assoc] using h

end MinCostFlow.Scaling.Circulation
