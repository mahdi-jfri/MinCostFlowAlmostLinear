module

public import MinCostFlow.IPM.InitialDomain
public import MinCostFlow.IPM.NamedInstance
public import MinCostFlow.Basic.Forest
import MinCostFlow.IPM.InitialRouting
import MinCostFlow.LSF.Walks
import Mathlib.Tactic

/-!
# A connected augmentation

Lemma 4.12 (page 31, Appendix B.1 page 92 of Chen et al., arXiv:2203.00671v2)
adds a hub edge at each nonzero deficit. To supply the spanning tree of
Lemma 5.4 (page 17), add two opposite hub edges at each zero deficit.
Their midpoint flows cancel at both ends.
-/

noncomputable section
@[expose] public section
namespace MinCostFlow.IPM

/-- The vertices that did not receive an edge in the deficit construction. -/
def zeroDeficitVertices (I : Instance) : Finset (Fin I.n) :=
  Finset.univ.filter fun v => twiceDeficit I v = 0

/-- The increasing enumeration of zero-deficit vertices. -/
def zeroDeficitIndex (I : Instance) :
    Fin (zeroDeficitVertices I).card ≃ {v // v ∈ zeroDeficitVertices I} :=
  ((zeroDeficitVertices I).orderIsoOfFin rfl).toEquiv

/-- Append one block of outgoing hub edges and one block of incoming hub edges. -/
def connectedInitialEdgeArray (I : Instance) (K : ℤ) :
    Fin (((freeEdges I).card + (deficitVertices I).card) +
      ((zeroDeficitVertices I).card + (zeroDeficitVertices I).card)) → Edge :=
  Fin.addCases (initialEdgeArray I K)
    (Fin.addCases (fun j => starEdge I.n (zeroDeficitIndex I j).1 2 K)
      (fun j => starEdge I.n (zeroDeficitIndex I j).1 (-2) K))

/-- The connected version of the auxiliary-vertex instance. -/
def connectedInitialInstance (I : Instance) (K : ℤ) : Instance :=
  instanceOfArrays (I.n+1) _ (connectedInitialEdgeArray I K) (initialDemands I)

/-- The old midpoint flow extended by one unit on both edges of every pair. -/
def connectedInitialFlow (I : Instance) (K : ℤ) :
    Fin (connectedInitialInstance I K).m → ℝ :=
  flowOfArray (connectedInitialEdgeArray I K) (initialDemands I)
    (Fin.addCases (initialArrayFlow I) (fun _ => 1))

/-- Each vertex receives at most two new edges. -/
theorem connectedInitialInstance_m_le (I : Instance) (K : ℤ) :
    (connectedInitialInstance I K).m ≤ I.m + 2*I.n := by
  have hfree : (freeEdges I).card ≤ I.m := by
    simpa using Finset.card_le_card (Finset.subset_univ (freeEdges I))
  have hpartition : (deficitVertices I).card + (zeroDeficitVertices I).card = I.n := by
    simpa [deficitVertices, zeroDeficitVertices, Nat.add_comm] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin I.n))) (p := fun v => twiceDeficit I v = 0))
  unfold connectedInitialInstance
  rw [instanceOfArrays_m]
  omega

/-- The augmented graph uses only the old vertices and the hub. -/
theorem connectedInitialInstance_valid (I : Instance) (K : ℤ) (hI : I.IsValid) :
    (connectedInitialInstance I K).IsValid := by
  apply valid_instanceOfArrays
  intro e
  refine Fin.addCases (fun j => ?_) (fun j => ?_) e
  · simp only [connectedInitialEdgeArray, Fin.addCases_left]
    let e₀ := (arrayIndex (initialEdgeArray I K) (initialDemands I)).symm j
    have he := (initialInstance_valid I K hI).1 _ (List.getElem_mem e₀.2)
    change ((initialInstance I K).edge e₀).tail < I.n+1 ∧
      ((initialInstance I K).edge e₀).head < I.n+1 at he
    rw [show (initialInstance I K).edge e₀ = _ from instanceOfArrays_edge _ _ e₀,
      Equiv.apply_symm_apply] at he
    exact he
  · simp only [connectedInitialEdgeArray, Fin.addCases_right]
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · rw [Fin.addCases_left]
      simp [starEdge, Nat.le_of_lt (zeroDeficitIndex I k).1.2]
    · rw [Fin.addCases_right]
      simp [starEdge, Nat.le_of_lt (zeroDeficitIndex I k).1.2]

/-- The two new edges at each vertex contribute zero to every demand. -/
theorem connectedInitialFlow_routes (I : Instance) (K : ℤ) (hI : I.IsValid)
    (hordered : ∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper)
    (hbal : (∑ v : Fin I.n, (I.d v : ℝ)) = 0) :
    (connectedInitialInstance I K).Routes (connectedInitialFlow I K) := by
  have h := (routes_flowOfArray_iff _ _ _).mp (initialFlow_routes I K hI hordered hbal)
  apply (routes_flowOfArray_iff _ _ _).mpr
  intro v
  rw [Fin.sum_univ_add]
  simp only [connectedInitialEdgeArray, Fin.addCases_left, Fin.addCases_right, mul_one]
  rw [h v, Fin.sum_univ_add, ← Finset.sum_add_distrib]
  have hz (j : Fin (zeroDeficitVertices I).card) :
      (starEdge I.n (zeroDeficitIndex I j).1 2 K).b v +
        (starEdge I.n (zeroDeficitIndex I j).1 (-2) K).b v = 0 := by
    simp [starEdge, Edge.b]
  simp only [Fin.addCases_left, Fin.addCases_right, hz, Finset.sum_const_zero, add_zero]

/-- Each connected midpoint slack is at least half a unit. -/
theorem connectedInitialFlow_slacks (I : Instance) (K : ℤ)
    (e : Fin (connectedInitialInstance I K).m) :
    (1/2 : ℝ) ≤ connectedInitialFlow I K e - ((connectedInitialInstance I K).edge e).lower ∧
      (1/2 : ℝ) ≤ ((connectedInitialInstance I K).edge e).upper - connectedInitialFlow I K e := by
  rw [show (connectedInitialInstance I K).edge e = _ from instanceOfArrays_edge _ _ e]
  unfold connectedInitialFlow flowOfArray
  generalize arrayIndex (connectedInitialEdgeArray I K) (initialDemands I) e = j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simp only [connectedInitialEdgeArray, Fin.addCases_left]
    exact initialArrayFlow_slacks I K k
  · simp only [connectedInitialEdgeArray, Fin.addCases_right]
    refine Fin.addCases (fun a => ?_) (fun a => ?_) k <;>
      simp only [Fin.addCases_left, Fin.addCases_right, starEdge_lower, starEdge_upper] <;> norm_num

/-- The added edges have unit midpoint slack, and the old slacks are unchanged. -/
theorem connectedInitialFlow_inside (I : Instance) (K : ℤ) :
    StrictlyInside (connectedInitialInstance I K) (connectedInitialFlow I K) := by
  intro e
  have hs := connectedInitialFlow_slacks I K e
  constructor <;> linarith only [hs.1, hs.2]

/-- The midpoint flow is feasible after the same prechecks as Lemma 4.12. -/
theorem connectedInitialFlow_feasible (I : Instance) (K : ℤ) (hI : I.IsValid)
    (hordered : ∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper)
    (hbal : (∑ v : Fin I.n, (I.d v : ℝ)) = 0) :
    (connectedInitialInstance I K).IsFeasible (connectedInitialFlow I K) :=
  feasible_of_inside _ _ (connectedInitialFlow_routes I K hI hordered hbal)
    (connectedInitialFlow_inside I K)

/-- Every original vertex has an edge to the hub, even at zero deficit. -/
theorem connectedInitialInstance_hub (I : Instance) (K : ℤ) (v : Fin I.n) :
    (namedInstance (connectedInitialInstance I K)).Connected v I.n := by
  have hlink (j : Fin (((freeEdges I).card + (deficitVertices I).card) +
      ((zeroDeficitVertices I).card + (zeroDeficitVertices I).card)))
      (hj : ((connectedInitialEdgeArray I K j).tail = v ∧
              (connectedInitialEdgeArray I K j).head = I.n) ∨
            ((connectedInitialEdgeArray I K j).head = v ∧
              (connectedInitialEdgeArray I K j).tail = I.n)) :
      (namedInstance (connectedInitialInstance I K)).Connected v I.n := by
    let e : Fin (connectedInitialInstance I K).m := (arrayIndex (connectedInitialEdgeArray I K) (initialDemands I)).symm j
    have he := LSF.connected_of_edge
      (G := namedInstance (connectedInitialInstance I K)) (e := e)
      (Finset.mem_range.mpr e.2)
    have hedge : (connectedInitialInstance I K).edge e = connectedInitialEdgeArray I K j := by
      rw [show (connectedInitialInstance I K).edge e = _ from instanceOfArrays_edge _ _ e,
        Equiv.apply_symm_apply]
    have ht : (namedInstance (connectedInitialInstance I K)).tail e =
        (connectedInitialEdgeArray I K j).tail := by
      change (if h : e.val < (connectedInitialInstance I K).m then
        ((connectedInitialInstance I K).edge ⟨e.val, h⟩).tail else 0) = _
      rw [dite_eq_left e.2]
      exact congrArg Edge.tail hedge
    have hh : (namedInstance (connectedInitialInstance I K)).head e =
        (connectedInitialEdgeArray I K j).head := by
      change (if h : e.val < (connectedInitialInstance I K).m then
        ((connectedInitialInstance I K).edge ⟨e.val, h⟩).head else 0) = _
      rw [dite_eq_left e.2]
      exact congrArg Edge.head hedge
    rw [ht, hh] at he
    rcases hj with ⟨ht, hh⟩ | ⟨hh, ht⟩
    · simpa only [ht, hh] using he
    · exact LSF.connected_symm (by simpa only [ht, hh] using he)
  by_cases hz : twiceDeficit I v = 0
  · let j := (zeroDeficitIndex I).symm ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩⟩
    apply hlink (Fin.natAdd _ (Fin.castAdd _ j))
    left
    simp [connectedInitialEdgeArray, Fin.addCases_left, Fin.addCases_right, j, starEdge]
  · let j := (deficitIndex I).symm ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩⟩
    apply hlink (Fin.castAdd _ (Fin.natAdd _ j))
    simp only [connectedInitialEdgeArray, initialEdgeArray, Fin.addCases_left, Fin.addCases_right,
      j, Equiv.apply_symm_apply]
    unfold starEdge
    split_ifs
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩

/-- The graph presented to the data structure at initialization is connected. -/
theorem connectedInitialInstance_connected (I : Instance) (K : ℤ) :
    let G := namedInstance (connectedInitialInstance I K)
    ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v := by
  intro G u hu v hv
  have toHub (w : ℕ) (hw : w ∈ G.V) : G.Connected w I.n := by
    have hw' : w < I.n+1 := Finset.mem_range.mp hw
    rcases Nat.lt_succ_iff_lt_or_eq.mp hw' with h | rfl
    · exact connectedInitialInstance_hub I K ⟨w, h⟩
    · exact LSF.connected_refl G I.n
  exact LSF.connected_trans (toHub u hu) (LSF.connected_symm (toHub v hv))

end MinCostFlow.IPM
