module

public import MinCostFlow.HierPaths.Walks
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Live vertices and the volume of the pruned set

The path data structure stores a family of *connectors*. A connector joins two terminals (its
endpoints) and stores a walk of the input graph `G` between their owners. Over time terminals are
lost, so the set of *surviving* terminals only shrinks. A connector is *eligible* while both its
endpoints survive. A vertex of `G` is *live* if it owns a surviving terminal or lies on the walk
of an eligible connector. The pruned set `V̂` reported to the user is the set of vertices that
are not live.

Deletions are tied to the connectors by the *reverse-index rule*: each connector has a designated
endpoint, and when an edge of its walk is deleted, its designated endpoint is lost.

This file states these notions for an abstract `ConnectorSystem` and proves the following
properties:

* `prunedSet_initial`: `V̂` is empty when all terminals survive;
* `prunedSet_mono`: `V̂` only grows as terminals are lost;
* `eligible_edge_not_deleted`, `eligible_vert_live`: an eligible walk uses only undeleted edges
  and live vertices;
* `vol_prunedSet_le`: if each vertex owns at least its degree in terminals, the volume of `V̂` in
  `G` is at most the number of lost terminals.

The support arrays and the walks they give are in `HierPaths/LiveSupport.lean`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

/-- A connector system: terminals `0, …, numTerm - 1` with their owners (vertices of the input
graph), and connectors `0, …, numConn - 1`. Connector `c` has the endpoint terminals `endA c` and
`endB c`, the designated endpoint `endB c` if `desigB c` and `endA c` otherwise, and a stored walk
`walk c` of the input graph from the owner of `endA c` to the owner of `endB c`. -/
structure ConnectorSystem where
  /-- The number of terminals. -/
  numTerm : ℕ
  /-- The owner of each terminal, a vertex of the input graph. -/
  owner : ℕ → ℕ
  /-- The number of connectors. -/
  numConn : ℕ
  /-- The first endpoint of each connector. -/
  endA : ℕ → ℕ
  /-- The second endpoint of each connector. -/
  endB : ℕ → ℕ
  /-- Whether the designated endpoint of a connector is its second endpoint. -/
  desigB : ℕ → Bool
  /-- The stored walk of each connector. -/
  walk : ℕ → Walk

namespace ConnectorSystem

variable (C : ConnectorSystem)

/-- The designated endpoint of connector `c`. -/
def desig (c : ℕ) : ℕ :=
  if C.desigB c then C.endB c else C.endA c

/-- The connector system fits the graph `G`: endpoints are terminals, owners are vertices, and
each stored walk is a walk of `G` between the owners of the endpoints. -/
def FitsGraph (G : Graph) : Prop :=
  (∀ t < C.numTerm, C.owner t < G.n) ∧
  ∀ c < C.numConn, C.endA c < C.numTerm ∧ C.endB c < C.numTerm ∧
    (C.walk c).IsWalk G (C.owner (C.endA c)) (C.owner (C.endB c))

/-- The reverse-index rule for the deleted edges `D` and the surviving terminals `surv`: if a
deleted edge lies on the walk of a connector, its designated endpoint does not survive. -/
def ReverseIndexRule (D surv : Finset ℕ) : Prop :=
  ∀ c < C.numConn, ∀ e ∈ (C.walk c).edges, e ∈ D → C.desig c ∉ surv

/-- Connector `c` is eligible when both its endpoints survive. -/
def Eligible (surv : Finset ℕ) (c : ℕ) : Prop :=
  c < C.numConn ∧ C.endA c ∈ surv ∧ C.endB c ∈ surv

instance (surv : Finset ℕ) (c : ℕ) : Decidable (C.Eligible surv c) := by
  unfold Eligible; infer_instance

/-- The live set `S`: the vertices of `G` that own a surviving terminal or lie on the walk of an
eligible connector. -/
def liveSet (G : Graph) (surv : Finset ℕ) : Finset ℕ :=
  G.verts.filter fun w =>
    (∃ t ∈ surv, C.owner t = w) ∨
      ∃ c ∈ Finset.range C.numConn, C.Eligible surv c ∧ w ∈ (C.walk c).verts

/-- The pruned set `V̂ = V \ S`. -/
def prunedSet (G : Graph) (surv : Finset ℕ) : Finset ℕ :=
  G.verts \ C.liveSet G surv

end ConnectorSystem

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

namespace ConnectorSystem

variable (C : ConnectorSystem)

public section

theorem mem_liveSet {G : Graph} {surv : Finset ℕ} {w : ℕ} :
    w ∈ C.liveSet G surv ↔ w < G.n ∧ ((∃ t ∈ surv, C.owner t = w) ∨
      ∃ c, C.Eligible surv c ∧ w ∈ (C.walk c).verts) := by
  unfold liveSet
  rw [Finset.mem_filter, Graph.verts, Finset.mem_range]
  constructor
  · rintro ⟨hw, h | ⟨c, _, hc⟩⟩
    · exact ⟨hw, Or.inl h⟩
    · exact ⟨hw, Or.inr ⟨c, hc⟩⟩
  · rintro ⟨hw, h | ⟨c, hc⟩⟩
    · exact ⟨hw, Or.inl h⟩
    · exact ⟨hw, Or.inr ⟨c, Finset.mem_range.mpr hc.1.1, hc⟩⟩

theorem mem_prunedSet {G : Graph} {surv : Finset ℕ} {w : ℕ} :
    w ∈ C.prunedSet G surv ↔ w < G.n ∧ w ∉ C.liveSet G surv := by
  rw [prunedSet, Finset.mem_sdiff, Graph.verts, Finset.mem_range]

/-- The pruned set, first part: when all terminals survive and every vertex owns a
terminal, the pruned set is empty. -/
theorem prunedSet_initial {G : Graph} (hown : ∀ w < G.n, ∃ t < C.numTerm, C.owner t = w) :
    C.prunedSet G (Finset.range C.numTerm) = ∅ := by
  ext w
  simp only [Finset.notMem_empty, iff_false]
  rw [mem_prunedSet]
  rintro ⟨hw, hl⟩
  obtain ⟨t, ht, rfl⟩ := hown w hw
  exact hl ((C.mem_liveSet).mpr ⟨hw, Or.inl ⟨t, Finset.mem_range.mpr ht, rfl⟩⟩)

/-- Eligibility only turns off as terminals are lost. -/
theorem Eligible.mono {surv surv' : Finset ℕ} (h : surv' ⊆ surv) {c : ℕ}
    (hc : C.Eligible surv' c) : C.Eligible surv c :=
  ⟨hc.1, h hc.2.1, h hc.2.2⟩

/-- The live set only shrinks as terminals are lost. -/
theorem liveSet_mono {G : Graph} {surv surv' : Finset ℕ} (h : surv' ⊆ surv) :
    C.liveSet G surv' ⊆ C.liveSet G surv := by
  intro w hw
  rw [mem_liveSet] at hw ⊢
  rcases hw with ⟨hw, ⟨t, ht, ho⟩ | ⟨c, hc, hwc⟩⟩
  · exact ⟨hw, Or.inl ⟨t, h ht, ho⟩⟩
  · exact ⟨hw, Or.inr ⟨c, hc.mono C h, hwc⟩⟩

/-- The pruned set, second part: the pruned set only grows as terminals are lost. -/
theorem prunedSet_mono {G : Graph} {surv surv' : Finset ℕ} (h : surv' ⊆ surv) :
    C.prunedSet G surv ⊆ C.prunedSet G surv' :=
  Finset.sdiff_subset_sdiff (subset_refl _) (C.liveSet_mono h)

/-- The pruned set, third part: under the reverse-index rule, an eligible walk uses no
deleted edge. The designated endpoint of an eligible connector survives, so no edge of its walk is
deleted. -/
theorem eligible_edge_not_deleted {D surv : Finset ℕ} (hrule : C.ReverseIndexRule D surv)
    {c : ℕ} (hc : C.Eligible surv c) {e : ℕ} (he : e ∈ (C.walk c).edges) : e ∉ D := by
  intro hD
  apply hrule c hc.1 e he hD
  unfold desig
  split_ifs
  · exact hc.2.2
  · exact hc.2.1

/-- The pruned set, third part: every vertex of an eligible walk is live. It is a vertex
of `G` because the walk is a walk of the valid graph `G`. -/
theorem eligible_vert_live {G : Graph} (hG : G.IsValid) (hfit : C.FitsGraph G)
    {surv : Finset ℕ} {c : ℕ} (hc : C.Eligible surv c) {x : ℕ} (hx : x ∈ (C.walk c).verts) :
    x ∈ C.liveSet G surv := by
  rw [mem_liveSet]
  exact ⟨Walk.isWalk_verts_lt hG (hfit.2 c hc.1).2.2 x hx, Or.inr ⟨c, hc, hx⟩⟩

/-- The terminals owned by `w`. -/
@[expose] def ownedBy (w : ℕ) : Finset ℕ :=
  (Finset.range C.numTerm).filter fun t => C.owner t = w

theorem mem_ownedBy {w t : ℕ} : t ∈ C.ownedBy w ↔ t < C.numTerm ∧ C.owner t = w := by
  rw [ownedBy, Finset.mem_filter, Finset.mem_range]

/-- The pruned set, last part: if each vertex `w` owns at least `deg_G(w)` terminals,
the volume of the pruned set in `G` is at most the number of terminals that do not survive. Every
terminal owned by a pruned vertex is lost, and different vertices own different terminals. -/
theorem vol_prunedSet_le {G : Graph} (hdeg : ∀ w < G.n, G.deg w ≤ (C.ownedBy w).card)
    (surv : Finset ℕ) :
    G.vol (C.prunedSet G surv) ≤ (Finset.range C.numTerm \ surv).card := by
  have hvol : G.vol (C.prunedSet G surv) = ∑ w ∈ C.prunedSet G surv, G.deg w := rfl
  rw [hvol]
  calc ∑ w ∈ C.prunedSet G surv, G.deg w
      ≤ ∑ w ∈ C.prunedSet G surv, (C.ownedBy w).card := by
        refine Finset.sum_le_sum fun w hw => hdeg w ((C.mem_prunedSet).mp hw).1
    _ = ((C.prunedSet G surv).biUnion C.ownedBy).card := by
        rw [Finset.card_biUnion]
        intro w _ w' _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro t ht ht'
        simp only [ownedBy, Finset.mem_filter] at ht ht'
        exact hne (ht.2.symm.trans ht'.2)
    _ ≤ (Finset.range C.numTerm \ surv).card := by
        refine Finset.card_le_card fun t ht => ?_
        obtain ⟨w, hw, ht⟩ := Finset.mem_biUnion.mp ht
        simp only [ownedBy, Finset.mem_filter] at ht
        rw [Finset.mem_sdiff]
        refine ⟨ht.1, fun hts => ?_⟩
        obtain ⟨hwn, hwl⟩ := (C.mem_prunedSet).mp hw
        exact hwl ((C.mem_liveSet).mpr ⟨hwn, Or.inl ⟨t, hts, ht.2⟩⟩)

/-- The hypotheses of this file can hold together: a graph with one vertex and one loop, one
terminal for each end of the loop, and one connector between them whose walk is the loop, with
nothing deleted and all terminals surviving. -/
theorem exists_fitsGraph : ∃ (G : Graph) (C : ConnectorSystem), G.IsValid ∧ C.FitsGraph G ∧
    C.ReverseIndexRule ∅ (Finset.range C.numTerm) ∧
    (∀ w < G.n, G.deg w ≤ (C.ownedBy w).card) ∧ C.numConn = 1 := by
  refine ⟨⟨1, [(0, 0)]⟩, ⟨2, fun _ => 0, 1, fun _ => 0, fun _ => 1, fun _ => false,
    fun _ => ⟨[0, 0], [0]⟩⟩, ?_, ?_, ?_, ?_, rfl⟩
  · intro e he; simp at he; subst he; simp
  · refine ⟨fun t _ => by simp, fun c hc => ⟨by simp, by simp, ?_⟩⟩
    exact Walk.isWalk_single (by simp) (by simp) (by simp [Graph.m])
      (Or.inl ⟨rfl, rfl⟩)
  · intro c _ e _ he; simp at he
  · intro w hw
    have hw0 : w = 0 := by simpa using hw
    subst hw0
    decide

end

end ConnectorSystem

end MinCostFlow.HierPaths
