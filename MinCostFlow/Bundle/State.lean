module

public import MinCostFlow.Bundle.Ordered
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.List.SplitLengths

/-!
# Bundle partitions and their graphs

Each bundle is an arc of the core rotation restricted to surviving epoch
edges. The bundle graph uses the bundle containing each end as its endpoint.
-/

@[expose] public section

namespace MinCostFlow.Bundle

/-- All ends of a set of edges, with distinct tail and head ends. -/
def edgeEnds (E : Finset ℕ) : Finset End := E ×ˢ {true, false}

theorem mem_edgeEnds (E : Finset ℕ) (x : End) : x ∈ edgeEnds E ↔ x.1 ∈ E := by
  obtain ⟨e, b⟩ := x
  cases b <;> simp [edgeEnds]

theorem card_edgeEnds (E : Finset ℕ) : (edgeEnds E).card = 2 * E.card := by
  simp [edgeEnds, Finset.card_product, Nat.mul_comm]

/-- The state of an epoch's bundle graph.
Empty bundles keep their vertex names and their projection. -/
structure BundleState where
  /-- Live bundle vertices. -/
  vertices : Finset ℕ
  /-- Current edges among the edges admitted at the start of the epoch. -/
  edges : Finset ℕ
  /-- The core vertex containing each bundle. -/
  parent : ℕ → ℕ
  /-- The bundle containing each end of a current edge. -/
  bundleOf : End → ℕ

/-- The ends assigned to a given bundle. -/
def BundleState.ends (B : BundleState) (b : ℕ) : Finset End :=
  (edgeEnds B.edges).filter fun x => B.bundleOf x = b

/-- Bundle partition conditions. -/
def BundleState.IsPartition (B : BundleState) {C : MGraph} (ρ : Rotation C) (k : ℕ) : Prop :=
  B.edges ⊆ C.E ∧
  (∀ b ∈ B.vertices, B.parent b ∈ C.V) ∧
  (∀ x ∈ edgeEnds B.edges, B.bundleOf x ∈ B.vertices ∧ B.parent (B.bundleOf x) = C.src x) ∧
  ∀ b ∈ B.vertices,
    (B.ends b).card ≤ k ∧
    IsArc (fun x => decide (x ∈ B.ends b))
      ((ρ.order (B.parent b)).filter fun x => decide (x.1 ∈ B.edges))

/-- The spanner input has one vertex per bundle and keeps each edge name. -/
def BundleState.graph (B : BundleState) : MGraph where
  V := B.vertices
  E := B.edges
  tail := fun e => B.bundleOf (e, true)
  head := fun e => B.bundleOf (e, false)

private theorem ends_eq_union (B : BundleState) (b : ℕ) :
    B.ends b = ((B.edges.filter fun e => B.bundleOf (e, true) = b).image (·, true)) ∪
      ((B.edges.filter fun e => B.bundleOf (e, false) = b).image (·, false)) := by
  ext ⟨e, side⟩
  cases side <;> simp [BundleState.ends, mem_edgeEnds]

/-- A bundle graph counts its ends as degrees, including both ends of a loop. -/
theorem BundleState.deg_eq (B : BundleState) (b : ℕ) : B.graph.deg b = (B.ends b).card := by
  rw [ends_eq_union, Finset.card_union_of_disjoint]
  · unfold MGraph.deg BundleState.graph
    rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1),
      Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)]
  · rw [Finset.disjoint_left]
    rintro x hx hy
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨_, _, hh⟩ := Finset.mem_image.mp hy
    exact Bool.noConfusion (Prod.mk.inj hh).2

/-- The degree is at most the bundle cap. -/
theorem BundleState.deg_le {B : BundleState} {C : MGraph} {ρ : Rotation C} {k b : ℕ}
    (h : B.IsPartition ρ k) (hb : b ∈ B.vertices) : B.graph.deg b ≤ k := by
  rw [B.deg_eq]
  exact (h.2.2.2 b hb).1

/-- The source of each dart in the bundle graph is its assigned bundle. -/
theorem BundleState.graph_src (B : BundleState) (x : End) : B.graph.src x = B.bundleOf x := by
  obtain ⟨e, b⟩ := x
  cases b <;> rfl

private theorem bundle_dst (B : BundleState) (x : End) : B.graph.dst x = B.bundleOf x.flip := by
  obtain ⟨e, b⟩ := x
  cases b <;> rfl

/-- Projection keeps the endpoints of each edge after mapping bundle names
to core vertices. -/
theorem BundleState.project_edge {B : BundleState} {C : MGraph} {ρ : Rotation C}
    {k : ℕ} (h : B.IsPartition ρ k) {e : ℕ} (he : e ∈ B.edges) :
    e ∈ C.E ∧ B.parent (B.graph.tail e) = C.tail e ∧ B.parent (B.graph.head e) = C.head e :=
  ⟨h.1 he, (h.2.2.1 (e, true) ((mem_edgeEnds _ _).mpr he)).2,
    (h.2.2.1 (e, false) ((mem_edgeEnds _ _).mpr he)).2⟩

/-- Projection keeps the list of darts of a walk. -/
theorem BundleState.project_walk {B : BundleState} {C : MGraph} {ρ : Rotation C}
    {k u v : ℕ} {P : List End} (h : B.IsPartition ρ k) (hw : B.graph.IsWalk u v P) :
    C.IsWalk (B.parent u) (B.parent v) P := by
  induction hw with
  | nil v => exact .nil _
  | @cons u v x P he hs _ ih =>
    have htail := (h.2.2.1 x ((mem_edgeEnds _ _).mpr he)).2
    have hhead := (h.2.2.1 (End.flip x) ((mem_edgeEnds _ _).mpr he)).2
    rw [← BundleState.graph_src, hs] at htail
    rw [← bundle_dst] at hhead
    have hh : C.src (End.flip x) = C.dst x := by
      obtain ⟨e, b⟩ := x
      cases b <;> rfl
    rw [hh] at hhead
    exact .cons (h.1 he) htail.symm (hhead ▸ ih)

/-- Cut a linear representative into as many consecutive chunks as are needed
at cap `k`. -/
def initialChunks {α : Type*} (k : ℕ) (xs : List α) : List (List α) :=
  (List.replicate (xs.length ⌈/⌉ k) k).splitLengths xs

/-- Initialization makes exactly one chunk per rounded-up unit of capacity. -/
theorem initialChunks_length {α : Type*} (k : ℕ) (xs : List α) :
    (initialChunks k xs).length = xs.length ⌈/⌉ k := by
  simp [initialChunks, List.length_splitLengths]

/-- The chunks cover the input in order, and each has size at most the cap. -/
theorem initialChunks_spec {α : Type*} {k : ℕ} (hk : 0 < k) (xs : List α) :
    (initialChunks k xs).flatten = xs ∧ ∀ ys ∈ initialChunks k xs, ys.length ≤ k := by
  constructor
  · apply List.flatten_splitLengths
    simpa [List.sum_replicate, Nat.mul_comm] using le_smul_ceilDiv (β := ℕ) hk (b := xs.length)
  · apply List.length_mem_splitLengths
    intro n hn
    exact Nat.le_of_eq (List.eq_of_mem_replicate hn)


/-- The graph determined by a bundle partition has both endpoints of
every admitted edge in its vertex set. -/
theorem BundleState.graph_isValid {B : BundleState} {C : MGraph} {ρ : Rotation C} {k : ℕ}
    (h : B.IsPartition ρ k) : B.graph.IsValid := by
  intro e he
  exact ⟨(h.2.2.1 (e, true) ((mem_edgeEnds _ _).mpr he)).1,
    (h.2.2.1 (e, false) ((mem_edgeEnds _ _).mpr he)).1⟩

/-- The bundle cap bounds maximum degree. -/
theorem BundleState.maxDeg_le {B : BundleState} {C : MGraph} {ρ : Rotation C} {k : ℕ}
    (h : B.IsPartition ρ k) : B.graph.maxDeg ≤ k := by
  apply Finset.sup_le
  exact fun _ hb => BundleState.deg_le h hb


/-- An end belongs to the bundle that owns it when its edge is admitted. -/
theorem BundleState.mem_ends (B : BundleState) (b : ℕ) (x : End) :
    x ∈ B.ends b ↔ x.1 ∈ B.edges ∧ B.bundleOf x = b := by
  simp [BundleState.ends, mem_edgeEnds]

end MinCostFlow.Bundle
