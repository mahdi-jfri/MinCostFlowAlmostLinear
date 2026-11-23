module

public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.ExplicitExpander.Spec
import MinCostFlow.Expander.GraphHelpers
import MinCostFlow.ExpanderDecomp.Injection
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Port graphs for the expander decomposition

The outer decomposition turns an induced subgraph `G[X]` with
`e` edges into a bounded-degree *port graph* `portGraph cloud G X` on `2e` vertices:

- Edge number `i` of `G.inside X` gets two ports: `2 * i` (for its first endpoint) and `2 * i + 1`
  (for its second endpoint), joined by the original edge `(2 * i, 2 * i + 1)`.
- The *cloud* `cloudOf G X v` of a vertex `v ∈ X` consists of all ports belonging to `v`; its size
  equals `G.degIn X v`.
- Inside each cloud of size `s ≥ 2`, we insert a copy of the cloud expander `cloud s` (with loops
  deleted). A singleton or empty cloud gets no internal edges.

Main results:
* `IsCloudExpander` and `isCloudExpander_explicitGraph` (from `ExplicitExpander.explicitGraph`).
* `portGraph_n`, `portGraph_isValid`, `portGraph_isLoopless`, `portGraph_m_le`, and
  `portGraph_deg_le`: `portGraph cloud G X` has `2e` vertices, is valid and loopless, has at most
  `10e` edges, and has maximum degree at most `10`.
* `card_cloudOf`, `card_liftSet`, `card_sdiff_liftSet`, and `cutIn_portGraph_liftSet`: the
  canonical port lift of `S ⊆ X` has cardinality `G.volIn X S` and cut equal to `G.cutIn X S`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-- A family of cloud expanders with expansion at least `α`: for every `s ≥ 2`, `cloud s` is a
valid graph on `s` vertices with maximum degree at most `9` and edge expansion at least `α`.
Any loops in `cloud s` are deleted when building the port graph. -/
structure IsCloudExpander (cloud : ℕ → Graph) (α : ℝ) : Prop where
  /-- `cloud s` has `s` vertices. -/
  n_eq : ∀ s, 2 ≤ s → (cloud s).n = s
  /-- Every edge of `cloud s` has both ends below `s`. -/
  isValid : ∀ s, 2 ≤ s → (cloud s).IsValid
  /-- Every vertex of `cloud s` has degree at most `9`. -/
  deg_le : ∀ s, 2 ≤ s → ∀ v < s, (cloud s).deg v ≤ 9
  /-- `cloud s` has edge expansion at least `α`. -/
  expansion : ∀ s, 2 ≤ s → (cloud s).IsExpansionExpanderOn (cloud s).verts α

/-- The original vertex that owns port `p` in `G[X]`: port `2 * i` belongs to the first endpoint
of edge `i` of `G.inside X`, and port `2 * i + 1` belongs to its second endpoint. -/
def portOwner (G : Graph) (X : Finset ℕ) (p : ℕ) : ℕ :=
  let e := (G.inside X).getD (p / 2) (0, 0)
  if p % 2 = 0 then e.1 else e.2

/-- The cloud of ports belonging to vertex `v` in `G[X]`. -/
def cloudOf (G : Graph) (X : Finset ℕ) (v : ℕ) : Finset ℕ :=
  (Finset.range (2 * (G.inside X).length)).filter fun p => portOwner G X p = v

/-- The ordered list of ports in the cloud of `v` in `G[X]`. -/
def cloudPortsList (G : Graph) (X : Finset ℕ) (v : ℕ) : List ℕ :=
  (List.range (2 * (G.inside X).length)).filter fun p => decide (portOwner G X p = v)

/-- The canonical port set corresponding to an original vertex set `S`. -/
def liftSet (G : Graph) (X S : Finset ℕ) : Finset ℕ :=
  (Finset.range (2 * (G.inside X).length)).filter fun p => portOwner G X p ∈ S

/-- The `e` original-edge port pairs `(2 * i, 2 * i + 1)` for `i < e`. -/
def origPortEdges (e : ℕ) : List (ℕ × ℕ) :=
  (List.range e).map fun i => (2 * i, 2 * i + 1)

/-- The cloud expander edges placed inside the cloud of `v`, with loops deleted. Singleton and
empty clouds receive no internal edges. -/
def cloudEdgesFor (cloud : ℕ → Graph) (G : Graph) (X : Finset ℕ) (v : ℕ) : List (ℕ × ℕ) :=
  let pts := cloudPortsList G X v
  if 2 ≤ pts.length then
    ((cloud pts.length).edges.filter fun e => decide (e.1 ≠ e.2)).map fun e =>
      (pts.getD e.1 0, pts.getD e.2 0)
  else []

/-- All cloud expander edges across vertices of `X`. -/
def allCloudEdges (cloud : ℕ → Graph) (G : Graph) (X : Finset ℕ) : List (ℕ × ℕ) :=
  (X.sort (· ≤ ·)).flatMap (cloudEdgesFor cloud G X)

/-- The port graph of `G[X]` using the cloud expander family `cloud`: it has `2e`
vertices where `e = (G.inside X).length`, the `e` original port edges, and the loopless cloud
expander inside each cloud of size at least `2`. -/
def portGraph (cloud : ℕ → Graph) (G : Graph) (X : Finset ℕ) : Graph :=
  ⟨2 * (G.inside X).length, origPortEdges (G.inside X).length ++ allCloudEdges cloud G X⟩

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Explicit expander instance -/

/-- `ExplicitExpander.explicitGraph` satisfies `IsCloudExpander` with `α = 1 / 12`. -/
theorem isCloudExpander_explicitGraph :
    IsCloudExpander ExplicitExpander.explicitGraph ExplicitExpander.alpha0 where
  n_eq s hs := (ExplicitExpander.explicitGraph_spec s (by omega)).1
  isValid s hs := (ExplicitExpander.explicitGraph_spec s (by omega)).2.1
  deg_le s hs := (ExplicitExpander.explicitGraph_spec s (by omega)).2.2.2.2
  expansion s hs := (ExplicitExpander.explicitGraph_spec s (by omega)).2.2.2.1

/-! ### Ports, clouds, and canonical lifts -/

/-- The port graph has `2 * (G.inside X).length` vertices. -/
theorem portGraph_n (cloud : ℕ → Graph) (G : Graph) (X : Finset ℕ) :
    (portGraph cloud G X).n = 2 * (G.inside X).length := rfl

/-- Port `2 * i` belongs to the first endpoint of edge `i` of `G.inside X`. -/
theorem portOwner_two_mul (G : Graph) (X : Finset ℕ) (i : ℕ) :
    portOwner G X (2 * i) = ((G.inside X).getD i (0, 0)).1 := by
  unfold portOwner
  have hdiv : 2 * i / 2 = i := by omega
  have hmod : 2 * i % 2 = 0 := by omega
  simp [hdiv, hmod]

/-- Port `2 * i + 1` belongs to the second endpoint of edge `i` of `G.inside X`. -/
theorem portOwner_two_mul_succ (G : Graph) (X : Finset ℕ) (i : ℕ) :
    portOwner G X (2 * i + 1) = ((G.inside X).getD i (0, 0)).2 := by
  unfold portOwner
  have hdiv : (2 * i + 1) / 2 = i := by omega
  simp [hdiv]

/-- Every port `p < 2e` belongs to a vertex of `X`. -/
theorem portOwner_mem {G : Graph} {X : Finset ℕ} {p : ℕ}
    (hp : p < 2 * (G.inside X).length) : portOwner G X p ∈ X := by
  have hi : p / 2 < (G.inside X).length := by omega
  have hmem : (G.inside X).getD (p / 2) (0, 0) ∈ G.inside X := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hin := mem_inside_iff.mp hmem
  unfold portOwner
  split_ifs
  · exact hin.2.1
  · exact hin.2.2

/-- Membership in `cloudPortsList G X v`. -/
theorem mem_cloudPortsList_iff {G : Graph} {X : Finset ℕ} {v p : ℕ} :
    p ∈ cloudPortsList G X v ↔ p < 2 * (G.inside X).length ∧ portOwner G X p = v := by
  simp [cloudPortsList]

/-- Membership in `cloudOf G X v`. -/
theorem mem_cloudOf_iff {G : Graph} {X : Finset ℕ} {v p : ℕ} :
    p ∈ cloudOf G X v ↔ p < 2 * (G.inside X).length ∧ portOwner G X p = v := by
  simp [cloudOf]

/-- `cloudPortsList G X v` has no duplicates. -/
theorem cloudPortsList_nodup (G : Graph) (X : Finset ℕ) (v : ℕ) :
    (cloudPortsList G X v).Nodup :=
  List.nodup_range.filter _

/-- `cloudPortsList` and `cloudOf` contain the same ports. -/
theorem cloudPortsList_toFinset (G : Graph) (X : Finset ℕ) (v : ℕ) :
    (cloudPortsList G X v).toFinset = cloudOf G X v := by
  ext p
  simp [mem_cloudPortsList_iff, mem_cloudOf_iff]

/-- The length of `cloudPortsList G X v` equals the cardinality of `cloudOf G X v`. -/
theorem cloudPortsList_length (G : Graph) (X : Finset ℕ) (v : ℕ) :
    (cloudPortsList G X v).length = (cloudOf G X v).card := by
  rw [← cloudPortsList_toFinset, List.toFinset_card_of_nodup (cloudPortsList_nodup G X v)]

/-- Distinct vertices have disjoint clouds. -/
theorem cloudOf_disjoint (G : Graph) (X : Finset ℕ) {u v : ℕ} (huv : u ≠ v) :
    Disjoint (cloudOf G X u) (cloudOf G X v) := by
  rw [Finset.disjoint_left]
  intro p hu hv
  rw [mem_cloudOf_iff] at hu hv
  exact huv (hu.2.symm.trans hv.2)

/-- Helper: splitting a sum over `Finset.range (2 * e)` into even and odd indices. -/
private theorem sum_range_two_mul (e : ℕ) (f : ℕ → ℕ) :
    ∑ p ∈ Finset.range (2 * e), f p =
      ∑ i ∈ Finset.range e, (f (2 * i) + f (2 * i + 1)) := by
  induction e with
  | zero => simp
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    omega

/-- Helper: summing an indicator over `Finset.range l.length` via `getD` equals the sum over `l`. -/
private theorem sum_range_getD_eq_sum_map {α : Type*} (l : List α) (d : α) (f : α → ℕ) :
    ∑ i ∈ Finset.range l.length, f (l.getD i d) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.sum_cons]
    rw [ih]
    omega

/-- The size of the cloud of `v` equals `G.degIn X v`. -/
theorem card_cloudOf (G : Graph) (X : Finset ℕ) (v : ℕ) :
    (cloudOf G X v).card = G.degIn X v := by
  unfold cloudOf
  rw [Finset.card_filter, sum_range_two_mul]
  have h1 : ∀ i,
      (if portOwner G X (2 * i) = v then 1 else 0) +
        (if portOwner G X (2 * i + 1) = v then 1 else 0) =
      (if ((G.inside X).getD i (0, 0)).1 = v then 1 else 0) +
        (if ((G.inside X).getD i (0, 0)).2 = v then 1 else 0) := by
    intro i
    rw [portOwner_two_mul, portOwner_two_mul_succ]
  simp_rw [h1]
  rw [sum_range_getD_eq_sum_map (G.inside X) (0, 0)
    (fun e => (if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0)),
    ← degIn_eq_sum_map]

/-- The length of `cloudPortsList G X v` equals `G.degIn X v`. -/
theorem cloudPortsList_length_eq_degIn (G : Graph) (X : Finset ℕ) (v : ℕ) :
    (cloudPortsList G X v).length = G.degIn X v := by
  rw [cloudPortsList_length, card_cloudOf]

/-- `liftSet G X S` is the disjoint union of the clouds `cloudOf G X v` for `v ∈ S`. -/
theorem liftSet_eq_biUnion (G : Graph) (X S : Finset ℕ) :
    liftSet G X S = S.biUnion (cloudOf G X) := by
  ext p
  simp [liftSet, cloudOf, and_comm]

/-- The cardinality of `liftSet G X S` equals `G.volIn X S`. -/
theorem card_liftSet (G : Graph) (X S : Finset ℕ) :
    (liftSet G X S).card = G.volIn X S := by
  rw [liftSet_eq_biUnion, Finset.card_biUnion]
  · unfold Graph.volIn
    exact Finset.sum_congr rfl fun v _ => card_cloudOf G X v
  · intro u _ v _ huv
    exact cloudOf_disjoint G X huv

/-- The complement of `liftSet G X S` in the port vertices is `liftSet G X (X \ S)` when `S ⊆ X`. -/
theorem sdiff_liftSet_eq {G : Graph} {X S : Finset ℕ} (_hS : S ⊆ X) :
    Finset.range (2 * (G.inside X).length) \ liftSet G X S = liftSet G X (X \ S) := by
  ext p
  simp only [Finset.mem_sdiff, liftSet, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hp, hnot⟩
    exact ⟨hp, portOwner_mem hp, fun hmem => hnot ⟨hp, hmem⟩⟩
  · rintro ⟨hp, _, hnot⟩
    exact ⟨hp, fun h => hnot h.2⟩

/-- The complement of `liftSet G X S` in `Finset.range (2e)` has cardinality `G.volIn X (X \ S)`. -/
theorem card_sdiff_liftSet {G : Graph} {X S : Finset ℕ} (hS : S ⊆ X) :
    (Finset.range (2 * (G.inside X).length) \ liftSet G X S).card = G.volIn X (X \ S) := by
  rw [sdiff_liftSet_eq hS, card_liftSet]

/-! ### Validity, looplessness, edge count, and degrees of `portGraph` -/

/-- Every original port edge joins two distinct vertices below `2e`. -/
theorem mem_origPortEdges {e : ℕ} {ed : ℕ × ℕ} (hed : ed ∈ origPortEdges e) :
    ed.1 < 2 * e ∧ ed.2 < 2 * e ∧ ed.1 ≠ ed.2 := by
  simp only [origPortEdges, List.mem_map, List.mem_range] at hed
  obtain ⟨i, hi, rfl⟩ := hed
  omega

/-- Every cloud edge for `v` joins two distinct ports in `cloudOf G X v`. -/
theorem mem_cloudEdgesFor {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    {G : Graph} {X : Finset ℕ} {v : ℕ} {ed : ℕ × ℕ}
    (hed : ed ∈ cloudEdgesFor cloud G X v) :
    ed.1 ∈ cloudOf G X v ∧ ed.2 ∈ cloudOf G X v ∧ ed.1 ≠ ed.2 := by
  unfold cloudEdgesFor at hed
  dsimp only at hed
  split_ifs at hed with hs
  · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hed
    obtain ⟨f, ⟨hf_mem, hf_ne⟩, rfl⟩ := hed
    set pts := cloudPortsList G X v
    have hval := hcloud.isValid pts.length hs f hf_mem
    rw [hcloud.n_eq pts.length hs] at hval
    have h1 : pts.getD f.1 0 ∈ pts := by
      rw [List.getD_eq_getElem _ _ hval.1]
      exact List.getElem_mem hval.1
    have h2 : pts.getD f.2 0 ∈ pts := by
      rw [List.getD_eq_getElem _ _ hval.2]
      exact List.getElem_mem hval.2
    have hne : pts.getD f.1 0 ≠ pts.getD f.2 0 := by
      rw [List.getD_eq_getElem _ _ hval.1, List.getD_eq_getElem _ _ hval.2]
      intro heq
      have hind := (List.Nodup.getElem_inj_iff (cloudPortsList_nodup G X v)).mp heq
      exact hf_ne hind
    rw [← cloudPortsList_toFinset]
    exact ⟨List.mem_toFinset.mpr h1, List.mem_toFinset.mpr h2, hne⟩
  · simp at hed

/-- Every edge of `allCloudEdges` joins two distinct ports belonging to the same vertex of `X`. -/
theorem mem_allCloudEdges {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    {G : Graph} {X : Finset ℕ} {ed : ℕ × ℕ} (hed : ed ∈ allCloudEdges cloud G X) :
    ∃ v ∈ X, ed.1 ∈ cloudOf G X v ∧ ed.2 ∈ cloudOf G X v ∧ ed.1 ≠ ed.2 := by
  unfold allCloudEdges at hed
  rw [List.mem_flatMap] at hed
  obtain ⟨v, hv, hedv⟩ := hed
  have hvX : v ∈ X := (Finset.mem_sort (· ≤ ·)).mp hv
  exact ⟨v, hvX, mem_cloudEdgesFor hcloud hedv⟩

/-- The port graph is valid: all edge endpoints are below `2e`. -/
theorem portGraph_isValid {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    (G : Graph) (X : Finset ℕ) : (portGraph cloud G X).IsValid := by
  intro ed hed
  unfold portGraph at hed ⊢
  dsimp only at hed ⊢
  rw [List.mem_append] at hed
  rcases hed with h | h
  · have hm := mem_origPortEdges h
    exact ⟨hm.1, hm.2.1⟩
  · obtain ⟨_, _, h1, h2, _⟩ := mem_allCloudEdges hcloud h
    exact ⟨(mem_cloudOf_iff.mp h1).1, (mem_cloudOf_iff.mp h2).1⟩

/-- The port graph is loopless. -/
theorem portGraph_isLoopless {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    (G : Graph) (X : Finset ℕ) : (portGraph cloud G X).IsLoopless := by
  intro ed hed
  unfold portGraph at hed
  dsimp only at hed
  rw [List.mem_append] at hed
  rcases hed with h | h
  · exact (mem_origPortEdges h).2.2
  · obtain ⟨_, _, _, _, hne⟩ := mem_allCloudEdges hcloud h
    exact hne

/-- The degree of a port `p` in `origPortEdges e` is `1` if `p < 2e` and `0` otherwise. -/
theorem deg_origPortEdges (e p : ℕ) :
    (Graph.mk (2 * e) (origPortEdges e)).deg p = if p < 2 * e then 1 else 0 := by
  have hv : (Graph.mk (2 * e) (origPortEdges e)).IsValid := by
    intro ed hed
    have h := mem_origPortEdges hed
    exact ⟨h.1, h.2.1⟩
  unfold Graph.deg
  rw [degIn_eq_sum_map, inside_verts_of_isValid hv]
  dsimp only [origPortEdges]
  rw [List.map_map]
  have hsum : ((List.range e).map fun i =>
      (if 2 * i = p then 1 else 0) + (if 2 * i + 1 = p then 1 else 0)).sum =
      ∑ i ∈ Finset.range e, ((if 2 * i = p then 1 else 0) + (if 2 * i + 1 = p then 1 else 0)) := by
    rw [← sum_range_getD_eq_sum_map (List.range e) 0
      (fun i => (if 2 * i = p then 1 else 0) + (if 2 * i + 1 = p then 1 else 0))]
    simp only [List.length_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < e := Finset.mem_range.mp hi
    rw [List.getD_eq_getElem _ _ (by simp [hi']), List.getElem_range]
  change ((List.range e).map fun i =>
    (if 2 * i = p then 1 else 0) + (if 2 * i + 1 = p then 1 else 0)).sum = _
  rw [hsum, ← sum_range_two_mul e (fun q => if q = p then 1 else 0)]
  simp

/-- Helper: count of incidences at `p` in a list of edges. -/
private def edgeDeg (E : List (ℕ × ℕ)) (p : ℕ) : ℕ :=
  (E.map fun e => (if e.1 = p then 1 else 0) + (if e.2 = p then 1 else 0)).sum

private theorem edgeDeg_append (E₁ E₂ : List (ℕ × ℕ)) (p : ℕ) :
    edgeDeg (E₁ ++ E₂) p = edgeDeg E₁ p + edgeDeg E₂ p := by
  unfold edgeDeg
  rw [List.map_append, List.sum_append]

private theorem edgeDeg_flatMap {α : Type*} (l : List α) (f : α → List (ℕ × ℕ)) (p : ℕ) :
    edgeDeg (l.flatMap f) p = (l.map fun x => edgeDeg (f x) p).sum := by
  induction l with
  | nil => simp [edgeDeg]
  | cons a t ih =>
    simp only [List.flatMap_cons, edgeDeg_append, List.map_cons, List.sum_cons, ih]

private theorem deg_eq_edgeDeg {G : Graph} (hv : G.IsValid) (p : ℕ) :
    G.deg p = edgeDeg G.edges p := by
  unfold Graph.deg edgeDeg
  rw [degIn_eq_sum_map, inside_verts_of_isValid hv]

/-- A port `p` has degree `0` in `cloudEdgesFor cloud G X v` whenever `p ∉ cloudOf G X v`. -/
private theorem edgeDeg_cloudEdgesFor_of_not_mem {cloud : ℕ → Graph} {α : ℝ}
    (hcloud : IsCloudExpander cloud α) {G : Graph} {X : Finset ℕ} {v p : ℕ}
    (hp : p ∉ cloudOf G X v) :
    edgeDeg (cloudEdgesFor cloud G X v) p = 0 := by
  unfold edgeDeg
  have hzero : ((cloudEdgesFor cloud G X v).map fun e =>
      (if e.1 = p then 1 else 0) + (if e.2 = p then 1 else 0)) =
      (cloudEdgesFor cloud G X v).map fun _ => 0 := by
    apply List.map_congr_left
    intro e he
    have hm := mem_cloudEdgesFor hcloud he
    have h1 : e.1 ≠ p := fun h => hp (h ▸ hm.1)
    have h2 : e.2 ≠ p := fun h => hp (h ▸ hm.2.1)
    simp [h1, h2]
  rw [hzero, sum_map_const, Nat.mul_zero]

/-- A port `p` has degree at most `9` in `cloudEdgesFor cloud G X v`. -/
private theorem edgeDeg_cloudEdgesFor_le {cloud : ℕ → Graph} {α : ℝ}
    (hcloud : IsCloudExpander cloud α) (G : Graph) (X : Finset ℕ) (v p : ℕ) :
    edgeDeg (cloudEdgesFor cloud G X v) p ≤ 9 := by
  by_cases hp : p ∈ cloudOf G X v
  · unfold cloudEdgesFor
    dsimp only
    split_ifs with hs
    · set pts := cloudPortsList G X v
      have hp_pts : p ∈ pts := by
        rw [← List.mem_toFinset, cloudPortsList_toFinset]
        exact hp
      obtain ⟨k, hk, hpk⟩ := List.getElem_of_mem hp_pts
      have hnd : pts.Nodup := cloudPortsList_nodup G X v
      have hv_cloud : (cloud pts.length).IsValid := hcloud.isValid pts.length hs
      have hn_cloud : (cloud pts.length).n = pts.length := hcloud.n_eq pts.length hs
      have hdeg_le : (cloud pts.length).deg k ≤ 9 := hcloud.deg_le pts.length hs k hk
      rw [deg_eq_edgeDeg hv_cloud] at hdeg_le
      refine le_trans ?_ hdeg_le
      unfold edgeDeg
      rw [List.map_map]
      have hfilt : ∀ l : List (ℕ × ℕ),
          (∀ e ∈ l, e.1 < pts.length ∧ e.2 < pts.length) →
          ((l.filter fun e => decide (e.1 ≠ e.2)).map
            ((fun e : ℕ × ℕ => (if e.1 = p then 1 else 0) + (if e.2 = p then 1 else 0)) ∘
              fun e => (pts.getD e.1 0, pts.getD e.2 0))).sum ≤
          (l.map fun e => (if e.1 = k then 1 else 0) + (if e.2 = k then 1 else 0)).sum := by
        intro l hl
        induction l with
        | nil => simp
        | cons a t ih =>
          have ha := hl a List.mem_cons_self
          have ht := ih fun e he => hl e (List.mem_cons_of_mem _ he)
          rw [List.filter_cons]
          split_ifs with hne
          · simp only [List.map_cons, List.sum_cons, Function.comp_apply]
            have h1 : pts.getD a.1 0 = p ↔ a.1 = k := by
              rw [List.getD_eq_getElem _ _ ha.1, ← hpk, List.Nodup.getElem_inj_iff hnd]
            have h2 : pts.getD a.2 0 = p ↔ a.2 = k := by
              rw [List.getD_eq_getElem _ _ ha.2, ← hpk, List.Nodup.getElem_inj_iff hnd]
            simp only [h1, h2]
            omega
          · simp only [List.map_cons, List.sum_cons]
            omega
      exact hfilt (cloud pts.length).edges fun e he => by
        have h := hv_cloud e he
        rw [hn_cloud] at h
        exact h
    · simp [edgeDeg]
  · rw [edgeDeg_cloudEdgesFor_of_not_mem hcloud hp]
    omega

/-- Every port `p < 2e` has degree at most `10` in `portGraph cloud G X`. -/
theorem portGraph_deg_le {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    (G : Graph) (X : Finset ℕ) (p : ℕ) :
    (portGraph cloud G X).deg p ≤ 10 := by
  have hv := portGraph_isValid hcloud G X
  rw [deg_eq_edgeDeg hv]
  unfold portGraph
  dsimp only
  rw [edgeDeg_append]
  have horig : edgeDeg (origPortEdges (G.inside X).length) p ≤ 1 := by
    have hv0 : (Graph.mk (2 * (G.inside X).length) (origPortEdges (G.inside X).length)).IsValid := by
      intro ed hed
      have h := mem_origPortEdges hed
      exact ⟨h.1, h.2.1⟩
    rw [← deg_eq_edgeDeg hv0, deg_origPortEdges]
    split_ifs <;> omega
  have hclouds : edgeDeg (allCloudEdges cloud G X) p ≤ 9 := by
    unfold allCloudEdges
    rw [edgeDeg_flatMap]
    by_cases hp : p < 2 * (G.inside X).length
    · set v₀ := portOwner G X p
      have hv₀ : v₀ ∈ X := portOwner_mem hp
      have hnd : (X.sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
      have hmem : v₀ ∈ X.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hv₀
      have hsingle : ((X.sort (· ≤ ·)).map fun v => edgeDeg (cloudEdgesFor cloud G X v) p).sum =
          (X.sort (· ≤ ·)).count v₀ * edgeDeg (cloudEdgesFor cloud G X v₀) p := by
        simpa [smul_eq_mul] using List.sum_map_eq_nsmul_single v₀
          (fun v => edgeDeg (cloudEdgesFor cloud G X v) p) (fun v hvne _ => by
            apply edgeDeg_cloudEdgesFor_of_not_mem hcloud
            rw [mem_cloudOf_iff]
            intro h
            exact hvne h.2.symm)
      rw [hsingle, List.count_eq_one_of_mem hnd hmem, one_mul]
      exact edgeDeg_cloudEdgesFor_le hcloud G X v₀ p
    · have hzero : ((X.sort (· ≤ ·)).map fun v => edgeDeg (cloudEdgesFor cloud G X v) p) =
          (X.sort (· ≤ ·)).map fun _ => 0 := by
        apply List.map_congr_left
        intro v _
        apply edgeDeg_cloudEdgesFor_of_not_mem hcloud
        rw [mem_cloudOf_iff]
        intro h
        exact hp h.1
      rw [hzero, sum_map_const, Nat.mul_zero]
      omega
  omega

/-- Each cloud of size `s` contributes at most `9 * s / 2` edges (in product form, `2 * m_v ≤ 9 * s`). -/
theorem two_mul_cloudEdgesFor_length_le {cloud : ℕ → Graph} {α : ℝ}
    (hcloud : IsCloudExpander cloud α) (G : Graph) (X : Finset ℕ) (v : ℕ) :
    2 * (cloudEdgesFor cloud G X v).length ≤ 9 * G.degIn X v := by
  unfold cloudEdgesFor
  dsimp only
  split_ifs with hs
  · set pts := cloudPortsList G X v
    have hlen : pts.length = G.degIn X v := cloudPortsList_length_eq_degIn G X v
    rw [List.length_map]
    have hfilt : ((cloud pts.length).edges.filter fun e => decide (e.1 ≠ e.2)).length ≤
        (cloud pts.length).m := List.length_filter_le _ _
    have hvol := vol_verts_of_isValid (hcloud.isValid pts.length hs)
    have hvol_le : (cloud pts.length).vol (cloud pts.length).verts ≤ 9 * pts.length := by
      unfold Graph.vol Graph.volIn Graph.verts
      rw [hcloud.n_eq pts.length hs]
      calc ∑ u ∈ Finset.range pts.length, (cloud pts.length).degIn (Finset.range pts.length) u
          = ∑ u ∈ Finset.range pts.length, (cloud pts.length).deg u := by
              apply Finset.sum_congr rfl
              intro u _
              unfold Graph.deg Graph.verts
              rw [hcloud.n_eq pts.length hs]
        _ ≤ ∑ _u ∈ Finset.range pts.length, 9 :=
              Finset.sum_le_sum fun u hu => hcloud.deg_le pts.length hs u (Finset.mem_range.mp hu)
        _ = 9 * pts.length := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]
    omega
  · simp

/-- `allCloudEdges` has at most `9 * (G.inside X).length` edges. -/
theorem allCloudEdges_length_le {cloud : ℕ → Graph} {α : ℝ}
    (hcloud : IsCloudExpander cloud α) (G : Graph) (X : Finset ℕ) :
    (allCloudEdges cloud G X).length ≤ 9 * (G.inside X).length := by
  have h2 : 2 * (allCloudEdges cloud G X).length ≤ 2 * (9 * (G.inside X).length) := by
    unfold allCloudEdges
    rw [List.length_flatMap]
    have hmul : ∀ l : List ℕ,
        2 * (l.map fun v => (cloudEdgesFor cloud G X v).length).sum =
        (l.map fun v => 2 * (cloudEdgesFor cloud G X v).length).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a t ih => simp only [List.map_cons, List.sum_cons, Nat.mul_add, ih]
    rw [hmul]
    have hle : ((X.sort (· ≤ ·)).map fun v => 2 * (cloudEdgesFor cloud G X v).length).sum ≤
        ((X.sort (· ≤ ·)).map fun v => 9 * G.degIn X v).sum :=
      sum_map_le_sum_map fun v _ => two_mul_cloudEdgesFor_length_le hcloud G X v
    have hsum : ((X.sort (· ≤ ·)).map fun v => 9 * G.degIn X v).sum = 9 * G.volIn X X := by
      have h9 : ∀ l : List ℕ, (l.map fun v => 9 * G.degIn X v).sum =
          9 * (l.map fun v => G.degIn X v).sum := by
        intro l
        induction l with
        | nil => simp
        | cons a t ih => simp only [List.map_cons, List.sum_cons, Nat.mul_add, ih]
      rw [h9]
      congr 1
      unfold Graph.volIn
      rw [← List.sum_toFinset _ (Finset.sort_nodup X (· ≤ ·))]
      have htoF : (X.sort (· ≤ ·)).toFinset = X := by
        ext v
        simp
      rw [htoF]
    rw [hsum, volIn_self] at hle
    omega
  omega

/-- The port graph has at most `10 * (G.inside X).length` edges. -/
theorem portGraph_m_le {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    (G : Graph) (X : Finset ℕ) :
    (portGraph cloud G X).m ≤ 10 * (G.inside X).length := by
  unfold Graph.m portGraph
  dsimp only
  rw [List.length_append]
  have h1 : (origPortEdges (G.inside X).length).length = (G.inside X).length := by
    simp [origPortEdges]
  have h2 := allCloudEdges_length_le hcloud G X
  omega

/-! ### Canonical port cuts -/

/-- The cut of `liftSet G X S` in `origPortEdges e` equals `G.cutIn X S`. -/
theorem cutIn_origPortEdges_liftSet (G : Graph) (X S : Finset ℕ) :
    (Graph.mk (2 * (G.inside X).length) (origPortEdges (G.inside X).length)).cutIn
      (Finset.range (2 * (G.inside X).length)) (liftSet G X S) = G.cutIn X S := by
  have hv : (Graph.mk (2 * (G.inside X).length) (origPortEdges (G.inside X).length)).IsValid := by
    intro ed hed
    have h := mem_origPortEdges hed
    exact ⟨h.1, h.2.1⟩
  rw [cutIn_eq_sum_map, cutIn_eq_sum_map]
  change (((Graph.mk (2 * (G.inside X).length) (origPortEdges (G.inside X).length)).inside
      (Graph.mk (2 * (G.inside X).length) (origPortEdges (G.inside X).length)).verts).map _).sum = _
  rw [inside_verts_of_isValid hv]
  dsimp only [origPortEdges]
  rw [List.map_map, ← sum_range_getD_eq_sum_map (G.inside X) (0, 0)]
  rw [← sum_range_getD_eq_sum_map (List.range (G.inside X).length) 0]
  simp only [List.length_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < (G.inside X).length := Finset.mem_range.mp hi
  rw [List.getD_eq_getElem _ _ (by simp [hi']), List.getElem_range]
  have h1 : 2 * i ∈ liftSet G X S ↔ ((G.inside X).getD i (0, 0)).1 ∈ S := by
    simp [liftSet, portOwner_two_mul, show 2 * i < 2 * (G.inside X).length by omega]
  have h2 : 2 * i + 1 ∈ liftSet G X S ↔ ((G.inside X).getD i (0, 0)).2 ∈ S := by
    simp [liftSet, portOwner_two_mul_succ, show 2 * i + 1 < 2 * (G.inside X).length by omega]
  simp only [Function.comp_apply, h1, h2]

/-- No cloud edge crosses a canonical port cut `liftSet G X S`. -/
theorem cutIn_allCloudEdges_liftSet {cloud : ℕ → Graph} {α : ℝ}
    (hcloud : IsCloudExpander cloud α) (G : Graph) (X S : Finset ℕ) :
    (Graph.mk (2 * (G.inside X).length) (allCloudEdges cloud G X)).cutIn
      (Finset.range (2 * (G.inside X).length)) (liftSet G X S) = 0 := by
  rw [cutIn_eq_sum_map]
  have hzero : (((Graph.mk (2 * (G.inside X).length) (allCloudEdges cloud G X)).inside
      (Finset.range (2 * (G.inside X).length))).map fun e =>
        if (decide (e.1 ∈ liftSet G X S) != decide (e.2 ∈ liftSet G X S)) then 1 else 0) =
      ((Graph.mk (2 * (G.inside X).length) (allCloudEdges cloud G X)).inside
        (Finset.range (2 * (G.inside X).length))).map fun _ => 0 := by
    apply List.map_congr_left
    intro e he
    rw [mem_inside_iff] at he
    obtain ⟨v, _, h1, h2, _⟩ := mem_allCloudEdges hcloud he.1
    have h1' := mem_cloudOf_iff.mp h1
    have h2' := mem_cloudOf_iff.mp h2
    have hmem1 : e.1 ∈ liftSet G X S ↔ v ∈ S := by simp [liftSet, h1'.1, h1'.2]
    have hmem2 : e.2 ∈ liftSet G X S ↔ v ∈ S := by simp [liftSet, h2'.1, h2'.2]
    simp [hmem1, hmem2]
  rw [hzero, sum_map_const, Nat.mul_zero]

/-- The cut of `liftSet G X S` in `portGraph cloud G X` equals `G.cutIn X S`. -/
theorem cutIn_portGraph_liftSet {cloud : ℕ → Graph} {α : ℝ}
    (hcloud : IsCloudExpander cloud α) (G : Graph) (X S : Finset ℕ) :
    (portGraph cloud G X).cutIn (portGraph cloud G X).verts (liftSet G X S) = G.cutIn X S := by
  unfold portGraph Graph.verts
  dsimp only
  rw [cutIn_append, cutIn_origPortEdges_liftSet, cutIn_allCloudEdges_liftSet hcloud, Nat.add_zero]

end MinCostFlow.ExpanderDecomp
