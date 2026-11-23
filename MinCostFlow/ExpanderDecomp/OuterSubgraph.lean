module

public import MinCostFlow.Statement.Cited.ChuzhoyEtAl
public import MinCostFlow.Expander.Components
public import Mathlib.Data.List.Dedup
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Compact subgraphs, connected-component base case, and label arrays

This file defines the compact subgraph representation and label-array builder used by the outer
expander decomposition model:

* **Edge/volume/cut split identities**: `volIn_eq_two_mul_inside_add_cutIn`, `inside_length_split`,
  `two_mul_inside_le_volIn`, `inside_diff_le_volIn`, `inside_length_mono`.
* **Compact subgraphs and isolation stripping**: `CompactSubgraph`,
  `CompactSubgraph.Represents`, `ofGraph`, `stripIsolated`, and `restrict`, maintaining compact
  local vertex and edge lists (`|active.verts| ≤ 2e`).
* **Connected-component base case**: `localGraph` and `componentsOf`, proving that
  when `e ≤ Q` the connected components partition `X`, cut zero edges of `G[X]`, and each have
  conductance at least `1 / Q`.
* **Label array and `partsOf` bridge**: `labelsOfParts`, proving that a partition of
  `G.verts` into nonempty disjoint `Finset ℕ` parts yields a length-`G.n` label list whose `partsOf`
  equals the partition.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-- A compact representation of an induced subgraph `G[X]`, storing its active original vertex IDs
and its induced edges. -/
structure CompactSubgraph where
  /-- Active original vertex IDs (no duplicates). -/
  verts : List ℕ
  /-- Induced edges of `G` with both endpoints in `verts`. -/
  edges : List (ℕ × ℕ)

namespace CompactSubgraph

/-- `H` faithfully represents the induced subgraph `G[X]`. -/
def Represents (H : CompactSubgraph) (G : Graph) (X : Finset ℕ) : Prop :=
  H.verts.Nodup ∧ H.verts.toFinset = X ∧ H.edges = G.inside X

/-- Vertex set of `H` as a `Finset ℕ`. -/
def vertSet (H : CompactSubgraph) : Finset ℕ :=
  H.verts.toFinset

/-- Build the compact subgraph of `G` on `G.verts = {0, …, G.n - 1}`. -/
def ofGraph (G : Graph) : CompactSubgraph :=
  ⟨List.range G.n, G.edges⟩

/-- Split `H` into isolated vertices (not incident to any edge in `H.edges`) and the remaining
active compact subgraph. -/
def stripIsolated (H : CompactSubgraph) : List ℕ × CompactSubgraph :=
  let hasEdge (v : ℕ) : Bool := H.edges.any fun e => decide (e.1 = v) || decide (e.2 = v)
  let iso := H.verts.filter fun v => !hasEdge v
  let act := H.verts.filter hasEdge
  (iso, ⟨act, H.edges⟩)

/-- Restrict `H` to a subset `S` by scanning only `H.verts` and `H.edges`. -/
def restrict (H : CompactSubgraph) (S : Finset ℕ) : CompactSubgraph :=
  ⟨H.verts.filter fun v => decide (v ∈ S),
    H.edges.filter fun e => decide (e.1 ∈ S) && decide (e.2 ∈ S)⟩

/-- Relabel `H` onto compact local vertex IDs `0, …, H.verts.length - 1`. -/
def localGraph (H : CompactSubgraph) : Graph :=
  ⟨H.verts.length, H.edges.map fun e => (H.verts.idxOf e.1, H.verts.idxOf e.2)⟩

/-- Connected components of `H` as original-vertex `Finset ℕ`s, computed via `compLabels` on
`H.localGraph`. -/
def componentsOf (H : CompactSubgraph) : List (Finset ℕ) :=
  let lbl := compLabels H.localGraph
  lbl.dedup.map fun c =>
    ((Finset.range H.verts.length).filter fun i => lbl.getD i 0 = c).image fun i =>
      H.verts.getD i 0

end CompactSubgraph

/-- Paint a single part `P` with label `c` into a label array `lbl` (scanning only `P`). -/
def paintPart (lbl : List ℕ) (P : Finset ℕ) (c : ℕ) : List ℕ :=
  (P.sort (· ≤ ·)).foldl (fun acc v => acc.set v c) lbl

/-- Assign fresh consecutive labels `0, 1, …` to a list of finalized parts, initializing the
length-`n` label array once and writing each vertex once. -/
def labelsOfPartsAux (parts : List (Finset ℕ)) (nextLbl : ℕ) (lbl : List ℕ) : List ℕ :=
  match parts with
  | [] => lbl
  | P :: rest => labelsOfPartsAux rest (nextLbl + 1) (paintPart lbl P nextLbl)

/-- Build the length-`n` label array from a list of finalized parts. -/
def labelsOfParts (n : ℕ) (parts : List (Finset ℕ)) : List ℕ :=
  labelsOfPartsAux parts 0 (List.replicate n 0)

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Edge, volume, and cut split identities -/

/-- For `S ⊆ X`, `vol_{G[X]}(S) = 2 · |E(G[S])| + |∂_{G[X]} S|`. -/
theorem volIn_eq_two_mul_inside_add_cutIn (G : Graph) {X S : Finset ℕ} (hSX : S ⊆ X) :
    G.volIn X S = 2 * (G.inside S).length + G.cutIn X S := by
  have hins : G.inside S = (G.inside X).filter fun e => decide (e.1 ∈ S) && decide (e.2 ∈ S) := by
    unfold Graph.inside
    rw [List.filter_filter]
    apply List.filter_congr
    intro e _
    by_cases h1 : e.1 ∈ S <;> by_cases h2 : e.2 ∈ S
    · simp [h1, h2, hSX h1, hSX h2]
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]
  rw [volIn_eq_sum_map, cutIn_eq_sum_map, hins, length_filter_eq_sum_map]
  suffices h : ∀ l : List (ℕ × ℕ),
      (l.map fun e => (if e.1 ∈ S then 1 else 0) + (if e.2 ∈ S then 1 else 0)).sum =
      2 * (l.map fun e => if (decide (e.1 ∈ S) && decide (e.2 ∈ S)) then 1 else 0).sum +
        (l.map fun e => if (decide (e.1 ∈ S) != decide (e.2 ∈ S)) then 1 else 0).sum from
    h (G.inside X)
  intro l
  induction l with
  | nil => simp
  | cons e t ih =>
    simp only [List.map_cons, List.sum_cons]
    by_cases h1 : e.1 ∈ S <;> by_cases h2 : e.2 ∈ S <;>
      simp only [h1, h2, decide_true, decide_false, Bool.and_true, Bool.and_false,
        bne_self_eq_false, Bool.true_bne, Bool.false_bne, Bool.not_false,
        ↓reduceIte, Bool.false_eq_true] <;>
      omega

/-- For `S ⊆ X`, `|E(G[S])| + |E(G[X \ S])| + |∂_{G[X]} S| = |E(G[X])|`. -/
theorem inside_length_split (G : Graph) {X S : Finset ℕ} (hSX : S ⊆ X) :
    (G.inside S).length + (G.inside (X \ S)).length + G.cutIn X S = (G.inside X).length := by
  have h1 := volIn_eq_two_mul_inside_add_cutIn G hSX
  have h2 := volIn_eq_two_mul_inside_add_cutIn G (Finset.sdiff_subset (s := X) (t := S))
  rw [cutIn_sdiff G X S hSX] at h2
  have hsum := volIn_add_volIn_sdiff G X S hSX
  omega

/-- For `S ⊆ X`, `2 · |E(G[S])| ≤ vol_{G[X]}(S)`. -/
theorem two_mul_inside_le_volIn (G : Graph) {X S : Finset ℕ} (hSX : S ⊆ X) :
    2 * (G.inside S).length ≤ G.volIn X S := by
  have h := volIn_eq_two_mul_inside_add_cutIn G hSX
  omega

/-- For `R ⊆ X`, every edge of `G[X]` not inside `R` contributes to `vol_{G[X]}(X \ R)`. -/
theorem inside_diff_le_volIn (G : Graph) {X R : Finset ℕ} (hRX : R ⊆ X) :
    (G.inside X).length ≤ (G.inside R).length + G.volIn X (X \ R) := by
  have hsplit := inside_length_split G hRX
  have hvol := volIn_eq_two_mul_inside_add_cutIn G (Finset.sdiff_subset (s := X) (t := R))
  rw [cutIn_sdiff G X R hRX] at hvol
  omega

/-- For `S ⊆ X`, `|E(G[S])| ≤ |E(G[X])|`. -/
theorem inside_length_mono (G : Graph) {X S : Finset ℕ} (hSX : S ⊆ X) :
    (G.inside S).length ≤ (G.inside X).length := by
  have h := inside_length_split G hSX
  omega

/-! ### Compact subgraph invariants -/

/-- `CompactSubgraph.ofGraph G` represents `G[G.verts]` for any valid `G`. -/
theorem CompactSubgraph.ofGraph_represents {G : Graph} (hv : G.IsValid) :
    (CompactSubgraph.ofGraph G).Represents G G.verts := by
  refine ⟨List.nodup_range, ?_, (inside_verts_of_isValid hv).symm⟩
  ext v
  simp [CompactSubgraph.ofGraph, Graph.verts]

/-- Restricting a compact subgraph representing `G[X]` to `S ⊆ X` represents `G[S]`. -/
theorem CompactSubgraph.restrict_represents {H : CompactSubgraph} {G : Graph} {X S : Finset ℕ}
    (hH : H.Represents G X) (hSX : S ⊆ X) :
    (H.restrict S).Represents G S := by
  obtain ⟨hnd, htoF, hedges⟩ := hH
  refine ⟨hnd.filter _, ?_, ?_⟩
  · ext v
    simp only [CompactSubgraph.restrict, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact And.right
    · intro hvS
      exact ⟨List.mem_toFinset.mp (htoF.symm ▸ hSX hvS), hvS⟩
  · unfold CompactSubgraph.restrict
    dsimp only
    rw [hedges]
    unfold Graph.inside
    rw [List.filter_filter]
    apply List.filter_congr
    intro e _
    by_cases h1 : e.1 ∈ S <;> by_cases h2 : e.2 ∈ S
    · simp [h1, h2, hSX h1, hSX h2]
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]

/-- Properties of `stripIsolated`:
1. `iso` has no duplicates and every `v ∈ iso` has `G.degIn X v = 0`;
2. `iso.toFinset` and `act.vertSet` are disjoint with union `X`;
3. `act` represents `G[act.vertSet]` with the same edge list `G.inside X`;
4. every vertex in `act.vertSet` has positive degree in `G[act.vertSet]`;
5. `act.verts.length ≤ 2 * act.edges.length`. -/
theorem CompactSubgraph.stripIsolated_spec {H : CompactSubgraph} {G : Graph} {X : Finset ℕ}
    (hH : H.Represents G X) :
    let (iso, act) := H.stripIsolated
    iso.Nodup ∧
      Disjoint iso.toFinset act.vertSet ∧
      iso.toFinset ∪ act.vertSet = X ∧
      (∀ v ∈ iso.toFinset, G.degIn X v = 0) ∧
      act.Represents G act.vertSet ∧
      act.edges = H.edges ∧
      (∀ v ∈ act.vertSet, 1 ≤ G.degIn act.vertSet v) ∧
      act.verts.length ≤ 2 * act.edges.length := by
  obtain ⟨hnd, htoF, hedges⟩ := hH
  set hasEdge : ℕ → Bool := fun v => H.edges.any fun e => decide (e.1 = v) || decide (e.2 = v)
  have hhasEdge_iff : ∀ v, hasEdge v = true ↔ ∃ e ∈ G.inside X, e.1 = v ∨ e.2 = v := by
    intro v
    simp only [hasEdge, hedges, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  have hdeg_pos : ∀ v, hasEdge v = true ↔ 1 ≤ G.degIn X v := by
    intro v
    rw [hhasEdge_iff v, Graph.degIn]
    constructor
    · rintro ⟨e, he, h1 | h2⟩
      · have hmem : e ∈ (G.inside X).filter fun e => e.1 = v :=
          List.mem_filter.mpr ⟨he, by simp [h1]⟩
        have hpos : 0 < ((G.inside X).filter fun e => e.1 = v).length :=
          List.length_pos_of_mem hmem
        omega
      · have hmem : e ∈ (G.inside X).filter fun e => e.2 = v :=
          List.mem_filter.mpr ⟨he, by simp [h2]⟩
        have hpos : 0 < ((G.inside X).filter fun e => e.2 = v).length :=
          List.length_pos_of_mem hmem
        omega
    · intro hge
      by_cases h1 : 0 < ((G.inside X).filter fun e => e.1 = v).length
      · obtain ⟨e, he⟩ := List.exists_mem_of_length_pos h1
        rw [List.mem_filter, decide_eq_true_eq] at he
        exact ⟨e, he.1, Or.inl he.2⟩
      · have h2 : 0 < ((G.inside X).filter fun e => e.2 = v).length := by omega
        obtain ⟨e, he⟩ := List.exists_mem_of_length_pos h2
        rw [List.mem_filter, decide_eq_true_eq] at he
        exact ⟨e, he.1, Or.inr he.2⟩
  dsimp only [CompactSubgraph.stripIsolated]
  set iso := H.verts.filter fun v => !hasEdge v
  set act : CompactSubgraph := ⟨H.verts.filter hasEdge, H.edges⟩
  have hiso_nd : iso.Nodup := hnd.filter _
  have hact_nd : act.verts.Nodup := hnd.filter _
  have hdisj : Disjoint iso.toFinset act.vertSet := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [iso, act, CompactSubgraph.vertSet, List.mem_toFinset, List.mem_filter,
      Bool.not_eq_true'] at hv1 hv2
    rw [hv1.2] at hv2
    exact Bool.false_ne_true hv2.2
  have hunion : iso.toFinset ∪ act.vertSet = X := by
    ext v
    simp only [Finset.mem_union, iso, act, CompactSubgraph.vertSet, List.mem_toFinset,
      List.mem_filter, Bool.not_eq_true']
    rw [← htoF, List.mem_toFinset]
    cases hasEdge v <;> simp
  have hiso_deg : ∀ v ∈ iso.toFinset, G.degIn X v = 0 := by
    intro v hv
    simp only [iso, List.mem_toFinset, List.mem_filter, Bool.not_eq_true'] at hv
    have hnot : ¬ (1 ≤ G.degIn X v) := by
      rw [← hdeg_pos v, hv.2]
      exact Bool.false_ne_true
    omega
  have hins_eq : G.inside act.vertSet = G.inside X := by
    have hact_sub : act.vertSet ⊆ X := by rw [← hunion]; exact Finset.subset_union_right
    unfold Graph.inside
    apply List.filter_congr
    intro e he
    by_cases hX1 : e.1 ∈ X <;> by_cases hX2 : e.2 ∈ X
    · have hein : e ∈ G.inside X := mem_inside_iff.mpr ⟨he, hX1, hX2⟩
      have h1 : hasEdge e.1 = true := (hhasEdge_iff e.1).mpr ⟨e, hein, Or.inl rfl⟩
      have h2 : hasEdge e.2 = true := (hhasEdge_iff e.2).mpr ⟨e, hein, Or.inr rfl⟩
      have hm1 : e.1 ∈ act.vertSet := by
        simp only [act, CompactSubgraph.vertSet, List.mem_toFinset, List.mem_filter]
        exact ⟨List.mem_toFinset.mp (htoF.symm ▸ hX1), h1⟩
      have hm2 : e.2 ∈ act.vertSet := by
        simp only [act, CompactSubgraph.vertSet, List.mem_toFinset, List.mem_filter]
        exact ⟨List.mem_toFinset.mp (htoF.symm ▸ hX2), h2⟩
      simp [hX1, hX2, hm1, hm2]
    · have hm2 : e.2 ∉ act.vertSet := fun h => hX2 (hact_sub h)
      simp [hX1, hX2, hm2]
    · have hm1 : e.1 ∉ act.vertSet := fun h => hX1 (hact_sub h)
      simp [hX1, hX2, hm1]
    · have hm1 : e.1 ∉ act.vertSet := fun h => hX1 (hact_sub h)
      simp [hX1, hX2, hm1]
  have hact_rep : act.Represents G act.vertSet :=
    ⟨hact_nd, rfl, hedges.trans hins_eq.symm⟩
  have hact_deg : ∀ v ∈ act.vertSet, 1 ≤ G.degIn act.vertSet v := by
    intro v hv
    have h1 : hasEdge v = true := by
      simp only [act, CompactSubgraph.vertSet, List.mem_toFinset, List.mem_filter] at hv
      exact hv.2
    have h2 : 1 ≤ G.degIn X v := (hdeg_pos v).mp h1
    simpa only [Graph.degIn, hins_eq] using h2
  have hact_len : act.verts.length ≤ 2 * act.edges.length := by
    have hcard : act.vertSet.card = act.verts.length :=
      List.toFinset_card_of_nodup hact_nd
    have hsum : act.vertSet.card ≤ G.volIn act.vertSet act.vertSet := by
      unfold Graph.volIn
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum hact_deg
    rw [volIn_self, ← hact_rep.2.2] at hsum
    omega
  exact ⟨hiso_nd, hdisj, hunion, hiso_deg, hact_rep, rfl, hact_deg, hact_len⟩

/-! ### Connected-component base case (`e ≤ Q`) -/

/-- `H.localGraph` is valid whenever `H` represents `G[X]`. -/
theorem CompactSubgraph.localGraph_isValid {H : CompactSubgraph} {G : Graph} {X : Finset ℕ}
    (hH : H.Represents G X) : H.localGraph.IsValid := by
  obtain ⟨_, htoF, hedges⟩ := hH
  intro e he
  simp only [CompactSubgraph.localGraph, List.mem_map] at he
  obtain ⟨f, hf, rfl⟩ := he
  rw [hedges, mem_inside_iff] at hf
  have h1 : f.1 ∈ H.verts := List.mem_toFinset.mp (htoF.symm ▸ hf.2.1)
  have h2 : f.2 ∈ H.verts := List.mem_toFinset.mp (htoF.symm ▸ hf.2.2)
  exact ⟨List.idxOf_lt_length_of_mem h1, List.idxOf_lt_length_of_mem h2⟩

private theorem getD_idxOf_eq {l : List ℕ} {v : ℕ} (hv : v ∈ l) :
    l.getD (l.idxOf v) 0 = v := by
  have hi : l.idxOf v < l.length := List.idxOf_lt_length_of_mem hv
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_idxOf hi

private theorem idxOf_getD_eq {l : List ℕ} (hnd : l.Nodup) {i : ℕ} (hi : i < l.length) :
    l.idxOf (l.getD i 0) = i := by
  rw [List.getD_eq_getElem _ _ hi]
  have hmem : l[i] ∈ l := List.getElem_mem hi
  have hj : l.idxOf l[i] < l.length := List.idxOf_lt_length_of_mem hmem
  exact (List.Nodup.getElem_inj_iff hnd).mp (List.getElem_idxOf hj)

/-- **Base case**: when `H` represents `G[X]` and `H.edges.length ≤ Q` (`1 ≤ Q`),
`H.componentsOf` is a list of pairwise disjoint nonempty subsets of `X` whose union is `X`, such
that:
1. every component `C ∈ H.componentsOf` has conductance at least `1 / Q` in `G`;
2. every component `C ∈ H.componentsOf` has `G.cutIn X C = 0`. -/
theorem CompactSubgraph.componentsOf_spec {H : CompactSubgraph} {G : Graph} {X : Finset ℕ}
    (hH : H.Represents G X) {Q : ℕ} (hQ : 1 ≤ Q) (he : H.edges.length ≤ Q) :
    H.componentsOf.Nodup ∧
      (∀ C ∈ H.componentsOf, C.Nonempty ∧ C ⊆ X) ∧
      H.componentsOf.Pairwise Disjoint ∧
      H.componentsOf.toFinset.biUnion id = X ∧
      (∀ C ∈ H.componentsOf, G.IsConductanceExpanderOn C (1 / (Q : ℝ))) ∧
      (∀ C ∈ H.componentsOf, G.cutIn X C = 0) := by
  obtain ⟨hnd, htoF, hedges⟩ := hH
  have hval : H.localGraph.IsValid := CompactSubgraph.localGraph_isValid ⟨hnd, htoF, hedges⟩
  set L := H.localGraph
  set lbl := compLabels L
  have hlen : lbl.length = H.verts.length := compLabels_length L
  set φ : ℕ → ℕ := fun i => H.verts.getD i 0
  have hφ_inj : ∀ i < H.verts.length, ∀ j < H.verts.length, φ i = φ j → i = j := by
    intro i hi j hj hij
    simp only [φ, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at hij
    exact (List.Nodup.getElem_inj_iff hnd).mp hij
  have hφ_mem : ∀ i < H.verts.length, φ i ∈ X := by
    intro i hi
    rw [← htoF, List.mem_toFinset]
    simp only [φ, List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  set partOf : ℕ → Finset ℕ := fun c =>
    (Finset.range H.verts.length).filter fun i => lbl.getD i 0 = c
  have hpart_mem_partsOf : ∀ c ∈ lbl.dedup, partOf c ∈ partsOf L lbl := by
    intro c hc
    rw [List.mem_dedup] at hc
    obtain ⟨i, hi, hic⟩ := List.getElem_of_mem hc
    have hiL : i < H.verts.length := by rw [← hlen]; exact hi
    have hget : lbl.getD i 0 = c := by rw [List.getD_eq_getElem _ _ hi, hic]
    rw [mem_partsOf_iff]
    refine ⟨i, Finset.mem_range.mpr hiL, ?_⟩
    ext j
    simp only [partOf, L, CompactSubgraph.localGraph, Graph.verts, Finset.mem_filter,
      Finset.mem_range, hget]
  have hpart_ne : ∀ c ∈ lbl.dedup, (partOf c).Nonempty := fun c hc =>
    partsOf_nonempty (hpart_mem_partsOf c hc)
  have hdisj_c : ∀ c₁ c₂, c₁ ≠ c₂ → Disjoint ((partOf c₁).image φ) ((partOf c₂).image φ) := by
    intro c₁ c₂ hne
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    rw [Finset.mem_image] at hv1 hv2
    obtain ⟨i, hi, rfl⟩ := hv1
    obtain ⟨j, hj, hij⟩ := hv2
    simp only [partOf, Finset.mem_filter, Finset.mem_range] at hi hj
    have heq : j = i := hφ_inj j hj.1 i hi.1 hij
    subst heq
    exact hne (hi.2.symm.trans hj.2)
  have hcomp_nodup : H.componentsOf.Nodup := by
    unfold CompactSubgraph.componentsOf
    dsimp only
    rw [List.nodup_map_iff_inj_on (List.nodup_dedup lbl)]
    intro c₁ hc₁ c₂ hc₂ heq
    by_contra hne
    have hdisj := hdisj_c c₁ c₂ hne
    have hnonempty : ((partOf c₁).image φ).Nonempty := (hpart_ne c₁ hc₁).image φ
    obtain ⟨v, hv⟩ := hnonempty
    exact Finset.disjoint_left.mp hdisj hv (heq ▸ hv)
  have hcomp_ne_sub : ∀ C ∈ H.componentsOf, C.Nonempty ∧ C ⊆ X := by
    intro C hC
    unfold CompactSubgraph.componentsOf at hC
    rw [List.mem_map] at hC
    obtain ⟨c, hc, rfl⟩ := hC
    refine ⟨(hpart_ne c hc).image φ, ?_⟩
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    exact hφ_mem i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
  have hcomp_pw : H.componentsOf.Pairwise Disjoint := by
    unfold CompactSubgraph.componentsOf
    dsimp only
    rw [List.pairwise_map]
    exact (List.nodup_dedup lbl).imp fun hne => hdisj_c _ _ hne
  have hcomp_union : H.componentsOf.toFinset.biUnion id = X := by
    ext v
    simp only [Finset.mem_biUnion, id_eq, List.mem_toFinset, CompactSubgraph.componentsOf,
      List.mem_map, List.mem_dedup]
    constructor
    · rintro ⟨C, ⟨c, hc, rfl⟩, hv⟩
      exact (hcomp_ne_sub _ (by
        unfold CompactSubgraph.componentsOf
        exact List.mem_map.mpr ⟨c, List.mem_dedup.mpr hc, rfl⟩)).2 hv
    · intro hvX
      have hv_mem : v ∈ H.verts := List.mem_toFinset.mp (htoF.symm ▸ hvX)
      set i := H.verts.idxOf v
      have hi : i < H.verts.length := List.idxOf_lt_length_of_mem hv_mem
      have hi_lbl : i < lbl.length := by rw [hlen]; exact hi
      set c := lbl.getD i 0
      have hc : c ∈ lbl := by
        simp only [c, List.getD_eq_getElem _ _ hi_lbl]
        exact List.getElem_mem hi_lbl
      refine ⟨(partOf c).image φ, ⟨c, hc, rfl⟩, ?_⟩
      rw [Finset.mem_image]
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, rfl⟩, ?_⟩
      exact getD_idxOf_eq hv_mem
  have hcut_bridge : ∀ (P S' : Finset ℕ), P ⊆ Finset.range H.verts.length → S' ⊆ P →
      G.cutIn (P.image φ) (S'.image φ) = L.cutIn P S' := by
    intro P S' hP hS'
    have hmem_img : ∀ (T : Finset ℕ), T ⊆ Finset.range H.verts.length →
        ∀ u ∈ X, u ∈ T.image φ ↔ H.verts.idxOf u ∈ T := by
      intro T hT u huX
      have hu_mem : u ∈ H.verts := List.mem_toFinset.mp (htoF.symm ▸ huX)
      constructor
      · intro hu
        rw [Finset.mem_image] at hu
        obtain ⟨j, hjT, hjφ⟩ := hu
        have hj : j < H.verts.length := Finset.mem_range.mp (hT hjT)
        have hidx : H.verts.idxOf u = j := by
          rw [← hjφ]
          exact idxOf_getD_eq hnd hj
        rwa [hidx]
      · intro huT
        exact Finset.mem_image.mpr ⟨H.verts.idxOf u, huT, getD_idxOf_eq hu_mem⟩
    have hS'sub : S' ⊆ Finset.range H.verts.length := hS'.trans hP
    have hins_L : L.inside P =
        (H.edges.filter fun e => decide (H.verts.idxOf e.1 ∈ P) && decide (H.verts.idxOf e.2 ∈ P)).map
          fun e => (H.verts.idxOf e.1, H.verts.idxOf e.2) := by
      unfold Graph.inside L CompactSubgraph.localGraph
      dsimp only
      rw [List.filter_map]
      rfl
    have hPsubX : P.image φ ⊆ X := by
      intro u hu
      rw [Finset.mem_image] at hu
      obtain ⟨j, hj, rfl⟩ := hu
      exact hφ_mem j (Finset.mem_range.mp (hP hj))
    have hins_G : G.inside (P.image φ) =
        H.edges.filter fun e => decide (H.verts.idxOf e.1 ∈ P) && decide (H.verts.idxOf e.2 ∈ P) := by
      have h1 : G.inside (P.image φ) =
          (G.inside X).filter fun e => decide (e.1 ∈ P.image φ) && decide (e.2 ∈ P.image φ) := by
        unfold Graph.inside
        rw [List.filter_filter]
        apply List.filter_congr
        intro e _
        by_cases a1 : e.1 ∈ P.image φ <;> by_cases a2 : e.2 ∈ P.image φ
        · simp [a1, a2, hPsubX a1, hPsubX a2]
        · simp [a1, a2]
        · simp [a1, a2]
        · simp [a1, a2]
      rw [h1, ← hedges]
      apply List.filter_congr
      intro e he
      rw [hedges, mem_inside_iff] at he
      simp [hmem_img P hP e.1 he.2.1, hmem_img P hP e.2 he.2.2]
    rw [cutIn_eq_sum_map, cutIn_eq_sum_map, hins_G, hins_L, List.map_map]
    congr 1
    apply List.map_congr_left
    intro e he
    rw [List.mem_filter, hedges, mem_inside_iff] at he
    simp only [Function.comp_apply, hmem_img S' hS'sub e.1 he.1.2.1, hmem_img S' hS'sub e.2 he.1.2.2]
  have hcomp_exp : ∀ C ∈ H.componentsOf, G.IsConductanceExpanderOn C (1 / (Q : ℝ)) := by
    intro C hC S hSC hSne hSneC
    unfold CompactSubgraph.componentsOf at hC
    rw [List.mem_map] at hC
    obtain ⟨c, hc, rfl⟩ := hC
    set P := partOf c
    have hPsub : P ⊆ Finset.range H.verts.length := Finset.filter_subset _ _
    have hPmem : P ∈ partsOf L lbl := hpart_mem_partsOf c hc
    set S' := P.filter fun i => φ i ∈ S
    have hS'sub : S' ⊆ P := Finset.filter_subset _ _
    have hS_eq : S'.image φ = S := by
      ext v
      simp only [Finset.mem_image, S', Finset.mem_filter]
      constructor
      · rintro ⟨i, ⟨_, hiS⟩, rfl⟩; exact hiS
      · intro hvS
        have hvP := hSC hvS
        rw [Finset.mem_image] at hvP
        obtain ⟨i, hiP, rfl⟩ := hvP
        exact ⟨i, ⟨hiP, hvS⟩, rfl⟩
    have hS'ne : S'.Nonempty := by
      obtain ⟨v, hvS⟩ := hSne
      rw [← hS_eq, Finset.mem_image] at hvS
      obtain ⟨i, hi, _⟩ := hvS
      exact ⟨i, hi⟩
    have hS'neP : S' ≠ P := by
      intro heq
      apply hSneC
      rw [← hS_eq, heq]
    have hcut1 : 1 ≤ G.cutIn (P.image φ) S := by
      rw [← hS_eq, hcut_bridge P S' hPsub hS'sub]
      exact cutIn_ge_one_of_part_compLabels hval hPmem hS'sub hS'ne hS'neP
    have hCX : P.image φ ⊆ X := by
      intro v hv
      rw [Finset.mem_image] at hv
      obtain ⟨i, hi, rfl⟩ := hv
      exact hφ_mem i (Finset.mem_range.mp (hPsub hi))
    have hvol_sum := volIn_add_volIn_sdiff G (P.image φ) S hSC
    have hins_le : (G.inside (P.image φ)).length ≤ Q := by
      calc (G.inside (P.image φ)).length ≤ (G.inside X).length := inside_length_mono G hCX
        _ = H.edges.length := congrArg List.length hedges.symm
        _ ≤ Q := he
    have hmin_le : min (G.volIn (P.image φ) S) (G.volIn (P.image φ) (P.image φ \ S)) ≤ Q := by
      omega
    have hmin_r : min (G.volIn (P.image φ) S : ℝ) (G.volIn (P.image φ) (P.image φ \ S) : ℝ) ≤
        (Q : ℝ) := by
      have : (min (G.volIn (P.image φ) S) (G.volIn (P.image φ) (P.image φ \ S)) : ℝ) ≤ (Q : ℝ) := by
        exact_mod_cast hmin_le
      simpa [Nat.cast_min] using this
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hcut1_r : (1 : ℝ) ≤ (G.cutIn (P.image φ) S : ℝ) := by exact_mod_cast hcut1
    calc (1 : ℝ) / (Q : ℝ) *
          min (G.volIn (P.image φ) S : ℝ) (G.volIn (P.image φ) (P.image φ \ S) : ℝ)
        ≤ (1 : ℝ) / (Q : ℝ) * (Q : ℝ) := by gcongr
      _ = 1 := by field_simp
      _ ≤ (G.cutIn (P.image φ) S : ℝ) := hcut1_r
  have hcomp_cut0 : ∀ C ∈ H.componentsOf, G.cutIn X C = 0 := by
    intro C hC
    unfold CompactSubgraph.componentsOf at hC
    rw [List.mem_map] at hC
    obtain ⟨c, hc, rfl⟩ := hC
    set P := partOf c
    have hPsub : P ⊆ Finset.range H.verts.length := Finset.filter_subset _ _
    have hX_img : (Finset.range H.verts.length).image φ = X := by
      ext v
      simp only [Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact hφ_mem i hi
      · intro hvX
        have hv_mem : v ∈ H.verts := List.mem_toFinset.mp (htoF.symm ▸ hvX)
        exact ⟨H.verts.idxOf v, List.idxOf_lt_length_of_mem hv_mem, getD_idxOf_eq hv_mem⟩
    rw [← hX_img, hcut_bridge (Finset.range H.verts.length) P (Finset.Subset.refl _) hPsub]
    exact cut_part_compLabels_eq_zero hval (hpart_mem_partsOf c hc)
  exact ⟨hcomp_nodup, hcomp_ne_sub, hcomp_pw, hcomp_union, hcomp_exp, hcomp_cut0⟩

/-! ### Label array and `partsOf` bridge -/

private theorem paintPart_length (lbl : List ℕ) (P : Finset ℕ) (c : ℕ) :
    (paintPart lbl P c).length = lbl.length := by
  unfold paintPart
  suffices h : ∀ l : List ℕ, ∀ acc : List ℕ,
      (l.foldl (fun acc v => acc.set v c) acc).length = acc.length from
    h (P.sort (· ≤ ·)) lbl
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons a t ih =>
    intro acc
    simp only [List.foldl_cons, ih, List.length_set]

private theorem paintPart_getD (lbl : List ℕ) (P : Finset ℕ) (c : ℕ) {v : ℕ}
    (hv : v < lbl.length) :
    (paintPart lbl P c).getD v 0 = if v ∈ P then c else lbl.getD v 0 := by
  unfold paintPart
  have hmem : ∀ x, x ∈ P.sort (· ≤ ·) ↔ x ∈ P := fun x => Finset.mem_sort (· ≤ ·)
  suffices h : ∀ l : List ℕ, ∀ acc : List ℕ, v < acc.length →
      (l.foldl (fun acc u => acc.set u c) acc).getD v 0 =
        if v ∈ l then c else acc.getD v 0 by
    rw [h (P.sort (· ≤ ·)) lbl hv]
    simp [hmem v]
  intro l
  induction l with
  | nil => intro acc _; simp
  | cons a t ih =>
    intro acc hacc
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih (acc.set a c) (by simpa using hacc)]
    by_cases hvt : v ∈ t
    · simp [hvt]
    · simp only [hvt, or_false, ↓reduceIte]
      by_cases hva : v = a
      · subst hva
        simp [List.getD, List.getElem?_set_self hacc]
      · simp [hva, List.getD, List.getElem?_set_ne (Ne.symm hva)]

private theorem labelsOfPartsAux_length (parts : List (Finset ℕ)) (k : ℕ) (lbl : List ℕ) :
    (labelsOfPartsAux parts k lbl).length = lbl.length := by
  induction parts generalizing k lbl with
  | nil => rfl
  | cons P rest ih =>
    simp only [labelsOfPartsAux, ih, paintPart_length]

private theorem labelsOfPartsAux_getD {parts : List (Finset ℕ)} {k : ℕ} {lbl : List ℕ}
    (hpw : parts.Pairwise Disjoint) {v : ℕ} (hv : v < lbl.length) :
    (∀ i (hi : i < parts.length), v ∈ parts[i] →
      (labelsOfPartsAux parts k lbl).getD v 0 = k + i) ∧
    ((∀ P ∈ parts, v ∉ P) → (labelsOfPartsAux parts k lbl).getD v 0 = lbl.getD v 0) := by
  induction parts generalizing k lbl with
  | nil =>
    exact ⟨fun i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | cons P rest ih =>
    rw [List.pairwise_cons] at hpw
    have hv' : v < (paintPart lbl P k).length := by rw [paintPart_length]; exact hv
    have ⟨ih1, ih2⟩ := ih (k := k + 1) (lbl := paintPart lbl P k) hpw.2 hv'
    constructor
    · intro i hi hvi
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero] at hvi
        simp only [labelsOfPartsAux, Nat.add_zero]
        have hnotrest : ∀ Q ∈ rest, v ∉ Q := fun Q hQ hvQ =>
          Finset.disjoint_left.mp (hpw.1 Q hQ) hvi hvQ
        rw [ih2 hnotrest, paintPart_getD lbl P k hv]
        simp [hvi]
      | succ j =>
        simp only [List.getElem_cons_succ] at hvi
        simp only [labelsOfPartsAux]
        have hj : j < rest.length := by simp only [List.length_cons] at hi; omega
        have h := ih1 j hj hvi
        omega
    · intro hnone
      simp only [labelsOfPartsAux]
      have hnotP : v ∉ P := hnone P List.mem_cons_self
      have hnotrest : ∀ Q ∈ rest, v ∉ Q := fun Q hQ => hnone Q (List.mem_cons_of_mem _ hQ)
      rw [ih2 hnotrest, paintPart_getD lbl P k hv]
      simp [hnotP]

/-- **Labels and `partsOf`**: given a list `parts` of pairwise disjoint nonempty
subsets of `G.verts` whose union is `G.verts`, `labelsOfParts G.n parts` has length `G.n`, gives
each vertex in `parts[i]` the label `i`, and satisfies `partsOf G (labelsOfParts G.n parts) =
parts.toFinset`. -/
theorem labelsOfParts_spec {G : Graph} {parts : List (Finset ℕ)}
    (hne : ∀ P ∈ parts, P.Nonempty) (hpw : parts.Pairwise Disjoint)
    (hcov : parts.toFinset.biUnion id = G.verts) :
    (labelsOfParts G.n parts).length = G.n ∧
      partsOf G (labelsOfParts G.n parts) = parts.toFinset ∧
      ∀ i (hi : i < parts.length), ∀ v ∈ parts[i],
        (labelsOfParts G.n parts).getD v 0 = i := by
  have hlen : (labelsOfParts G.n parts).length = G.n := by
    unfold labelsOfParts
    rw [labelsOfPartsAux_length, List.length_replicate]
  have hsub : ∀ P ∈ parts, P ⊆ G.verts := by
    intro P hP v hv
    rw [← hcov, Finset.mem_biUnion]
    exact ⟨P, List.mem_toFinset.mpr hP, hv⟩
  have hget : ∀ i (hi : i < parts.length), ∀ v ∈ parts[i],
      (labelsOfParts G.n parts).getD v 0 = i := by
    intro i hi v hv
    have hv_lt : v < (List.replicate G.n 0).length := by
      rw [List.length_replicate]
      exact Finset.mem_range.mp (hsub parts[i] (List.getElem_mem hi) hv)
    have h := (labelsOfPartsAux_getD (k := 0) hpw hv_lt).1 i hi hv
    simpa [labelsOfParts] using h
  have hparts : partsOf G (labelsOfParts G.n parts) = parts.toFinset := by
    ext X
    rw [mem_partsOf_iff, List.mem_toFinset]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [← hcov, Finset.mem_biUnion] at hv
      obtain ⟨P, hPmem, hvP⟩ := hv
      rw [List.mem_toFinset] at hPmem
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hPmem
      have hlbl_v : (labelsOfParts G.n parts).getD v 0 = i := hget i hi v hvP
      suffices heq : G.verts.filter (fun x =>
          (labelsOfParts G.n parts).getD x 0 = (labelsOfParts G.n parts).getD v 0) = parts[i] by
        rw [heq]
        exact List.getElem_mem hi
      ext x
      simp only [Finset.mem_filter, hlbl_v]
      constructor
      · rintro ⟨hx, hlbl_x⟩
        rw [← hcov, Finset.mem_biUnion] at hx
        obtain ⟨Q, hQmem, hxQ⟩ := hx
        rw [List.mem_toFinset] at hQmem
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hQmem
        have hlbl_x' := hget j hj x hxQ
        have hij : j = i := hlbl_x'.symm.trans hlbl_x
        subst hij
        exact hxQ
      · intro hx
        exact ⟨hsub parts[i] (List.getElem_mem hi) hx, hget i hi x hx⟩
    · intro hX
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hX
      obtain ⟨v, hv⟩ := hne parts[i] (List.getElem_mem hi)
      refine ⟨v, hsub parts[i] (List.getElem_mem hi) hv, ?_⟩
      have hlbl_v : (labelsOfParts G.n parts).getD v 0 = i := hget i hi v hv
      ext x
      simp only [Finset.mem_filter, hlbl_v]
      constructor
      · intro hx
        exact ⟨hsub parts[i] (List.getElem_mem hi) hx, hget i hi x hx⟩
      · rintro ⟨hx, hlbl_x⟩
        rw [← hcov, Finset.mem_biUnion] at hx
        obtain ⟨Q, hQmem, hxQ⟩ := hx
        rw [List.mem_toFinset] at hQmem
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hQmem
        have hlbl_x' := hget j hj x hxQ
        have hij : j = i := hlbl_x'.symm.trans hlbl_x
        subst hij
        exact hxQ
  exact ⟨hlen, hparts, hget⟩

/-- An edge has distinct labels under `labelsOfParts` if and only if no single part contains both
of its endpoints. -/
theorem filter_diff_labelsOfParts_eq {G : Graph} {parts : List (Finset ℕ)}
    (hne : ∀ P ∈ parts, P.Nonempty) (hpw : parts.Pairwise Disjoint)
    (hcov : parts.toFinset.biUnion id = G.verts) {e : ℕ × ℕ}
    (he1 : e.1 ∈ G.verts) (he2 : e.2 ∈ G.verts) :
    (labelsOfParts G.n parts).getD e.1 0 ≠ (labelsOfParts G.n parts).getD e.2 0 ↔
      ∀ P ∈ parts, ¬ (e.1 ∈ P ∧ e.2 ∈ P) := by
  have hget := (labelsOfParts_spec hne hpw hcov).2.2
  constructor
  · intro hne_lbl P hP ⟨h1, h2⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hP
    rw [hget i hi e.1 h1, hget i hi e.2 h2] at hne_lbl
    exact hne_lbl rfl
  · intro hno heq
    rw [← hcov, Finset.mem_biUnion] at he1 he2
    obtain ⟨P, hP, h1⟩ := he1
    obtain ⟨Q, hQ, h2⟩ := he2
    rw [List.mem_toFinset] at hP hQ
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hP
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hQ
    rw [hget i hi e.1 h1, hget j hj e.2 h2] at heq
    subst heq
    exact hno parts[i] (List.getElem_mem hi) ⟨h1, h2⟩

end MinCostFlow.ExpanderDecomp
