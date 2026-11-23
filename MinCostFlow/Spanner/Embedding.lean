module

public import MinCostFlow.Statement.Cited.Graphs
public import Mathlib.Data.Finset.Fold
public import Mathlib.Data.List.GetD

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Graph embeddings and congestion

This file formalizes graph walks, graph embeddings, edge and vertex congestion (`econg`, `vcong`),
embedding length, and composition of embeddings over `Cited.Graph`, following Section 2 (page 7) of
the paper, and proves **Fact 1** (page 7).

A graph is a `Cited.Graph` (vertices `0, …, n - 1`, edge number `j` is `edges[j]`), and weights
are functions `ℕ → ℝ` on edge numbers. A path/walk in a graph is given explicitly by its vertex
list and edge-number list (`Walk`), with the empty walk `Walk.empty` (used for self-loops whose
embedding path is empty) having no edges and no vertices.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-- A walk in a multigraph, given explicitly by its sequence of vertices `verts` and edge numbers
`edges`. An empty path (for a self-loop) has `verts = []` and `edges = []`. -/
structure Walk where
  /-- The sequence of vertices along the walk. -/
  verts : List ℕ
  /-- The sequence of edge numbers along the walk. -/
  edges : List ℕ
  deriving DecidableEq

namespace Walk

/-- The empty walk, used as the trivial embedding path of a self-loop. -/
def empty : Walk :=
  ⟨[], []⟩

/-- An undirected edge `e = (a, b)` matches the ordered pair `(x, y)`. -/
def EdgeMatches (e : ℕ × ℕ) (x y : ℕ) : Prop :=
  (e.1 = x ∧ e.2 = y) ∨ (e.2 = x ∧ e.1 = y)

/-- `P` is a valid `u`-`v` walk in `H`: either `P = empty` with `u = v < H.n`, or `P` has at least
one edge, `verts.length = edges.length + 1`, starts at `u`, ends at `v`, and each step uses an
edge of `H` joining the consecutive vertices. -/
def IsWalk (H : Graph) (u v : ℕ) (P : Walk) : Prop :=
  u < H.n ∧ v < H.n ∧
    ((P.verts = [] ∧ P.edges = [] ∧ u = v) ∨
     (P.edges ≠ [] ∧ P.verts.length = P.edges.length + 1 ∧
      P.verts.head? = some u ∧ P.verts.getLast? = some v ∧
      (∀ j ∈ P.edges, j < H.m) ∧
      (∀ i : ℕ, i < P.edges.length →
        EdgeMatches (H.edges.getD (P.edges.getD i 0) (0, 0))
          (P.verts.getD i 0) (P.verts.getD (i + 1) 0))))

/-- A single-edge walk from `u` to `v` along edge number `j`. -/
def single (u v j : ℕ) : Walk :=
  ⟨[u, v], [j]⟩

/-- Reverse of a walk (`rev(P)` in Section 2, page 5–6). -/
def reverse (P : Walk) : Walk :=
  ⟨P.verts.reverse, P.edges.reverse⟩

/-- Concatenation `P ⊕ Q` of two walks (`prelims.tex`, Section 2, page 6). -/
def append (P Q : Walk) : Walk :=
  if P.edges.isEmpty then Q
  else if Q.edges.isEmpty then P
  else ⟨P.verts ++ Q.verts.tail, P.edges ++ Q.edges⟩

/-- Map the edge numbers of a walk along `f`, keeping the vertex sequence unchanged. -/
def mapEdges (f : ℕ → ℕ) (P : Walk) : Walk :=
  ⟨P.verts, P.edges.map f⟩

/-- Map the vertex numbers of a walk along `g`, keeping the edge-number sequence unchanged. -/
def mapVerts (g : ℕ → ℕ) (P : Walk) : Walk :=
  ⟨P.verts.map g, P.edges⟩

theorem edgeMatches_symm {e : ℕ × ℕ} {x y : ℕ} (h : EdgeMatches e x y) :
    EdgeMatches e y x := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h2, h1⟩
  · exact Or.inl ⟨h2, h1⟩

theorem append_empty_left (P : Walk) : empty.append P = P := by
  simp [append, empty]

theorem append_empty_right (P : Walk) (hP : P.edges = [] → P = empty) :
    P.append empty = P := by
  unfold append
  split_ifs with h1 h2
  · exact (hP (List.isEmpty_iff.mp h1)).symm
  · rfl
  · simp [empty] at h2

theorem edges_append (P Q : Walk) : (P.append Q).edges = P.edges ++ Q.edges := by
  unfold append
  split_ifs with h1 h2
  · have hP : P.edges = [] := List.isEmpty_iff.mp h1
    simp [hP]
  · have hQ : Q.edges = [] := List.isEmpty_iff.mp h2
    simp [hQ]
  · rfl

theorem mem_verts_append_left {P Q : Walk} {x : ℕ} (hx : x ∈ (P.append Q).verts) :
    x ∈ P.verts ∨ x ∈ Q.verts := by
  unfold append at hx
  split_ifs at hx
  · exact Or.inr hx
  · exact Or.inl hx
  · rcases List.mem_append.mp hx with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_of_mem_tail h)

theorem mem_verts_append_iff {H : Graph} {u w v : ℕ} {P Q : Walk}
    (hP : P.IsWalk H u w) (hQ : Q.IsWalk H w v) (x : ℕ) :
    x ∈ (P.append Q).verts ↔ x ∈ P.verts ∨ x ∈ Q.verts := by
  constructor
  · exact mem_verts_append_left
  · unfold append
    split_ifs with h1 h2
    · have hPe : P.edges = [] := List.isEmpty_iff.mp h1
      rcases hP.2.2 with ⟨hPv, _, _⟩ | ⟨hne, _⟩
      · simp [hPv]
      · exact (hne hPe).elim
    · have hQe : Q.edges = [] := List.isEmpty_iff.mp h2
      rcases hQ.2.2 with ⟨hQv, _, _⟩ | ⟨hne, _⟩
      · simp [hQv]
      · exact (hne hQe).elim
    · intro hx
      rcases hx with hx | hx
      · exact List.mem_append_left _ hx
      · rcases hP.2.2 with ⟨_, hPe, _⟩ | ⟨_, _, _, hPlast, _⟩
        · exact absurd (List.isEmpty_iff.mpr hPe) h1
        · rcases hQ.2.2 with ⟨_, hQe, _⟩ | ⟨_, _, hQhead, _⟩
          · exact absurd (List.isEmpty_iff.mpr hQe) h2
          · cases hQv : Q.verts with
            | nil => simp [hQv] at hQhead
            | cons qh qt =>
              rw [hQv] at hQhead hx
              simp only [List.head?_cons, Option.some.injEq] at hQhead
              subst hQhead
              rcases List.mem_cons.mp hx with rfl | hx'
              · exact List.mem_append_left _ (List.mem_of_getLast? hPlast)
              · exact List.mem_append_right _ (by simp [hx'])

theorem isWalk_single {H : Graph} {u v j : ℕ} (hu : u < H.n) (hv : v < H.n) (hj : j < H.m)
    (hm : EdgeMatches (H.edges.getD j (0, 0)) u v) :
    (single u v j).IsWalk H u v := by
  refine ⟨hu, hv, Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [single]
  · simp [single]
  · simp [single]
  · simp [single]
  · simp [single, hj]
  · intro i hi
    simp only [single, List.length_singleton] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    simpa [single, List.getD_eq_getElem?_getD] using hm

private theorem getD_reverse_eq {α : Type*} (l : List α) (d : α) {i : ℕ} (hi : i < l.length) :
    l.reverse.getD i d = l.getD (l.length - 1 - i) d := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi),
      List.getD_eq_getElem _ _ (by omega : l.length - 1 - i < l.length),
      List.getElem_reverse]

theorem isWalk_reverse {H : Graph} {u v : ℕ} {P : Walk}
    (hP : P.IsWalk H u v) : P.reverse.IsWalk H v u := by
  rcases hP with ⟨hu, hv, ⟨hPv, hPe, rfl⟩ | ⟨hne, hlen, hhead, hlast, hedges, hstep⟩⟩
  · exact ⟨hu, hu, Or.inl ⟨by simp [reverse, hPv], by simp [reverse, hPe], rfl⟩⟩
  · refine ⟨hv, hu, Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simpa [reverse] using hne
    · simp [reverse, hlen]
    · simpa [reverse, List.head?_reverse] using hlast
    · simpa [reverse, List.getLast?_reverse] using hhead
    · intro j hj
      exact hedges j (by simpa [reverse] using hj)
    · intro i hi
      simp only [reverse, List.length_reverse] at hi ⊢
      have hk : P.edges.length - 1 - i < P.edges.length := by omega
      rw [getD_reverse_eq P.edges 0 hi]
      rw [getD_reverse_eq P.verts 0 (by omega : i < P.verts.length)]
      rw [getD_reverse_eq P.verts 0 (by omega : i + 1 < P.verts.length)]
      have hsub1 : P.verts.length - 1 - i = P.edges.length - 1 - i + 1 := by omega
      have hsub2 : P.verts.length - 1 - (i + 1) = P.edges.length - 1 - i := by omega
      rw [hsub1, hsub2]
      exact edgeMatches_symm (hstep (P.edges.length - 1 - i) hk)

theorem isWalk_verts_lt {H : Graph} {u v : ℕ} {P : Walk}
    (hH : H.IsValid) (hP : P.IsWalk H u v) : ∀ x ∈ P.verts, x < H.n := by
  rcases hP with ⟨hu, _, ⟨hPv, _, _⟩ | ⟨_, hlen, hhead, _, hedges, hstep⟩⟩
  · simp [hPv]
  · intro x hx
    rcases List.mem_iff_getElem.mp hx with ⟨k, hk, rfl⟩
    cases k with
    | zero =>
      have h0 : P.verts[0]'hk = u := by
        apply Option.some.inj
        rw [← List.getElem?_eq_getElem hk, ← List.head?_eq_getElem?]
        exact hhead
      simpa [h0] using hu
    | succ i =>
      have hi : i < P.edges.length := by omega
      have hji : P.edges.getD i 0 < H.m := by
        rw [List.getD_eq_getElem _ _ hi]
        exact hedges _ (List.getElem_mem hi)
      have hmem : H.edges[P.edges.getD i 0]'hji ∈ H.edges := List.getElem_mem hji
      have hvalid := hH _ hmem
      have hmatch := hstep i hi
      rw [List.getD_eq_getElem _ _ (by omega : i + 1 < P.verts.length),
          List.getD_eq_getElem _ _ hji] at hmatch
      rcases hmatch with ⟨_, h2⟩ | ⟨_, h1⟩
      · rw [← h2]; exact hvalid.2
      · rw [← h1]; exact hvalid.1

private theorem getD_append_left' {α : Type*} (l₁ l₂ : List α) (d : α) {i : ℕ}
    (hi : i < l₁.length) : (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_append_right' {α : Type*} (l₁ l₂ : List α) (d : α) {i : ℕ}
    (hi : l₁.length ≤ i) : (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

theorem isWalk_append {H : Graph} {u w v : ℕ} {P Q : Walk}
    (hP : P.IsWalk H u w) (hQ : Q.IsWalk H w v) : (P.append Q).IsWalk H u v := by
  unfold append
  split_ifs with h1 h2
  · have hPe : P.edges = [] := List.isEmpty_iff.mp h1
    rcases hP with ⟨_, _, ⟨_, _, rfl⟩ | ⟨hne, _⟩⟩
    · exact hQ
    · exact (hne hPe).elim
  · have hQe : Q.edges = [] := List.isEmpty_iff.mp h2
    rcases hQ with ⟨_, _, ⟨_, _, rfl⟩ | ⟨hne, _⟩⟩
    · exact hP
    · exact (hne hQe).elim
  · rcases hP with ⟨hu, hw, ⟨_, hPe, _⟩ | ⟨hPne, hPlen, hPhead, hPlast, hPedges, hPstep⟩⟩
    · exact absurd (List.isEmpty_iff.mpr hPe) h1
    · rcases hQ with ⟨_, hv, ⟨_, hQe, _⟩ | ⟨hQne, hQlen, hQhead, hQlast, hQedges, hQstep⟩⟩
      · exact absurd (List.isEmpty_iff.mpr hQe) h2
      · refine ⟨hu, hv, Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
        · simp [hPne]
        · rw [List.length_append, List.length_append, List.length_tail, hPlen, hQlen]
          omega
        · cases hPv : P.verts with
          | nil => simp [hPv] at hPhead
          | cons ph pt => simpa [hPv] using hPhead
        · have hQtail_ne : Q.verts.tail ≠ [] := by
            intro hnil
            have h1 : Q.verts.tail.length = 0 := by simp [hnil]
            have h2 : 0 < Q.edges.length := List.length_pos_of_ne_nil hQne
            rw [List.length_tail] at h1
            omega
          rw [List.getLast?_append_of_ne_nil _ hQtail_ne]
          cases hQv : Q.verts with
          | nil => simp [hQv] at hQhead
          | cons qh qt =>
            simp only [List.tail_cons]
            cases qt with
            | nil =>
              exfalso
              rw [hQv] at hQlen
              simp only [List.length_singleton] at hQlen
              exact hQne (List.length_eq_zero_iff.mp (by omega))
            | cons qh2 qt2 => simp [hQv] at hQlast ⊢; exact hQlast
        · intro j hj
          rcases List.mem_append.mp hj with hj | hj
          · exact hPedges j hj
          · exact hQedges j hj
        · intro i hi
          rw [List.length_append] at hi
          by_cases hip : i < P.edges.length
          · rw [getD_append_left' P.edges Q.edges 0 hip]
            rw [getD_append_left' P.verts Q.verts.tail 0 (by omega)]
            rw [getD_append_left' P.verts Q.verts.tail 0 (by omega)]
            exact hPstep i hip
          · have hpi : P.edges.length ≤ i := Nat.le_of_not_lt hip
            let k := i - P.edges.length
            have hk : k < Q.edges.length := by omega
            rw [getD_append_right' P.edges Q.edges 0 hpi]
            have hQverts : Q.verts = w :: Q.verts.tail := by
              cases hQv : Q.verts with
              | nil => simp [hQv] at hQhead
              | cons qh qt =>
                simp only [hQv, List.head?_cons, Option.some.injEq] at hQhead
                simp [hQhead]
            have hstepQ := hQstep k hk
            have hv1 : (P.verts ++ Q.verts.tail).getD i 0 = Q.verts.getD k 0 := by
              by_cases hk0 : k = 0
              · have hi_eq : i = P.edges.length := by omega
                subst hi_eq
                rw [getD_append_left' P.verts Q.verts.tail 0 (by omega)]
                have hplast_eq : P.verts.getD P.edges.length 0 = w := by
                  rw [List.getD_eq_getElem _ _ (by omega : P.edges.length < P.verts.length)]
                  have hlast := List.getLast?_eq_getElem? (l := P.verts)
                  rw [hPlast, hPlen, Nat.add_sub_cancel] at hlast
                  rw [List.getElem?_eq_getElem (by omega : P.edges.length < P.verts.length)] at hlast
                  exact Option.some.inj hlast.symm
                rw [hplast_eq]
                conv_rhs => rw [hQverts]
                simp [List.getD_eq_getElem?_getD, hk0]
              · rw [getD_append_right' P.verts Q.verts.tail 0 (by omega)]
                have hsub : i - P.verts.length = k - 1 := by omega
                rw [hsub]
                conv_rhs => rw [hQverts]
                obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk0
                simp [hk', List.getD_eq_getElem?_getD]
            have hv2 : (P.verts ++ Q.verts.tail).getD (i + 1) 0 = Q.verts.getD (k + 1) 0 := by
              rw [getD_append_right' P.verts Q.verts.tail 0 (by omega)]
              have hsub : i + 1 - P.verts.length = k := by omega
              rw [hsub]
              conv_rhs => rw [hQverts]
              simp [List.getD_eq_getElem?_getD]
            rw [hv1, hv2]
            exact hstepQ

theorem verts_toFinset_card_le {H : Graph} {u v : ℕ} {P : Walk}
    (hP : P.IsWalk H u v) : P.verts.toFinset.card ≤ P.edges.length + 1 := by
  calc P.verts.toFinset.card ≤ P.verts.length := List.toFinset_card_le P.verts
    _ ≤ P.edges.length + 1 := by
      rcases hP.2.2 with ⟨hPv, _⟩ | ⟨_, hlen, _⟩
      · simp [hPv]
      · omega

theorem verts_toFinset_card_eq_zero_of_edges_nil {H : Graph} {u v : ℕ} {P : Walk}
    (hP : P.IsWalk H u v) (he : P.edges = []) : P.verts.toFinset.card = 0 := by
  rcases hP.2.2 with ⟨hPv, _⟩ | ⟨hne, _⟩
  · simp [hPv]
  · exact (hne he).elim

theorem isWalk_mapEdges {H H' : Graph} {f : ℕ → ℕ} {u v : ℕ} {P : Walk}
    (hHn : H.n ≤ H'.n)
    (hf : ∀ j (_hj : j < H.m), f j < H'.m ∧ H'.edges.getD (f j) (0, 0) = H.edges.getD j (0, 0))
    (hP : P.IsWalk H u v) : (P.mapEdges f).IsWalk H' u v := by
  rcases hP with ⟨hu, hv, ⟨hPv, hPe, huv⟩ | ⟨hne, hlen, hhead, hlast, hedges, hstep⟩⟩
  · exact ⟨Nat.lt_of_lt_of_le hu hHn, Nat.lt_of_lt_of_le hv hHn,
      Or.inl ⟨hPv, by simp [mapEdges, hPe], huv⟩⟩
  · refine ⟨Nat.lt_of_lt_of_le hu hHn, Nat.lt_of_lt_of_le hv hHn, Or.inr ⟨?_, ?_, hhead, hlast, ?_, ?_⟩⟩
    · simpa [mapEdges] using hne
    · simpa [mapEdges] using hlen
    · intro k hk
      simp only [mapEdges, List.mem_map] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      exact (hf j (hedges j hj)).1
    · intro i hi
      simp only [mapEdges, List.length_map] at hi ⊢
      have hji : P.edges.getD i 0 < H.m := by
        rw [List.getD_eq_getElem _ _ hi]
        exact hedges _ (List.getElem_mem hi)
      have hmap_i : (P.edges.map f).getD i 0 = f (P.edges.getD i 0) := by
        rw [List.getD_eq_getElem _ _ (by simpa using hi),
            List.getD_eq_getElem _ _ hi, List.getElem_map]
      rw [hmap_i, (hf _ hji).2]
      exact hstep i hi

end Walk

/-! ## Graph Embeddings (Section 2, page 7) -/

/-- A graph embedding `Π_{G → H}` from `G` into `H` (`V(G) ⊆ V(H)`, here `G.n ≤ H.n`) maps each
edge `j < G.m` of `G` with endpoints `(u, v)` to a `u`-`v` walk `emb j` in `H`
(`prelims.tex`, Section 2, page 7). -/
def IsEmbedding (G H : Graph) (emb : ℕ → Walk) : Prop :=
  G.n ≤ H.n ∧ ∀ j (hj : j < G.m), (emb j).IsWalk H (G.edges[j]'hj).1 (G.edges[j]'hj).2

/-- A partial graph embedding from `G` into `H` maps each embedded edge (`emb? j = some P`) to a
valid walk between its endpoints (`Algorithm 4`, Tasks 2 and 3). -/
def IsPartialEmbedding (G H : Graph) (emb? : ℕ → Option Walk) : Prop :=
  G.n ≤ H.n ∧ ∀ j (hj : j < G.m) P, emb? j = some P → P.IsWalk H (G.edges[j]'hj).1 (G.edges[j]'hj).2

/-- Convert a partial embedding `ℕ → Option Walk` into a total map `ℕ → Walk`, sending unembedded
edges (`none`) to `Walk.empty` (contributing 0 to congestion and length). -/
def partialToWalk (emb? : ℕ → Option Walk) (j : ℕ) : Walk :=
  (emb? j).getD Walk.empty

/-- Edge congestion at edge `eH` (`prelims.tex`, Section 2, page 7):
`econg(Π_{G → H}, eH) = (∑_{eG ∈ E(G) : eH ∈ Π(eG)} w_G(eG)) / w_H(eH)`. -/
noncomputable def econgAt (G : Graph) (wG wH : ℕ → ℝ) (emb : ℕ → Walk) (eH : ℕ) : ℝ :=
  (∑ j ∈ (Finset.range G.m).filter (fun j => eH ∈ (emb j).edges), wG j) / wH eH

/-- Edge congestion of an embedding (`prelims.tex`, Section 2, page 7):
`econg(Π_{G → H}) = max_{eH ∈ E(H)} econg(Π_{G → H}, eH)` (0 if `H` has no edges). -/
noncomputable def econg (G H : Graph) (wG wH : ℕ → ℝ) (emb : ℕ → Walk) : ℝ :=
  (Finset.range H.m).fold max 0 (fun eH => econgAt G wG wH emb eH)

/-- Vertex congestion at vertex `vH` (`prelims.tex`, Section 2, page 7):
`vcong(Π_{G → H}, vH) = ∑_{eG ∈ E(G) : vH ∈ Π(eG)} w_G(eG)`. -/
noncomputable def vcongAt (G : Graph) (wG : ℕ → ℝ) (emb : ℕ → Walk) (vH : ℕ) : ℝ :=
  ∑ j ∈ (Finset.range G.m).filter (fun j => vH ∈ (emb j).verts), wG j

/-- Vertex congestion of an embedding (`prelims.tex`, Section 2, page 7):
`vcong(Π_{G → H}) = max_{vH ∈ V(H)} vcong(Π_{G → H}, vH)` (0 if `H` has no vertices). -/
noncomputable def vcong (G H : Graph) (wG : ℕ → ℝ) (emb : ℕ → Walk) : ℝ :=
  (Finset.range H.n).fold max 0 (fun vH => vcongAt G wG emb vH)

/-- Length of an embedding (`prelims.tex`, Section 2, page 7):
`length(Π_{G → H}) = max_{eG ∈ E(G)} |Π(eG)|` (0 if `G` has no edges). -/
def length (G : Graph) (emb : ℕ → Walk) : ℕ :=
  (Finset.range G.m).fold max 0 (fun j => (emb j).edges.length)

/-- Auxiliary recursion for embedding composition along a walk `(vs, js)` in `B`, orienting
each step `(u, v)` along edge `j` of `B` using `embBC j` or its reverse. -/
def composeAux (B : Graph) (embBC : ℕ → Walk) : List ℕ → List ℕ → Walk
  | u :: v :: vs, j :: js =>
    let e := B.edges.getD j (0, 0)
    let step := if e.1 = u ∧ e.2 = v then embBC j else (embBC j).reverse
    step.append (composeAux B embBC (v :: vs) js)
  | _, _ => Walk.empty

/-- Composition of embeddings `Π_{B → C} ∘ Π_{A → B}` (`prelims.tex`, Section 2, page 7):
maps `eA ∈ E(A)` with `Π_{A → B}(eA) = eB_1 ⊕ … ⊕ eB_k` to `Π_{B → C}(eB_1) ⊕ … ⊕ Π_{B → C}(eB_k)`,
orienting each `Π_{B → C}(eB_i)` to match the direction traversed in `Π_{A → B}(eA)`. -/
def compose (B : Graph) (embBC embAB : ℕ → Walk) (eA : ℕ) : Walk :=
  composeAux B embBC (embAB eA).verts (embAB eA).edges

/-- Restrict an embedding `emb` of `J` into `H'` to the subgraph `J̃` whose edge `k` is edge
`keptEdges[k]` of `J`. -/
def restrictEmb (emb : ℕ → Walk) (keptEdges : List ℕ) (k : ℕ) : Walk :=
  emb (keptEdges.getD k 0)

theorem econg_nonneg (G H : Graph) (wG wH : ℕ → ℝ) (emb : ℕ → Walk) :
    0 ≤ econg G H wG wH emb :=
  (Finset.le_fold_max _).mpr (Or.inl le_rfl)

theorem econgAt_le_econg {G H : Graph} (wG wH : ℕ → ℝ) (emb : ℕ → Walk) {eH : ℕ}
    (he : eH < H.m) : econgAt G wG wH emb eH ≤ econg G H wG wH emb :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨eH, Finset.mem_range.mpr he, le_rfl⟩)

theorem econg_le_iff {G H : Graph} {wG wH : ℕ → ℝ} {emb : ℕ → Walk} {B : ℝ} :
    econg G H wG wH emb ≤ B ↔ 0 ≤ B ∧ ∀ eH < H.m, econgAt G wG wH emb eH ≤ B := by
  simp [econg, Finset.fold_max_le, Finset.mem_range]

theorem vcong_nonneg (G H : Graph) (wG : ℕ → ℝ) (emb : ℕ → Walk) :
    0 ≤ vcong G H wG emb :=
  (Finset.le_fold_max _).mpr (Or.inl le_rfl)

theorem vcongAt_le_vcong {G H : Graph} (wG : ℕ → ℝ) (emb : ℕ → Walk) {vH : ℕ}
    (hv : vH < H.n) : vcongAt G wG emb vH ≤ vcong G H wG emb :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨vH, Finset.mem_range.mpr hv, le_rfl⟩)

theorem vcong_le_iff {G H : Graph} {wG : ℕ → ℝ} {emb : ℕ → Walk} {B : ℝ} :
    vcong G H wG emb ≤ B ↔ 0 ≤ B ∧ ∀ vH < H.n, vcongAt G wG emb vH ≤ B := by
  simp [vcong, Finset.fold_max_le, Finset.mem_range]

theorem vcongAt_nonneg {G : Graph} {wG : ℕ → ℝ} (hw : ∀ j < G.m, 0 ≤ wG j)
    (emb : ℕ → Walk) (vH : ℕ) : 0 ≤ vcongAt G wG emb vH := by
  apply Finset.sum_nonneg
  intro j hj
  exact hw j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)

theorem edges_length_le_length {G : Graph} (emb : ℕ → Walk) {j : ℕ} (hj : j < G.m) :
    (emb j).edges.length ≤ length G emb :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨j, Finset.mem_range.mpr hj, le_rfl⟩)

theorem length_le_iff {G : Graph} {emb : ℕ → Walk} {B : ℕ} :
    length G emb ≤ B ↔ ∀ j < G.m, (emb j).edges.length ≤ B := by
  simp [length, Finset.fold_max_le, Finset.mem_range]

theorem mem_verts_composeAux {B : Graph} {embBC : ℕ → Walk} :
    ∀ (vs js : List ℕ) {x : ℕ}, x ∈ (composeAux B embBC vs js).verts →
      ∃ j ∈ js, x ∈ (embBC j).verts := by
  intro vs js
  induction js generalizing vs with
  | nil =>
    intro x hx
    cases vs with
    | nil => simp [composeAux, Walk.empty] at hx
    | cons u vs' =>
      cases vs' with
      | nil => simp [composeAux, Walk.empty] at hx
      | cons v vs'' => simp [composeAux, Walk.empty] at hx
  | cons j js ih =>
    intro x hx
    cases vs with
    | nil => simp [composeAux, Walk.empty] at hx
    | cons u vs' =>
      cases vs' with
      | nil => simp [composeAux, Walk.empty] at hx
      | cons v vs'' =>
        simp only [composeAux] at hx
        rcases Walk.mem_verts_append_left hx with h | h
        · refine ⟨j, List.mem_cons_self, ?_⟩
          split_ifs at h
          · exact h
          · simpa [Walk.reverse] using h
        · obtain ⟨j', hj', hx'⟩ := ih (v :: vs'') h
          exact ⟨j', List.mem_cons_of_mem j hj', hx'⟩

theorem mem_verts_compose {B : Graph} {embBC embAB : ℕ → Walk} {eA x : ℕ}
    (hx : x ∈ (compose B embBC embAB eA).verts) :
    ∃ j ∈ (embAB eA).edges, x ∈ (embBC j).verts :=
  mem_verts_composeAux (embAB eA).verts (embAB eA).edges hx

theorem mem_edges_composeAux {B : Graph} {embBC : ℕ → Walk} :
    ∀ (vs js : List ℕ) {eC : ℕ}, eC ∈ (composeAux B embBC vs js).edges →
      ∃ j ∈ js, eC ∈ (embBC j).edges := by
  intro vs js
  induction js generalizing vs with
  | nil =>
    intro eC he
    cases vs with
    | nil => simp [composeAux, Walk.empty] at he
    | cons u vs' =>
      cases vs' <;> simp [composeAux, Walk.empty] at he
  | cons j js ih =>
    intro eC he
    cases vs with
    | nil => simp [composeAux, Walk.empty] at he
    | cons u vs' =>
      cases vs' with
      | nil => simp [composeAux, Walk.empty] at he
      | cons v vs'' =>
        simp only [composeAux, Walk.edges_append, List.mem_append] at he
        rcases he with h | h
        · refine ⟨j, List.mem_cons_self, ?_⟩
          split_ifs at h
          · exact h
          · simpa [Walk.reverse] using h
        · obtain ⟨j', hj', he'⟩ := ih (v :: vs'') h
          exact ⟨j', List.mem_cons_of_mem j hj', he'⟩

theorem mem_edges_compose {B : Graph} {embBC embAB : ℕ → Walk} {eA eC : ℕ}
    (he : eC ∈ (compose B embBC embAB eA).edges) :
    ∃ j ∈ (embAB eA).edges, eC ∈ (embBC j).edges :=
  mem_edges_composeAux (embAB eA).verts (embAB eA).edges he

theorem composeAux_edges_length_le {B : Graph} {embBC : ℕ → Walk} :
    ∀ (vs js : List ℕ), (∀ j ∈ js, j < B.m) →
      (composeAux B embBC vs js).edges.length ≤ js.length * length B embBC := by
  intro vs js hjs
  induction js generalizing vs with
  | nil =>
    cases vs with
    | nil => simp [composeAux, Walk.empty]
    | cons _ vs' => cases vs' <;> simp [composeAux, Walk.empty]
  | cons j js ih =>
    cases vs with
    | nil => simp [composeAux, Walk.empty]
    | cons u vs' =>
      cases vs' with
      | nil => simp [composeAux, Walk.empty]
      | cons v vs'' =>
        simp only [composeAux, Walk.edges_append, List.length_append, List.length_cons]
        have hj : (if (B.edges.getD j (0, 0)).1 = u ∧ (B.edges.getD j (0, 0)).2 = v then
            embBC j else (embBC j).reverse).edges.length ≤ length B embBC := by
          have hlen := edges_length_le_length embBC (hjs j List.mem_cons_self)
          split_ifs <;> simpa [Walk.reverse] using hlen
        have hrest := ih (v :: vs'') (fun k hk => hjs k (List.mem_cons_of_mem j hk))
        calc _ ≤ length B embBC + js.length * length B embBC := Nat.add_le_add hj hrest
          _ = (js.length + 1) * length B embBC := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem length_compose_le {A B : Graph} {embBC embAB : ℕ → Walk}
    (hAB : ∀ j < A.m, ∀ eB ∈ (embAB j).edges, eB < B.m) :
    length A (compose B embBC embAB) ≤ length A embAB * length B embBC := by
  rw [length_le_iff]
  intro j hj
  have h1 := composeAux_edges_length_le (embBC := embBC) (embAB j).verts (embAB j).edges (hAB j hj)
  have h2 : (embAB j).edges.length ≤ length A embAB := edges_length_le_length embAB hj
  exact le_trans h1 (Nat.mul_le_mul_right _ h2)

theorem composeAux_isWalk {B C : Graph} {embBC : ℕ → Walk}
    (hBC : IsEmbedding B C embBC) :
    ∀ (js vs : List ℕ) (u v : ℕ),
      vs.length = js.length + 1 →
      vs.head? = some u →
      vs.getLast? = some v →
      (∀ j ∈ js, j < B.m) →
      (∀ i : ℕ, i < js.length →
        Walk.EdgeMatches (B.edges.getD (js.getD i 0) (0, 0)) (vs.getD i 0) (vs.getD (i + 1) 0)) →
      v < B.n →
      (composeAux B embBC vs js).IsWalk C u v := by
  intro js
  induction js with
  | nil =>
    intro vs u v hlen hhead hlast _ _ hv
    cases vs with
    | nil => simp at hlen
    | cons a vs' =>
      cases vs' with
      | cons _ _ => simp at hlen
      | nil =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        simp only [List.getLast?_singleton, Option.some.injEq] at hlast
        subst hhead hlast
        exact ⟨Nat.lt_of_lt_of_le hv hBC.1, Nat.lt_of_lt_of_le hv hBC.1,
          Or.inl ⟨rfl, rfl, rfl⟩⟩
  | cons j js ih =>
    intro vs u v hlen hhead hlast hedges hstep hv
    cases vs with
    | nil => simp at hlen
    | cons a vs' =>
      cases vs' with
      | nil => simp at hlen
      | cons b vs'' =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst a
        have hjB : j < B.m := hedges j List.mem_cons_self
        have hstep0 := hstep 0 (by simp)
        simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some] at hstep0
        rw [← List.getD_eq_getElem?_getD] at hstep0
        have hBe : B.edges.getD j (0, 0) = B.edges[j]'hjB :=
          List.getD_eq_getElem _ _ hjB
        have hj_walk := hBC.2 j hjB
        have hstep_walk : (if (B.edges.getD j (0, 0)).1 = u ∧ (B.edges.getD j (0, 0)).2 = b then
            embBC j else (embBC j).reverse).IsWalk C u b := by
          rw [hBe] at hstep0 ⊢
          rcases hstep0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [h1, h2, and_self, ↓reduceIte]
            simpa [h1, h2] using hj_walk
          · split_ifs with hcond
            · rw [hcond.1, hcond.2] at hj_walk
              exact hj_walk
            · rw [← h1, ← h2]
              exact Walk.isWalk_reverse hj_walk
        have hlen' : (b :: vs'').length = js.length + 1 := by simpa using hlen
        have hlast' : (b :: vs'').getLast? = some v := by
          simpa [List.getLast?_cons_cons] using hlast
        have hedges' : ∀ k ∈ js, k < B.m := fun k hk => hedges k (List.mem_cons_of_mem j hk)
        have hstep' : ∀ i : ℕ, i < js.length →
            Walk.EdgeMatches (B.edges.getD (js.getD i 0) (0, 0))
              ((b :: vs'').getD i 0) ((b :: vs'').getD (i + 1) 0) := by
          intro i hi
          have := hstep (i + 1) (by simpa using Nat.succ_lt_succ hi)
          simpa [List.getD_eq_getElem?_getD] using this
        have htail_walk : (composeAux B embBC (b :: vs'') js).IsWalk C b v :=
          ih (b :: vs'') b v hlen' rfl hlast' hedges' hstep' hv
        exact Walk.isWalk_append hstep_walk htail_walk

theorem isEmbedding_compose {A B C : Graph} {embBC embAB : ℕ → Walk}
    (hAB : IsEmbedding A B embAB) (hBC : IsEmbedding B C embBC) :
    IsEmbedding A C (compose B embBC embAB) := by
  refine ⟨le_trans hAB.1 hBC.1, fun j hj => ?_⟩
  have hW := hAB.2 j hj
  unfold compose
  rcases hW with ⟨hu, hv, ⟨hPv, hPe, huv⟩ | ⟨_, hlen, hhead, hlast, hedges, hstep⟩⟩
  · rw [hPv, hPe]
    refine ⟨Nat.lt_of_lt_of_le hu hBC.1,
      Nat.lt_of_lt_of_le hv hBC.1, Or.inl ⟨rfl, rfl, huv⟩⟩
  · exact composeAux_isWalk hBC (embAB j).edges (embAB j).verts
      (A.edges[j]'hj).1 (A.edges[j]'hj).2 hlen hhead hlast hedges hstep hv

theorem isEmbedding_restrictEmb {J H' : Graph} {emb : ℕ → Walk} {keptEdges : List ℕ}
    (hkept : ∀ j ∈ keptEdges, j < J.m)
    (hemb : IsEmbedding J H' emb) :
    IsEmbedding ⟨J.n, keptEdges.map fun j => J.edges.getD j (0, 0)⟩ H' (restrictEmb emb keptEdges) := by
  refine ⟨hemb.1, fun k hk => ?_⟩
  dsimp only [Graph.m] at hk
  rw [List.length_map] at hk
  have hmem : keptEdges[k]'hk ∈ keptEdges := List.getElem_mem hk
  have hj : keptEdges[k]'hk < J.m := hkept _ hmem
  have hk_getD : keptEdges.getD k 0 = keptEdges[k]'hk := List.getD_eq_getElem _ _ hk
  rw [restrictEmb, hk_getD]
  simp only [List.getElem_map, List.getD_eq_getElem _ _ hj]
  exact hemb.2 _ hj

/-- **Fact 1** (`prelims.tex`, Section 2, page 7):
For embeddings `Π_{B → C}` and `Π_{A → B}`,
`vcong(Π_{B → C} ∘ Π_{A → B}) ≤ vcong(Π_{B → C}) · econg(Π_{A → B})`. -/
theorem fact_1 {A B C : Graph} {wA wB : ℕ → ℝ} {embBC embAB : ℕ → Walk}
    (hwA : ∀ j < A.m, 0 ≤ wA j) (hwB : ∀ eB < B.m, 0 < wB eB)
    (hAB : ∀ j < A.m, ∀ eB ∈ (embAB j).edges, eB < B.m) :
    vcong A C wA (compose B embBC embAB) ≤ vcong B C wB embBC * econg A B wA wB embAB := by
  rw [vcong_le_iff]
  refine ⟨mul_nonneg (vcong_nonneg B C wB embBC) (econg_nonneg A B wA wB embAB), ?_⟩
  intro vC hvC
  unfold vcongAt
  have hstep1 :
      ∑ j ∈ (Finset.range A.m).filter (fun j => vC ∈ (compose B embBC embAB j).verts), wA j ≤
      ∑ j ∈ Finset.range A.m,
        ∑ eB ∈ (Finset.range B.m).filter (fun eB => eB ∈ (embAB j).edges ∧ vC ∈ (embBC eB).verts),
          wA j := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro j hjA
    have hjAm : j < A.m := Finset.mem_range.mp hjA
    split_ifs with hv
    · obtain ⟨eB, heB_edges, heB_v⟩ := mem_verts_compose hv
      have heBm : eB < B.m := hAB j hjAm eB heB_edges
      have hmem : eB ∈ (Finset.range B.m).filter
          (fun eB => eB ∈ (embAB j).edges ∧ vC ∈ (embBC eB).verts) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr heBm, heB_edges, heB_v⟩
      exact Finset.single_le_sum (fun _ _ => hwA j hjAm) hmem
    · exact Finset.sum_nonneg (fun _ _ => hwA j hjAm)
  have hswap :
      (∑ j ∈ Finset.range A.m,
        ∑ eB ∈ (Finset.range B.m).filter (fun eB => eB ∈ (embAB j).edges ∧ vC ∈ (embBC eB).verts),
          wA j) =
      ∑ eB ∈ (Finset.range B.m).filter (fun eB => vC ∈ (embBC eB).verts),
        ∑ j ∈ (Finset.range A.m).filter (fun j => eB ∈ (embAB j).edges), wA j := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun eB _ => ?_
    by_cases h2 : vC ∈ (embBC eB).verts
    · simp [h2]
    · simp [h2]
  have hstep2 :
      (∑ eB ∈ (Finset.range B.m).filter (fun eB => vC ∈ (embBC eB).verts),
        ∑ j ∈ (Finset.range A.m).filter (fun j => eB ∈ (embAB j).edges), wA j) ≤
      ∑ eB ∈ (Finset.range B.m).filter (fun eB => vC ∈ (embBC eB).verts),
        wB eB * econg A B wA wB embAB := by
    apply Finset.sum_le_sum
    intro eB heB
    have heBm : eB < B.m := Finset.mem_range.mp (Finset.mem_filter.mp heB).1
    have hwpos : 0 < wB eB := hwB eB heBm
    have hecong : econgAt A wA wB embAB eB ≤ econg A B wA wB embAB :=
      econgAt_le_econg wA wB embAB heBm
    unfold econgAt at hecong
    calc (∑ j ∈ (Finset.range A.m).filter (fun j => eB ∈ (embAB j).edges), wA j)
        = wB eB * ((∑ j ∈ (Finset.range A.m).filter (fun j => eB ∈ (embAB j).edges), wA j) /
            wB eB) := (mul_div_cancel₀ _ hwpos.ne').symm
      _ ≤ wB eB * econg A B wA wB embAB := mul_le_mul_of_nonneg_left hecong hwpos.le
  calc ∑ j ∈ (Finset.range A.m).filter (fun j => vC ∈ (compose B embBC embAB j).verts), wA j
      ≤ _ := hstep1
    _ = _ := hswap
    _ ≤ _ := hstep2
    _ = (∑ eB ∈ (Finset.range B.m).filter (fun eB => vC ∈ (embBC eB).verts), wB eB) *
          econg A B wA wB embAB := (Finset.sum_mul _ _ _).symm
    _ = vcongAt B wB embBC vC * econg A B wA wB embAB := rfl
    _ ≤ vcong B C wB embBC * econg A B wA wB embAB :=
        mul_le_mul_of_nonneg_right (vcongAt_le_vcong wB embBC hvC) (econg_nonneg A B wA wB embAB)

end MinCostFlow.Spanner
