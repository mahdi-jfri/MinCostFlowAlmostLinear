module

public import MinCostFlow.Basic.Graph
public import MinCostFlow.Basic.Embedding
public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.Spanner.Embedding
public import MinCostFlow.Spanner.Algorithm

import MinCostFlow.Spanner.Subgraph
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort

/-!
# Translation Between `MGraph` and `Cited.Graph` for `Sparsify`

This file translates inputs `(H', J, embJH)` on `MGraph` (`Basic/Graph.lean`) into `Cited.Graph`
instances supported strictly on the vertices `V(J)` and the vertices and edges visited by `embJH`
in `H'` (never touching unused vertices or edges of `H'`), and translates the output sparsifier
`J̃` and embedding `Π_{J → J̃}` back to `MGraph` and `MinCostFlow.Embedding`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## Vertex and edge enumerations on `MGraph` -/

/-- Set of vertices of `H'` that must be represented in `toCitedH`: `V(J)` together with every
vertex visited by `embJH e` for `e ∈ J.E`. Independent of `|V(H')|`. -/
def usedHVerts (H' J : MGraph) (embJH : MinCostFlow.Embedding) : Finset ℕ :=
  J.V ∪ J.E.biUnion fun e => (H'.walkVertices (J.tail e) (embJH e)).toFinset

/-- Set of edges of `H'` traversed by `embJH e` for `e ∈ J.E`. Independent of `|E(H')|`. -/
def usedHEdges (J : MGraph) (embJH : MinCostFlow.Embedding) : Finset ℕ :=
  J.E.biUnion fun e => MinCostFlow.walkEdges (embJH e)

/-- Canonical vertex list of `H'` used by `toCitedH`: `vertsOf J.V` as prefix `0 .. J.n - 1`,
followed by sorted vertices in `usedHVerts \ J.V`. -/
def hVerts (H' J : MGraph) (embJH : MinCostFlow.Embedding) : List ℕ :=
  vertsOf J.V ++ vertsOf (usedHVerts H' J embJH \ J.V)

/-- Canonical edge list of `H'` used by `toCitedH`. -/
def hEdges (J : MGraph) (embJH : MinCostFlow.Embedding) : List ℕ :=
  vertsOf (usedHEdges J embJH)

/-- `Cited.Graph` representing `J` via `vertsOf J.V` and `vertsOf J.E`. -/
def toCitedJ (J : MGraph) : Cited.Graph :=
  let vs := vertsOf J.V
  let es := vertsOf J.E
  { n := vs.length
    edges := es.map fun e => (vs.idxOf (J.tail e), vs.idxOf (J.head e)) }

/-- `Cited.Graph` representing the subgraph of `H'` supported on `usedHVerts` and `usedHEdges`. -/
def toCitedH (H' J : MGraph) (embJH : MinCostFlow.Embedding) : Cited.Graph :=
  let vs := hVerts H' J embJH
  let es := hEdges J embJH
  { n := vs.length
    edges := es.map fun e => (vs.idxOf (H'.tail e), vs.idxOf (H'.head e)) }

/-- Convert an `MGraph` walk `P` starting at `u` into a `Cited.Walk` along vertex list `vs`
and edge list `es`. Empty `MGraph` walks become `Walk.empty`. -/
def walkToCited (H' : MGraph) (vs es : List ℕ) (u : ℕ) (P : List (ℕ × Bool)) : Walk :=
  if P.isEmpty then Walk.empty
  else
    { verts := (H'.walkVertices u P).map vs.idxOf
      edges := (P.map Prod.fst).map es.idxOf }

/-- Translate `embJH : MinCostFlow.Embedding` (`J → H'`) into an embedding `toCitedJ J → toCitedH H' J embJH`. -/
def embToCited (H' J : MGraph) (embJH : MinCostFlow.Embedding) : ℕ → Walk :=
  let vs := hVerts H' J embJH
  let es := hEdges J embJH
  let jEs := vertsOf J.E
  fun j =>
    let e := jEs.getD j 0
    walkToCited H' vs es (J.tail e) (embJH e)

/-- Subgraph of `J : MGraph` retaining the edge subset indexed by `kept : List ℕ`. -/
def outJtilde (J : MGraph) (kept : List ℕ) : MGraph :=
  let jEs := vertsOf J.E
  { V := J.V
    E := (kept.map fun j => jEs.getD j 0).toFinset
    tail := J.tail
    head := J.head }

/-- Convert a `Cited.Walk` along `G` (`out.Jtilde`) back into an `MGraph` walk in `outJtilde J kept`. -/
def citedWalkSteps (jEs : List ℕ) (G : Cited.Graph) (kept : List ℕ) :
    List ℕ → List ℕ → List (ℕ × Bool)
  | u :: v :: vs, c :: cs =>
    let eG := G.edges.getD c (0, 0)
    let dir := decide (eG.1 = u ∧ eG.2 = v)
    let eOrig := jEs.getD (kept.getD c 0) 0
    (eOrig, dir) :: citedWalkSteps jEs G kept (v :: vs) cs
  | _, _ => []

/-- Translate `emb : ℕ → Walk` (`toCitedJ J → G`) into `MinCostFlow.Embedding` (`J → outJtilde J kept`). -/
def citedEmbToMGraph (J : MGraph) (G : Cited.Graph) (kept : List ℕ) (emb : ℕ → Walk) :
    MinCostFlow.Embedding :=
  let jEs := vertsOf J.E
  fun e =>
    if e ∈ J.E then
      let P := emb (jEs.idxOf e)
      citedWalkSteps jEs G kept P.verts P.edges
    else []

/-! ## Enumeration and indexing lemmas -/

lemma hVerts_nodup (H' J : MGraph) (embJH : MinCostFlow.Embedding) :
    (hVerts H' J embJH).Nodup := by
  unfold hVerts
  refine List.nodup_append.mpr ⟨vertsOf_nodup J.V, vertsOf_nodup _, ?_⟩
  intro a ha1 b hb2 hab
  subst hab
  rw [mem_vertsOf] at ha1 hb2
  exact (Finset.mem_sdiff.mp hb2).2 ha1

lemma mem_hVerts {H' J : MGraph} {embJH : MinCostFlow.Embedding} {v : ℕ} :
    v ∈ hVerts H' J embJH ↔ v ∈ usedHVerts H' J embJH := by
  unfold hVerts
  rw [List.mem_append, mem_vertsOf, mem_vertsOf, Finset.mem_sdiff]
  constructor
  · rintro (hv | ⟨hv, _⟩)
    · exact Finset.mem_union_left _ hv
    · exact hv
  · intro hv
    by_cases hvJ : v ∈ J.V
    · exact Or.inl hvJ
    · exact Or.inr ⟨hv, hvJ⟩

private lemma list_idxOf_append_of_mem {α : Type*} [BEq α] [LawfulBEq α] :
    ∀ (l₁ l₂ : List α) {a : α}, a ∈ l₁ → (l₁ ++ l₂).idxOf a = l₁.idxOf a
  | [], _, _, ha => by simp at ha
  | x :: xs, l₂, a, ha => by
    simp only [List.cons_append, List.idxOf_cons]
    by_cases h : x == a
    · simp [h]
    · simp only [h]
      have ha' : a ∈ xs := by
        rcases List.mem_cons.mp ha with rfl | hmem
        · simp at h
        · exact hmem
      simp [list_idxOf_append_of_mem xs l₂ ha']

lemma hVerts_idxOf_eq_vertsOf {H' J : MGraph} {embJH : MinCostFlow.Embedding} {v : ℕ}
    (hv : v ∈ J.V) :
    (hVerts H' J embJH).idxOf v = (vertsOf J.V).idxOf v :=
  list_idxOf_append_of_mem (vertsOf J.V) _ (mem_vertsOf.mpr hv)

lemma hVerts_idxOf_lt {H' J : MGraph} {embJH : MinCostFlow.Embedding} {v : ℕ}
    (hv : v ∈ usedHVerts H' J embJH) :
    (hVerts H' J embJH).idxOf v < (hVerts H' J embJH).length :=
  List.idxOf_lt_length_iff.mpr (mem_hVerts.mpr hv)

lemma getElem_hVerts_idxOf {H' J : MGraph} {embJH : MinCostFlow.Embedding} {v : ℕ}
    (hv : v ∈ usedHVerts H' J embJH) :
    (hVerts H' J embJH)[(hVerts H' J embJH).idxOf v]'(hVerts_idxOf_lt hv) = v :=
  List.getElem_idxOf (hVerts_idxOf_lt hv)

lemma idxOf_getElem_hVerts {H' J : MGraph} {embJH : MinCostFlow.Embedding} {k : ℕ}
    (hk : k < (hVerts H' J embJH).length) :
    (hVerts H' J embJH).idxOf ((hVerts H' J embJH)[k]'hk) = k :=
  (hVerts_nodup H' J embJH).idxOf_getElem k hk

lemma hVerts_length_le (H' J : MGraph) (embJH : MinCostFlow.Embedding) :
    (hVerts H' J embJH).length ≤ J.n + J.m * (embJH.length J + 1) := by
  unfold hVerts
  rw [List.length_append, vertsOf_length, vertsOf_length]
  have hsub : usedHVerts H' J embJH \ J.V ⊆
      J.E.biUnion fun e => (H'.walkVertices (J.tail e) (embJH e)).toFinset := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hx1, hx2⟩
    rcases Finset.mem_union.mp hx1 with hxJ | hxU
    · exact (hx2 hxJ).elim
    · exact hxU
  have hcard1 := Finset.card_le_card hsub
  have hcard2 : (J.E.biUnion fun e => (H'.walkVertices (J.tail e) (embJH e)).toFinset).card ≤
      ∑ e ∈ J.E, ((embJH e).length + 1) := by
    refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun e _ => ?_)
    have h1 := List.toFinset_card_le (H'.walkVertices (J.tail e) (embJH e))
    simpa [MGraph.walkVertices] using h1
  have hcard3 : (∑ e ∈ J.E, ((embJH e).length + 1)) ≤ J.m * (embJH.length J + 1) := by
    calc ∑ e ∈ J.E, ((embJH e).length + 1)
        ≤ ∑ _e ∈ J.E, (embJH.length J + 1) := by
          refine Finset.sum_le_sum fun e he => Nat.add_le_add_right ?_ 1
          exact Finset.le_sup (f := fun e => (embJH e).length) he
      _ = J.m * (embJH.length J + 1) := by rw [Finset.sum_const, smul_eq_mul]; rfl
  change J.n + (usedHVerts H' J embJH \ J.V).card ≤ J.n + J.m * (embJH.length J + 1)
  omega

lemma hEdges_length_le (J : MGraph) (embJH : MinCostFlow.Embedding) :
    (hEdges J embJH).length ≤ J.m * embJH.length J := by
  unfold hEdges usedHEdges
  rw [vertsOf_length]
  have hcard1 : (J.E.biUnion fun e => MinCostFlow.walkEdges (embJH e)).card ≤
      ∑ e ∈ J.E, (embJH e).length := by
    refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun e _ => ?_)
    unfold MinCostFlow.walkEdges
    have h1 := List.toFinset_card_le ((embJH e).map Prod.fst)
    simpa using h1
  have hcard2 : (∑ e ∈ J.E, (embJH e).length) ≤ J.m * embJH.length J := by
    calc ∑ e ∈ J.E, (embJH e).length
        ≤ ∑ _e ∈ J.E, embJH.length J :=
          Finset.sum_le_sum fun e he => Finset.le_sup (f := fun e => (embJH e).length) he
      _ = J.m * embJH.length J := by rw [Finset.sum_const, smul_eq_mul]; rfl
  exact le_trans hcard1 hcard2

/-! ## `MGraph` walk helpers -/

lemma mgraph_isWalk_append {G : MGraph} :
    ∀ {u w v : ℕ} {P Q : List (ℕ × Bool)},
      G.IsWalk u w P → G.IsWalk w v Q → G.IsWalk u v (P ++ Q)
  | _, _, _, [], _, .nil _, hQ => hQ
  | _, _, _, _ :: _, _, .cons hx hsrc hP, hQ =>
    .cons hx hsrc (mgraph_isWalk_append hP hQ)

lemma mgraph_isWalk_walkRev {G : MGraph} :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, G.IsWalk u v P → G.IsWalk v u (MinCostFlow.walkRev P)
  | u, _, [], .nil _ => .nil u
  | u, _, (e, b) :: _, .cons he hsrc hP => by
    have hIH := mgraph_isWalk_walkRev hP
    have hstep : G.IsWalk (G.dst (e, b)) u [(e, !b)] := by
      have hsrc' : G.src (e, !b) = G.dst (e, b) := by cases b <;> rfl
      have hdst' : G.dst (e, !b) = G.src (e, b) := by cases b <;> rfl
      have hnil : G.IsWalk (G.dst (e, !b)) u [] := by
        rw [hdst', hsrc]; exact .nil u
      exact .cons he hsrc' hnil
    simpa [MinCostFlow.walkRev] using mgraph_isWalk_append hIH hstep

lemma mgraph_walkVertices_last_of_isWalk {G : MGraph} :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, G.IsWalk u v P → v ∈ G.walkVertices u P
  | u, _, [], .nil _ => by simp [MGraph.walkVertices]
  | _, _, _ :: xs, .cons _ _ hP =>
    List.mem_cons_of_mem _ (by simpa [MGraph.walkVertices] using mgraph_walkVertices_last_of_isWalk hP)

lemma mgraph_walkVertices_subset {G : MGraph} (hG : G.IsValid) :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, G.IsWalk u v P → u ∈ G.V →
      ∀ x ∈ G.walkVertices u P, x ∈ G.V
  | u, _, [], .nil _, hu, x, hx => by simp [MGraph.walkVertices] at hx; rwa [hx]
  | _, _, y :: ys, .cons hy _ hP, hu, x, hx => by
    simp only [MGraph.walkVertices, List.map_cons, List.mem_cons] at hx
    have hdstV : G.dst y ∈ G.V := by
      rcases hG y.1 hy with ⟨ht, hh⟩
      cases hyb : y.2 <;> simp [MGraph.dst, hyb, ht, hh]
    rcases hx with rfl | hx'
    · exact hu
    · exact mgraph_walkVertices_subset hG hP hdstV x (by simpa [MGraph.walkVertices] using hx')

lemma mgraph_mem_walkVertices_src_dst {G : MGraph} :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, G.IsWalk u v P →
      ∀ y ∈ P, y.1 ∈ G.E ∧ G.src y ∈ G.walkVertices u P ∧ G.dst y ∈ G.walkVertices u P
  | _, _, [], .nil _, _, hy => by simp at hy
  | u, _, x :: xs, .cons hx hsrc hP, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨hx, hsrc ▸ List.mem_cons_self, by simp [MGraph.walkVertices]⟩
    · rcases mgraph_mem_walkVertices_src_dst hP y hy' with ⟨he, h1, h2⟩
      refine ⟨he, ?_, ?_⟩
      · exact List.mem_cons_of_mem u (by simpa [MGraph.walkVertices] using h1)
      · exact List.mem_cons_of_mem u (by simpa [MGraph.walkVertices] using h2)

lemma mgraph_walkVertices_append {G : MGraph} :
    ∀ {u w : ℕ} {P Q : List (ℕ × Bool)}, G.IsWalk u w P →
      ∀ x, x ∈ G.walkVertices u (P ++ Q) ↔ x ∈ G.walkVertices u P ∨ x ∈ G.walkVertices w Q
  | _, _, [], Q, .nil u, x => by
    simp only [MGraph.walkVertices, List.nil_append, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false]
    constructor
    · intro h; exact Or.inr h
    · rintro (rfl | h); exact Or.inl rfl; exact h
  | u, w, y :: ys, Q, .cons hy _ hP, x => by
    simp only [MGraph.walkVertices, List.cons_append, List.map_cons, List.mem_cons] at ⊢
    have hIH := mgraph_walkVertices_append hP x (Q := Q)
    simp only [MGraph.walkVertices, List.mem_cons] at hIH
    tauto

lemma mgraph_walkVertices_walkRev {G : MGraph} :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, G.IsWalk u v P →
      ∀ x, x ∈ G.walkVertices v (MinCostFlow.walkRev P) ↔ x ∈ G.walkVertices u P := by
  intro u v P hP x
  have hm_rev : ∀ {u' v' : ℕ} {Q : List (ℕ × Bool)},
      G.IsWalk u' v' Q → ∀ z, z ∈ G.walkVertices v' (MinCostFlow.walkRev Q) → z ∈ G.walkVertices u' Q := by
    intro u' v' Q hQ z hz
    induction Q generalizing u' z with
    | nil =>
      cases hQ
      simp [MinCostFlow.walkRev, MGraph.walkVertices] at hz ⊢
      exact hz
    | cons y ys ih =>
      cases hQ with
      | cons hy hsrc hys =>
        have hys_rev : G.IsWalk v' (G.dst y) (MinCostFlow.walkRev ys) := mgraph_isWalk_walkRev hys
        have hrew : MinCostFlow.walkRev (y :: ys) = MinCostFlow.walkRev ys ++ [(y.1, !y.2)] := by
          simp [MinCostFlow.walkRev]
        rw [hrew, mgraph_walkVertices_append hys_rev z] at hz
        rcases hz with hmem | hsing
        · exact List.mem_cons_of_mem u' (by simpa [MGraph.walkVertices] using ih hys z hmem)
        · have hdst_eq : G.dst (y.1, !y.2) = u' := by
            cases hyb : y.2 <;> simp [MGraph.src, MGraph.dst, hyb] at hsrc ⊢ <;> exact hsrc
          simp only [MGraph.walkVertices, List.map_cons, List.map_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hsing
          rcases hsing with rfl | rfl
          · exact List.mem_cons_of_mem u' (by simp)
          · exact hdst_eq ▸ List.mem_cons_self
  constructor
  · exact hm_rev hP x
  · intro hx
    have hP_rev := mgraph_isWalk_walkRev hP
    have h1 := hm_rev hP_rev x
    have hrev_rev : MinCostFlow.walkRev (MinCostFlow.walkRev P) = P := by
      unfold MinCostFlow.walkRev
      rw [List.map_reverse, List.reverse_reverse, List.map_map]
      have hfun : ((fun x : ℕ × Bool => (x.1, !x.2)) ∘ fun x : ℕ × Bool => (x.1, !x.2)) = id := by
        funext ⟨a, b⟩; cases b <;> rfl
      rw [hfun, List.map_id]
    exact (hrev_rev ▸ h1) hx

lemma isSubgraph_isWalk {G H : MGraph} (hsub : G.IsSubgraph H) :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, H.IsWalk u v P → G.IsWalk u v P
  | _, _, _, .nil u => .nil u
  | u, _, (e, b) :: xs, .cons he hsrc hP => by
    have heG : e ∈ G.E := hsub.2.1 he
    have hth := hsub.2.2 e he
    have hsrcG : G.src (e, b) = u := by
      simp only [MGraph.src] at hsrc
      cases b <;> simp [MGraph.src, ← hth.1, ← hth.2] <;> exact hsrc
    have hdstG : G.dst (e, b) = H.dst (e, b) := by
      cases b <;> simp [MGraph.dst, hth.1, hth.2]
    exact .cons heG hsrcG (hdstG ▸ isSubgraph_isWalk hsub hP)

lemma isWalk_dst_eq_of_nil {G : MGraph} {u v : ℕ} (h : G.IsWalk u v []) : u = v := by
  cases h; rfl

lemma usedHVerts_subset_V {H' J : MGraph} {embJH : MinCostFlow.Embedding}
    (hH' : H'.IsValid) (hJ : J.IsValid) (hemb : embJH.IsEmbedding J H') :
    usedHVerts H' J embJH ⊆ H'.V := by
  intro x hx
  rcases Finset.mem_union.mp hx with hxJ | hxU
  · exact hemb.1 hxJ
  · rcases Finset.mem_biUnion.mp hxU with ⟨e, he, hxv⟩
    have hwe := hemb.2 e he
    have htv : J.tail e ∈ H'.V := hemb.1 (hJ e he).1
    exact mgraph_walkVertices_subset hH' hwe htv x (List.mem_toFinset.mp hxv)

/-! ## Validity, degree, and walk preservation for `toCitedJ`, `toCitedH`, `outJtilde` -/

lemma toCitedJ_m (J : MGraph) : (toCitedJ J).m = J.m := by
  dsimp only [toCitedJ, Graph.m, MGraph.m]
  rw [List.length_map, vertsOf_length]

lemma toCitedH_m (H' J : MGraph) (embJH : MinCostFlow.Embedding) :
    (toCitedH H' J embJH).m = (hEdges J embJH).length := by
  dsimp only [toCitedH, Graph.m]
  rw [List.length_map]

lemma toCitedJ_isValid {J : MGraph} (hJ : J.IsValid) : (toCitedJ J).IsValid := by
  intro e he
  dsimp only [toCitedJ] at he ⊢
  rw [List.mem_map] at he
  rcases he with ⟨eJ, heJ, rfl⟩
  rw [mem_vertsOf] at heJ
  have hv := hJ eJ heJ
  rw [vertsOf_length]
  exact ⟨idxOf_lt_card hv.1, idxOf_lt_card hv.2⟩

lemma toCitedH_isValid {H' J : MGraph} {embJH : MinCostFlow.Embedding}
    (_hH' : H'.IsValid) (_hJ : J.IsValid) (hemb : embJH.IsEmbedding J H') :
    (toCitedH H' J embJH).IsValid := by
  intro e he
  dsimp only [toCitedH] at he ⊢
  rw [List.mem_map] at he
  rcases he with ⟨eH, heH, rfl⟩
  rw [show hEdges J embJH = vertsOf (usedHEdges J embJH) from rfl, mem_vertsOf] at heH
  rcases Finset.mem_biUnion.mp heH with ⟨eJ, heJ, hstep⟩
  unfold MinCostFlow.walkEdges at hstep
  rw [List.mem_toFinset, List.mem_map] at hstep
  rcases hstep with ⟨y, hyP, hy1⟩
  have hwalk := hemb.2 eJ heJ
  have hmem := mgraph_mem_walkVertices_src_dst hwalk y hyP
  have htail_u : H'.tail eH ∈ usedHVerts H' J embJH := by
    refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨eJ, heJ, List.mem_toFinset.mpr ?_⟩)
    cases hy : y.2 <;> subst hy1
    · simpa [MGraph.dst, hy] using hmem.2.2
    · simpa [MGraph.src, hy] using hmem.2.1
  have hhead_u : H'.head eH ∈ usedHVerts H' J embJH := by
    refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨eJ, heJ, List.mem_toFinset.mpr ?_⟩)
    cases hy : y.2 <;> subst hy1
    · simpa [MGraph.src, hy] using hmem.2.1
    · simpa [MGraph.dst, hy] using hmem.2.2
  exact ⟨hVerts_idxOf_lt htail_u, hVerts_idxOf_lt hhead_u⟩

private lemma count_vertsOf_filter {X : Finset ℕ} (p : ℕ → Bool) :
    ((vertsOf X).filter p).length = (X.filter fun x => p x = true).card := by
  rw [← List.toFinset_card_of_nodup ((vertsOf_nodup X).filter p)]
  congr 1
  ext x
  simp [mem_vertsOf]

lemma maxDeg_toCitedJ_le {J : MGraph} (hJ : J.IsValid) :
    maxDeg (toCitedJ J) ≤ J.maxDeg := by
  rw [maxDeg_le_iff]
  intro v hv
  have hv_card : v < J.V.card := by
    simpa [toCitedJ, vertsOf_length] using hv
  have hvalid := toCitedJ_isValid hJ
  rw [deg_eq_filter_edges hvalid v]
  let u := (vertsOf J.V).getD v 0
  have huV : u ∈ J.V := getD_vertsOf_mem hv_card
  have htail : ((toCitedJ J).edges.filter fun e => decide (e.1 = v)).length =
      (J.E.filter fun e => J.tail e = u).card := by
    change (((vertsOf J.E).map fun e =>
        ((vertsOf J.V).idxOf (J.tail e), (vertsOf J.V).idxOf (J.head e))).filter
        fun e => decide (e.1 = v)).length = _
    rw [List.filter_map, List.length_map, count_vertsOf_filter]
    congr 1
    ext e
    simp only [Finset.mem_filter, Function.comp_apply, decide_eq_true_eq]
    constructor
    · rintro ⟨he, hidx⟩
      refine ⟨he, ?_⟩
      have htV : J.tail e ∈ J.V := (hJ e he).1
      rw [← getD_vertsOf_idxOf htV, hidx]
    · rintro ⟨he, hEq⟩
      rw [hEq]
      exact ⟨he, idxOf_getD_vertsOf hv_card⟩
  have hhead : ((toCitedJ J).edges.filter fun e => decide (e.2 = v)).length =
      (J.E.filter fun e => J.head e = u).card := by
    change (((vertsOf J.E).map fun e =>
        ((vertsOf J.V).idxOf (J.tail e), (vertsOf J.V).idxOf (J.head e))).filter
        fun e => decide (e.2 = v)).length = _
    rw [List.filter_map, List.length_map, count_vertsOf_filter]
    congr 1
    ext e
    simp only [Finset.mem_filter, Function.comp_apply, decide_eq_true_eq]
    constructor
    · rintro ⟨he, hidx⟩
      refine ⟨he, ?_⟩
      have hhV : J.head e ∈ J.V := (hJ e he).2
      rw [← getD_vertsOf_idxOf hhV, hidx]
    · rintro ⟨he, hEq⟩
      rw [hEq]
      exact ⟨he, idxOf_getD_vertsOf hv_card⟩
  have hf1 : ((toCitedJ J).edges.filter fun e => e.1 = v) =
      ((toCitedJ J).edges.filter fun e => decide (e.1 = v)) := by simp
  have hf2 : ((toCitedJ J).edges.filter fun e => e.2 = v) =
      ((toCitedJ J).edges.filter fun e => decide (e.2 = v)) := by simp
  rw [hf1, hf2, htail, hhead]
  exact Finset.le_sup (f := J.deg) huV

private lemma mgraph_walkVertices_getLast? {G : MGraph} :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, G.IsWalk u v P →
      (G.walkVertices u P).getLast? = some v
  | u, _, [], .nil _ => by simp [MGraph.walkVertices]
  | u, v, x :: xs, .cons _ _ hP => by
    have ih := mgraph_walkVertices_getLast? hP
    cases hxs : xs with
    | nil =>
      subst hxs
      cases hP
      simp [MGraph.walkVertices]
    | cons b bs =>
      subst hxs
      simp only [MGraph.walkVertices, List.map_cons, List.getLast?_cons_cons] at ih ⊢
      exact ih

private lemma mgraph_walkVertices_step {G : MGraph} :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, G.IsWalk u v P →
      ∀ i, (hi : i < P.length) →
        (G.walkVertices u P).getD i 0 = G.src (P[i]'hi) ∧
        (G.walkVertices u P).getD (i + 1) 0 = G.dst (P[i]'hi)
  | _, _, [], .nil _, i, hi => by simp at hi
  | u, _, x :: xs, .cons _ hsrc hP, i, hi => by
    cases i with
    | zero =>
      simp only [MGraph.walkVertices, List.map_cons, List.getD_eq_getElem?_getD,
        List.getElem?_cons_zero, Option.getD_some, zero_add, List.getElem?_cons_succ]
      exact ⟨hsrc.symm, rfl⟩
    | succ k =>
      have hk : k < xs.length := by simpa using hi
      have ih := mgraph_walkVertices_step hP k hk
      simp only [MGraph.walkVertices, List.map_cons, List.getD_eq_getElem?_getD,
        List.getElem?_cons_succ, List.getElem_cons_succ] at ih ⊢
      exact ih

lemma embToCited_isEmbedding {H' J : MGraph} {embJH : MinCostFlow.Embedding}
    (hJ : J.IsValid) (hemb : embJH.IsEmbedding J H') :
    IsEmbedding (toCitedJ J) (toCitedH H' J embJH) (embToCited H' J embJH) := by
  refine ⟨?_, ?_⟩
  · dsimp only [toCitedJ, toCitedH, hVerts]
    simp
  intro j hj
  have hj' : j < (vertsOf J.E).length := by
    dsimp only [toCitedJ, Graph.m] at hj; rw [List.length_map] at hj; exact hj
  set eJ := (vertsOf J.E).getD j 0
  have heJ : eJ ∈ J.E := getD_vertsOf_mem (vertsOf_length J.E ▸ hj')
  have he_eq : (toCitedJ J).edges[j]'hj =
      ((vertsOf J.V).idxOf (J.tail eJ), (vertsOf J.V).idxOf (J.head eJ)) := by
    rw [← List.getD_eq_getElem _ (0, 0) hj]
    simp only [toCitedJ, eJ, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hj']
    rfl
  rw [he_eq]
  have hwalk := hemb.2 eJ heJ
  have htV : J.tail eJ ∈ J.V := (hJ eJ heJ).1
  have hhV : J.head eJ ∈ J.V := (hJ eJ heJ).2
  have ht_idx : (vertsOf J.V).idxOf (J.tail eJ) = (hVerts H' J embJH).idxOf (J.tail eJ) :=
    (hVerts_idxOf_eq_vertsOf htV).symm
  have hh_idx : (vertsOf J.V).idxOf (J.head eJ) = (hVerts H' J embJH).idxOf (J.head eJ) :=
    (hVerts_idxOf_eq_vertsOf hhV).symm
  have ht_lt : (hVerts H' J embJH).idxOf (J.tail eJ) < (toCitedH H' J embJH).n :=
    hVerts_idxOf_lt (Finset.mem_union_left _ htV)
  have hh_lt : (hVerts H' J embJH).idxOf (J.head eJ) < (toCitedH H' J embJH).n :=
    hVerts_idxOf_lt (Finset.mem_union_left _ hhV)
  change Walk.IsWalk (toCitedH H' J embJH) _ _ (walkToCited H' (hVerts H' J embJH) (hEdges J embJH) (J.tail eJ) (embJH eJ))
  unfold walkToCited
  split_ifs with hPnil
  · have hnil : embJH eJ = [] := List.isEmpty_iff.mp hPnil
    rw [hnil] at hwalk
    have hth_eq := isWalk_dst_eq_of_nil hwalk
    refine ⟨ht_idx ▸ ht_lt, hh_idx ▸ hh_lt, Or.inl ⟨rfl, rfl, ?_⟩⟩
    rw [ht_idx, hh_idx, hth_eq]
  · have hPne : embJH eJ ≠ [] := fun h => by simp [h] at hPnil
    refine ⟨ht_idx ▸ ht_lt, hh_idx ▸ hh_lt, Or.inr ⟨by simp [hPne], by simp [MGraph.walkVertices], ?_, ?_, ?_, ?_⟩⟩
    · simp only [MGraph.walkVertices, List.map_cons, List.head?_cons, ht_idx]
    · have hlast := mgraph_walkVertices_getLast? hwalk
      simp only [List.getLast?_map, hlast, Option.map_some, hh_idx]
    · intro c hc
      rw [List.mem_map] at hc
      rcases hc with ⟨eH, heH, rfl⟩
      rw [List.mem_map] at heH
      rcases heH with ⟨y, hyP, rfl⟩
      have heH_mem : y.1 ∈ usedHEdges J embJH :=
        Finset.mem_biUnion.mpr ⟨eJ, heJ, List.mem_toFinset.mpr (List.mem_map.mpr ⟨y, hyP, rfl⟩)⟩
      rw [toCitedH_m]
      exact List.idxOf_lt_length_iff.mpr (mem_vertsOf.mpr heH_mem)
    · intro i hi
      have hi' : i < (embJH eJ).length := by simpa using hi
      have hstep := mgraph_walkVertices_step hwalk i hi'
      let y := (embJH eJ)[i]'hi'
      have hy_mem : y ∈ embJH eJ := List.getElem_mem hi'
      have heH_mem : y.1 ∈ usedHEdges J embJH :=
        Finset.mem_biUnion.mpr ⟨eJ, heJ, List.mem_toFinset.mpr (List.mem_map.mpr ⟨y, hy_mem, rfl⟩)⟩
      have heIdx_lt : (hEdges J embJH).idxOf y.1 < (hEdges J embJH).length :=
        List.idxOf_lt_length_iff.mpr (mem_vertsOf.mpr heH_mem)
      have he_get : (hEdges J embJH).getD ((hEdges J embJH).idxOf y.1) 0 = y.1 :=
        getD_vertsOf_idxOf heH_mem
      have hedge_idx : ((embJH eJ).map Prod.fst |>.map (hEdges J embJH).idxOf).getD i 0 =
          (hEdges J embJH).idxOf y.1 := by
        rw [List.getD_eq_getElem _ _ (by simpa using hi')]
        simp [y]
      have hedge_cH : (toCitedH H' J embJH).edges.getD
          (((embJH eJ).map Prod.fst |>.map (hEdges J embJH).idxOf).getD i 0) (0, 0) =
          ((hVerts H' J embJH).idxOf (H'.tail y.1), (hVerts H' J embJH).idxOf (H'.head y.1)) := by
        rw [hedge_idx]
        unfold toCitedH
        rw [List.getD_eq_getElem _ _ (by simp [heIdx_lt])]
        simp
      have hv_i : ((H'.walkVertices (J.tail eJ) (embJH eJ)).map (hVerts H' J embJH).idxOf).getD i 0 =
          (hVerts H' J embJH).idxOf (H'.src y) := by
        have hi_lt : i < (H'.walkVertices (J.tail eJ) (embJH eJ)).length := by
          simp [MGraph.walkVertices]; omega
        rw [List.getD_eq_getElem _ _ (by simp [hi_lt])]
        have hstep1 := hstep.1
        rw [List.getD_eq_getElem _ _ hi_lt] at hstep1
        simp [y, hstep1]
      have hv_i1 : ((H'.walkVertices (J.tail eJ) (embJH eJ)).map (hVerts H' J embJH).idxOf).getD (i + 1) 0 =
          (hVerts H' J embJH).idxOf (H'.dst y) := by
        have hi1_lt : i + 1 < (H'.walkVertices (J.tail eJ) (embJH eJ)).length := by
          simp [MGraph.walkVertices]; omega
        rw [List.getD_eq_getElem _ _ (by simp [hi1_lt])]
        have hstep2 := hstep.2
        rw [List.getD_eq_getElem _ _ hi1_lt] at hstep2
        simp [y, hstep2]
      rw [hedge_cH, hv_i, hv_i1]
      cases hyb : y.2
      · refine Or.inr ⟨by simp [MGraph.src, hyb], by simp [MGraph.dst, hyb]⟩
      · refine Or.inl ⟨by simp [MGraph.src, hyb], by simp [MGraph.dst, hyb]⟩

lemma length_embToCited_le (H' J : MGraph) (embJH : MinCostFlow.Embedding) :
    length (toCitedJ J) (embToCited H' J embJH) ≤ embJH.length J := by
  rw [length_le_iff]
  intro j hj
  have hj' : j < (vertsOf J.E).length := by
    dsimp only [toCitedJ, Graph.m] at hj; rw [List.length_map] at hj; exact hj
  set eJ := (vertsOf J.E).getD j 0
  have heJ : eJ ∈ J.E := getD_vertsOf_mem (vertsOf_length J.E ▸ hj')
  unfold embToCited walkToCited
  dsimp only
  split_ifs with hnil
  · exact Nat.zero_le _
  · have hlen : (((embJH eJ).map Prod.fst).map (hEdges J embJH).idxOf).length = (embJH eJ).length := by
      simp
    rw [hlen]
    exact Finset.le_sup (f := fun e => (embJH e).length) heJ

lemma vcong_embToCited_le {H' J : MGraph} {embJH : MinCostFlow.Embedding}
    (hH' : H'.IsValid) (hJ : J.IsValid) (hemb : embJH.IsEmbedding J H') :
    vcong (toCitedJ J) (toCitedH H' J embJH) (fun _ => 1) (embToCited H' J embJH) ≤
      embJH.vcong J H' (fun _ => 1) := by
  rw [vcong_le_iff]
  refine ⟨?_, ?_⟩
  · unfold Embedding.vcong
    split_ifs with hne
    · exact le_trans (Finset.sum_nonneg fun _ _ => zero_le_one)
        (Finset.le_sup' (embJH.vcongAt J H' (fun _ => 1)) hne.choose_spec)
    · exact le_rfl
  intro v_cit hv_cit
  have hv_len : v_cit < (hVerts H' J embJH).length := by simpa [toCitedH] using hv_cit
  let vH := (hVerts H' J embJH)[v_cit]'hv_len
  have hvH_used : vH ∈ usedHVerts H' J embJH := mem_hVerts.mp (List.getElem_mem hv_len)
  have hvH_V : vH ∈ H'.V := usedHVerts_subset_V hH' hJ hemb hvH_used
  have hmem_iff : ∀ j < (toCitedJ J).m,
      v_cit ∈ (embToCited H' J embJH j).verts →
        vH ∈ H'.walkVertices (J.tail ((vertsOf J.E).getD j 0)) (embJH ((vertsOf J.E).getD j 0)) := by
    intro j hj hvmem
    have hj_c : j < J.E.card := show j < J.m from (toCitedJ_m J) ▸ hj
    have heJ : (vertsOf J.E).getD j 0 ∈ J.E := getD_vertsOf_mem hj_c
    unfold embToCited walkToCited at hvmem
    dsimp only at hvmem
    split_ifs at hvmem
    · simp [Walk.empty] at hvmem
    · rw [List.mem_map] at hvmem
      rcases hvmem with ⟨w, hw, hwidx⟩
      have hw_u : w ∈ usedHVerts H' J embJH :=
        Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_, heJ, List.mem_toFinset.mpr hw⟩)
      have hw_eq : w = vH := by
        have h1 := getElem_hVerts_idxOf hw_u
        simpa [vH, hwidx] using h1.symm
      exact hw_eq ▸ hw
  have hcard_le : ((Finset.range (toCitedJ J).m).filter fun j =>
      v_cit ∈ (embToCited H' J embJH j).verts).card ≤
      (J.E.filter fun e => vH ∈ H'.walkVertices (J.tail e) (embJH e)).card := by
    refine Finset.card_le_card_of_injOn (fun j => (vertsOf J.E).getD j 0) ?_ ?_
    · intro j hj
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
      have hj_c : j < J.E.card := show j < J.m from (toCitedJ_m J) ▸ hj.1
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨getD_vertsOf_mem hj_c, hmem_iff j hj.1 hj.2⟩)
    · intro j₁ hj₁ j₂ hj₂ heq
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj₁ hj₂
      have hj₁_c : j₁ < J.E.card := show j₁ < J.m from (toCitedJ_m J) ▸ hj₁.1
      have hj₂_c : j₂ < J.E.card := show j₂ < J.m from (toCitedJ_m J) ▸ hj₂.1
      have h1 := idxOf_getD_vertsOf hj₁_c
      have h2 := idxOf_getD_vertsOf hj₂_c
      dsimp only at heq
      rw [heq] at h1
      exact h1.symm.trans h2
  have hcit_eq : vcongAt (toCitedJ J) (fun _ => 1) (embToCited H' J embJH) v_cit =
      (((Finset.range (toCitedJ J).m).filter fun j =>
        v_cit ∈ (embToCited H' J embJH j).verts).card : ℝ) := by
    unfold vcongAt
    simp
  have hmg_eq : embJH.vcongAt J H' (fun _ => 1) vH =
      ((J.E.filter fun e => vH ∈ H'.walkVertices (J.tail e) (embJH e)).card : ℝ) := by
    unfold Embedding.vcongAt
    simp
  have hle_at : vcongAt (toCitedJ J) (fun _ => 1) (embToCited H' J embJH) v_cit ≤
      embJH.vcongAt J H' (fun _ => 1) vH := by
    rw [hcit_eq, hmg_eq]
    exact_mod_cast hcard_le
  have hsup : embJH.vcongAt J H' (fun _ => 1) vH ≤ embJH.vcong J H' (fun _ => 1) := by
    simp only [Embedding.vcong]
    split_ifs with hne
    · exact Finset.le_sup' (fun x => embJH.vcongAt J H' (fun _ => 1) x) hvH_V
    · exact absurd ⟨vH, hvH_V⟩ hne
  exact le_trans hle_at hsup

/-! ## Subgraph and reverse embedding translation (`outJtilde`, `citedEmbToMGraph`) -/

lemma outJtilde_isSubgraph (J : MGraph) (kept : List ℕ) (hkept : ∀ j ∈ kept, j < J.m) :
    J.IsSubgraph (outJtilde J kept) := by
  refine ⟨Finset.Subset.rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
  intro e he
  unfold outJtilde at he
  dsimp only at he
  rw [List.mem_toFinset, List.mem_map] at he
  rcases he with ⟨j, hj_mem, rfl⟩
  exact getD_vertsOf_mem (hkept j hj_mem)

lemma outJtilde_isValid {J : MGraph} (hJ : J.IsValid) (kept : List ℕ)
    (hkept : ∀ j ∈ kept, j < J.m) : (outJtilde J kept).IsValid := by
  intro e he
  exact hJ e ((outJtilde_isSubgraph J kept hkept).2.1 he)

lemma outJtilde_m_eq (J : MGraph) (kept : List ℕ) (hnodup : kept.Nodup)
    (hkept : ∀ j ∈ kept, j < J.m) : (outJtilde J kept).m = kept.length := by
  unfold outJtilde MGraph.m
  dsimp only
  have hnodup_map : (kept.map fun j => (vertsOf J.E).getD j 0).Nodup := by
    refine hnodup.map_on ?_
    intro j₁ hj₁ j₂ hj₂ heq
    have h1 := idxOf_getD_vertsOf (hkept j₁ hj₁)
    have h2 := idxOf_getD_vertsOf (hkept j₂ hj₂)
    rw [heq] at h1
    exact h1.symm.trans h2
  rw [List.toFinset_card_of_nodup hnodup_map, List.length_map]

end MinCostFlow.Spanner

