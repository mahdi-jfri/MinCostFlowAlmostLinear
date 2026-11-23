module

public import MinCostFlow.ExpanderDecomp.MatchingPlayer
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Local graph utilities, walks, and parameters for `RouteOrCut`

This file provides the shared foundations for the static multi-pair matching router
`RouteOrCut`:

* The integer parameters `routeH`, `routeD`, `routeHBatch`, and `routeR`,
  together with the congestion bound `routeR_le` (`R ≤ 528 Δ² b² L²`).
* Integer binomial inequalities `two_mul_pow_le_succ_pow` (`2 h^h ≤ (h + 1)^h`) and
  `two_mul_pred_pow_lt_pow` (`2 (H - 1)^H < H^H`), used for ball growing and batch halving.
* Local adjacency lists `adjOf G X` for the induced subgraph `G[X]`, whose lengths equal
  `G.degIn X v` and sum to `2 * (G.inside X).length`.
* Walks and simple walks inside a vertex subset `V` (`IsEdgeWalkIn`, `walkVerts`,
  `IsSimpleWalkIn`), with prefix/suffix splitting and disjointness transfer to edges.
* Disjoint terminal pairs (`ValidTerminalPairs`) and cut-composition lemmas for ball growing
  and isolating path vertices.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Parameters -/

/-- Maximum path length `d = 2 h L = 32 Δ b L`, matching `routePathLen`. -/
abbrev routeD (Δ b L : ℕ) : ℕ :=
  routePathLen Δ b L

/-- Batch progress factor `H_batch = 16 b Δ (d + 1)`, matching `routeBatchH`. -/
abbrev routeHBatch (Δ b L : ℕ) : ℕ :=
  routeBatchH Δ b L

/-- Maximum number of batches and congestion bound `R = H_batch * L`, matching `routeCong`. -/
abbrev routeR (Δ b L : ℕ) : ℕ :=
  routeCong Δ b L

/-! ### Local adjacency lists for `G[X]` -/

/-- Indexed edges of `G` with both ends in `X`: pairs `(j, e)` with `j < G.m` and
`e = edgeAt G.edges j`. -/
def insideEdgesIdx (G : Graph) (X : Finset ℕ) : List (ℕ × (ℕ × ℕ)) :=
  (G.edges.zipIdx.map Prod.swap).filter fun ie => insideB X ie.2

/-- Local adjacency list of `v` in `G[X]`: pairs `(w, j)` where edge number `j` of `G` has both
ends in `X` and connects `v` to `w`. A loop at `v` appears twice, matching `G.degIn X v`. -/
def adjOf (G : Graph) (X : Finset ℕ) (v : ℕ) : List (ℕ × ℕ) :=
  (insideEdgesIdx G X).flatMap fun ie =>
    (if ie.2.1 = v then [(ie.2.2, ie.1)] else []) ++
      (if ie.2.2 = v then [(ie.2.1, ie.1)] else [])

/-! ### Walks inside a vertex subset and vertex traces -/

/-- A walk from `u` to `v` in `G` whose edges all have both ends in `V`. -/
def IsEdgeWalkIn (G : Graph) (V : Finset ℕ) (u v : ℕ) (es : List ℕ) : Prop :=
  IsEdgeWalk G.edges u v es ∧ ∀ i ∈ es, insideB V (edgeAt G.edges i) = true

/-- The other endpoint of edge `j` when leaving vertex `u`. -/
def walkStep (E : List (ℕ × ℕ)) (u j : ℕ) : ℕ :=
  if (edgeAt E j).1 = u then (edgeAt E j).2 else (edgeAt E j).1

/-- The sequence of vertices visited by starting at `u` and following edge list `es`. -/
def walkVerts (E : List (ℕ × ℕ)) (u : ℕ) : List ℕ → List ℕ
  | [] => [u]
  | j :: es => u :: walkVerts E (walkStep E u j) es

/-- A simple walk in `G[V]`: a walk in `G[V]` whose visited vertices have no duplicates. -/
def IsSimpleWalkIn (G : Graph) (V : Finset ℕ) (u v : ℕ) (es : List ℕ) : Prop :=
  IsEdgeWalkIn G V u v es ∧ (walkVerts G.edges u es).Nodup

/-! ### Terminal pairs -/

/-- Pairwise disjoint terminal pairs `(A_i, B_i)` inside `X` with `|A_i| ≤ |B_i|`. -/
def RouteTerminalPairs (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)) : Prop :=
  (∀ p ∈ pairs, p.1 ⊆ X ∧ p.2 ⊆ X ∧ p.1.card ≤ p.2.card ∧ Disjoint p.1 p.2) ∧
    pairs.Pairwise fun p q => Disjoint (p.1 ∪ p.2) (q.1 ∪ q.2)

/-- Total demand `∑_i |A_i|` of a list of terminal pairs. -/
def totalDemand (pairs : List (Finset ℕ × Finset ℕ)) : ℕ :=
  (pairs.map fun p => p.1.card).sum

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Parameter bounds -/

theorem routeD_eq_two_mul_routeH (Δ b L : ℕ) :
    routeD Δ b L = 2 * routeH Δ b * L := by
  unfold routeD routePathLen routeH
  ring

theorem routeH_pos {Δ b : ℕ} (hΔ : 1 ≤ Δ) (hb : 1 ≤ b) : 0 < routeH Δ b := by
  unfold routeH
  have h1 : 1 ≤ Δ * b := Nat.mul_pos hΔ hb
  have h2 : 16 * Δ * b = 16 * (Δ * b) := by ring
  omega

theorem routeHBatch_ge_two {Δ b L : ℕ} (hΔ : 1 ≤ Δ) (hb : 1 ≤ b) :
    2 ≤ routeHBatch Δ b L := by
  unfold routeHBatch routeBatchH
  have h1 : 1 ≤ b * Δ := Nat.mul_pos hb hΔ
  have h2 : 1 ≤ routePathLen Δ b L + 1 := Nat.succ_pos _
  have h3 : 1 ≤ b * Δ * (routePathLen Δ b L + 1) := Nat.mul_pos h1 h2
  have h4 : 16 * b * Δ * (routePathLen Δ b L + 1) = 16 * (b * Δ * (routePathLen Δ b L + 1)) := by ring
  omega

theorem routeR_pos {Δ b L : ℕ} (hΔ : 1 ≤ Δ) (hb : 1 ≤ b) (hL : 1 ≤ L) :
    0 < routeR Δ b L := by
  unfold routeR routeCong
  exact Nat.mul_pos (lt_of_lt_of_le (by decide) (routeHBatch_ge_two hΔ hb)) hL

/-- Congestion bound: `R ≤ 528 Δ² b² L²` for `Δ, b, L ≥ 1`. -/
theorem routeR_le {Δ b L : ℕ} (hΔ : 1 ≤ Δ) (hb : 1 ≤ b) (hL : 1 ≤ L) :
    routeR Δ b L ≤ 528 * Δ ^ 2 * b ^ 2 * L ^ 2 :=
  routeCong_le hΔ hb hL

/-! ### Integer binomial inequalities -/

private lemma bernoulli_nat (h k : ℕ) :
    h ^ k + k * h ^ (k - 1) ≤ (h + 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    cases k with
    | zero => simp
    | succ m =>
      have hmul : (h ^ (m + 1) + (m + 1) * h ^ m) * (h + 1) ≤ (h + 1) ^ (m + 1) * (h + 1) :=
        Nat.mul_le_mul_right (h + 1) ih
      have hlhs : h ^ (m + 2) + (m + 2) * h ^ (m + 1) ≤
          (h ^ (m + 1) + (m + 1) * h ^ m) * (h + 1) := by
        have hpow : h ^ (m + 2) = h ^ (m + 1) * h := by rw [Nat.pow_succ]
        have hpow' : h ^ (m + 1) = h ^ m * h := by rw [Nat.pow_succ]
        calc
          h ^ (m + 2) + (m + 2) * h ^ (m + 1)
              = h ^ (m + 1) * h + (m + 1) * (h ^ m * h) + h ^ (m + 1) := by
                rw [hpow, ← hpow']; ring
          _ ≤ h ^ (m + 1) * h + (m + 1) * (h ^ m * h) + h ^ (m + 1) + (m + 1) * h ^ m :=
                Nat.le_add_right _ _
          _ = (h ^ (m + 1) + (m + 1) * h ^ m) * (h + 1) := by ring
      calc
        h ^ (m + 2) + (m + 2) * h ^ (m + 2 - 1)
            = h ^ (m + 2) + (m + 2) * h ^ (m + 1) := rfl
        _ ≤ (h + 1) ^ (m + 1) * (h + 1) := le_trans hlhs hmul
        _ = (h + 1) ^ (m + 2) := (Nat.pow_succ (h + 1) (m + 1)).symm

/-- Integer form of `(1 + 1/h)^h ≥ 2`: for `h ≥ 1`, `2 * h^h ≤ (h + 1)^h`. -/
theorem two_mul_pow_le_succ_pow {h : ℕ} (hh : 1 ≤ h) :
    2 * h ^ h ≤ (h + 1) ^ h := by
  have hb := bernoulli_nat h h
  have hpow : h * h ^ (h - 1) = h ^ h := by
    cases h with
    | zero => omega
    | succ m =>
      simp only [Nat.add_sub_cancel]
      rw [Nat.pow_succ, Nat.mul_comm]
  rw [hpow] at hb
  omega

/-- Integer form of `(1 - 1/H)^H < 1/2`: for `H ≥ 2`, `2 * (H - 1)^H < H^H`. -/
theorem two_mul_pred_pow_lt_pow {H : ℕ} (hH : 2 ≤ H) :
    2 * (H - 1) ^ H < H ^ H := by
  set k := H - 1
  have hk : 1 ≤ k := by omega
  have hEq : H = k + 1 := by omega
  rw [hEq]
  have hbase : 2 * k ^ k ≤ (k + 1) ^ k := two_mul_pow_le_succ_pow hk
  have hkpos : 0 < k ^ k := Nat.pow_pos (by omega)
  calc
    2 * k ^ (k + 1) = 2 * k ^ k * k := by rw [Nat.pow_succ]; ring
    _ < 2 * k ^ k * (k + 1) := Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self k) (by omega)
    _ ≤ (k + 1) ^ k * (k + 1) := Nat.mul_le_mul_right (k + 1) hbase
    _ = (k + 1) ^ (k + 1) := (Nat.pow_succ (k + 1) k).symm

/-! ### Local adjacency lemmas -/

private lemma zipIdx_map_swap_snd {α : Type*} (l : List α) (n : ℕ) :
    ((l.zipIdx n).map Prod.swap).map Prod.snd = l := by
  induction l generalizing n with
  | nil => simp
  | cons a t ih => simp [List.zipIdx_cons, ih]

private lemma map_filter_comp {α β : Type*} (l : List α) (f : α → β) (p : β → Bool) :
    (l.filter fun x => p (f x)).map f = (l.map f).filter p := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases h : p (f a)
    · simp [h, ih]
    · simp [h, ih]

theorem insideEdgesIdx_map_snd (G : Graph) (X : Finset ℕ) :
    (insideEdgesIdx G X).map Prod.snd = G.inside X := by
  unfold insideEdgesIdx Graph.inside
  rw [map_filter_comp _ Prod.snd (insideB X), zipIdx_map_swap_snd]
  rfl

theorem insideEdgesIdx_length (G : Graph) (X : Finset ℕ) :
    (insideEdgesIdx G X).length = (G.inside X).length := by
  rw [← List.length_map Prod.snd, insideEdgesIdx_map_snd]

theorem mem_insideEdgesIdx_iff (G : Graph) (X : Finset ℕ) (j : ℕ) (e : ℕ × ℕ) :
    (j, e) ∈ insideEdgesIdx G X ↔
      j < G.m ∧ e = edgeAt G.edges j ∧ insideB X e = true := by
  unfold insideEdgesIdx Graph.m edgeAt
  simp only [List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨⟨⟨e', j'⟩, hmem, hswap⟩, hin⟩
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hswap
    rcases hswap with ⟨rfl, rfl⟩
    rw [List.mem_zipIdx_iff_getElem?] at hmem
    have hj : j' < G.edges.length := by
      by_contra hge
      rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hmem
      cases hmem
    refine ⟨hj, ?_, hin⟩
    rw [List.getD_eq_getElem?_getD, hmem]
    rfl
  · rintro ⟨hj, rfl, hin⟩
    refine ⟨⟨(G.edges.getD j (0, 0), j), ?_, rfl⟩, hin⟩
    rw [List.mem_zipIdx_iff_getElem?]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      Option.getD_some]

theorem mem_adjOf_iff (G : Graph) (X : Finset ℕ) (v w j : ℕ) :
    (w, j) ∈ adjOf G X v ↔
      j < G.m ∧ insideB X (edgeAt G.edges j) = true ∧
        (((edgeAt G.edges j).1 = v ∧ (edgeAt G.edges j).2 = w) ∨
          ((edgeAt G.edges j).1 = w ∧ (edgeAt G.edges j).2 = v)) := by
  unfold adjOf
  simp only [List.mem_flatMap, List.mem_append]
  constructor
  · rintro ⟨⟨j', e⟩, hmem, hpair⟩
    rw [mem_insideEdgesIdx_iff] at hmem
    obtain ⟨hj, rfl, hin⟩ := hmem
    rcases hpair with h1 | h2
    · split_ifs at h1 with hEq
      · simp only [List.mem_singleton, Prod.mk.injEq] at h1
        rcases h1 with ⟨rfl, rfl⟩
        exact ⟨hj, hin, Or.inl ⟨hEq, rfl⟩⟩
      · simp at h1
    · split_ifs at h2 with hEq
      · simp only [List.mem_singleton, Prod.mk.injEq] at h2
        rcases h2 with ⟨rfl, rfl⟩
        exact ⟨hj, hin, Or.inr ⟨rfl, hEq⟩⟩
      · simp at h2
  · rintro ⟨hj, hin, hpair⟩
    refine ⟨(j, edgeAt G.edges j), (mem_insideEdgesIdx_iff G X j _).mpr ⟨hj, rfl, hin⟩, ?_⟩
    rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      simp [h1, h2]
    · right
      simp [h1, h2]

theorem adjOf_mem_left {G : Graph} {X : Finset ℕ} {v w j : ℕ}
    (h : (w, j) ∈ adjOf G X v) : w ∈ X := by
  rw [mem_adjOf_iff] at h
  obtain ⟨_, hin, hpair⟩ := h
  unfold insideB at hin
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
  rcases hpair with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact h2 ▸ hin.2
  · exact h1 ▸ hin.1

theorem adjOf_length_eq_degIn (G : Graph) (X : Finset ℕ) (v : ℕ) :
    (adjOf G X v).length = G.degIn X v := by
  rw [degIn_eq_sum_map, ← insideEdgesIdx_map_snd]
  unfold adjOf
  rw [List.length_flatMap, List.map_map]
  congr 1
  apply List.map_congr_left
  intro ie _
  simp only [Function.comp_apply, List.length_append]
  by_cases h1 : ie.2.1 = v <;> by_cases h2 : ie.2.2 = v <;> simp [h1, h2]

theorem sum_adjOf_length (G : Graph) (X : Finset ℕ) :
    ∑ v ∈ X, (adjOf G X v).length = 2 * (G.inside X).length := by
  simp_rw [adjOf_length_eq_degIn]
  exact volIn_self G X

theorem sum_adjOf_length_le (G : Graph) {X V : Finset ℕ} (hVX : V ⊆ X) :
    ∑ v ∈ V, (adjOf G X v).length ≤ 2 * (G.inside X).length := by
  calc
    ∑ v ∈ V, (adjOf G X v).length
        ≤ ∑ v ∈ X, (adjOf G X v).length :=
          Finset.sum_le_sum_of_subset hVX
    _ = 2 * (G.inside X).length := sum_adjOf_length G X

/-! ### Walks inside `G[V]` and vertex traces -/

theorem IsEdgeWalkIn.nil (G : Graph) (V : Finset ℕ) (u : ℕ) :
    IsEdgeWalkIn G V u u [] :=
  ⟨IsEdgeWalk.nil u, by simp⟩

theorem IsEdgeWalkIn.cons_of_adj {G : Graph} {X V : Finset ℕ} {u x v j : ℕ} {es : List ℕ}
    (hadj : (x, j) ∈ adjOf G X u) (hu : u ∈ V) (hx : x ∈ V)
    (hrest : IsEdgeWalkIn G V x v es) :
    IsEdgeWalkIn G V u v (j :: es) := by
  rw [mem_adjOf_iff] at hadj
  obtain ⟨hj, _, hend⟩ := hadj
  refine ⟨IsEdgeWalk.cons hj hend hrest.1, ?_⟩
  intro i hi
  rcases List.mem_cons.mp hi with rfl | hi
  · unfold insideB
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1 ▸ hu, h2 ▸ hx⟩
    · exact ⟨h1 ▸ hx, h2 ▸ hu⟩
  · exact hrest.2 i hi

theorem IsEdgeWalkIn.mono {G : Graph} {V W : Finset ℕ} (hVW : V ⊆ W) {u v : ℕ} {es : List ℕ}
    (h : IsEdgeWalkIn G V u v es) : IsEdgeWalkIn G W u v es := by
  refine ⟨h.1, fun i hi => ?_⟩
  have h1 := h.2 i hi
  unfold insideB at h1 ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 ⊢
  exact ⟨hVW h1.1, hVW h1.2⟩

theorem IsEdgeWalk.append {E : List (ℕ × ℕ)} {u x v : ℕ} {es₁ es₂ : List ℕ}
    (h1 : IsEdgeWalk E u x es₁) (h2 : IsEdgeWalk E x v es₂) :
    IsEdgeWalk E u v (es₁ ++ es₂) := by
  induction h1 with
  | nil => exact h2
  | cons hj hend _ ih => exact IsEdgeWalk.cons hj hend (ih h2)

theorem IsEdgeWalkIn.append {G : Graph} {V : Finset ℕ} {u x v : ℕ} {es₁ es₂ : List ℕ}
    (h1 : IsEdgeWalkIn G V u x es₁) (h2 : IsEdgeWalkIn G V x v es₂) :
    IsEdgeWalkIn G V u v (es₁ ++ es₂) := by
  refine ⟨h1.1.append h2.1, fun i hi => ?_⟩
  rcases List.mem_append.mp hi with hi | hi
  · exact h1.2 i hi
  · exact h2.2 i hi

theorem IsEdgeWalk.reverse {E : List (ℕ × ℕ)} {u v : ℕ} {es : List ℕ}
    (h : IsEdgeWalk E u v es) : IsEdgeWalk E v u es.reverse := by
  induction h with
  | nil u => exact IsEdgeWalk.nil u
  | cons hj hend _ ih =>
    rw [List.reverse_cons]
    exact ih.append (IsEdgeWalk.cons hj hend.symm (IsEdgeWalk.nil _))

theorem IsEdgeWalkIn.reverse {G : Graph} {V : Finset ℕ} {u v : ℕ} {es : List ℕ}
    (h : IsEdgeWalkIn G V u v es) : IsEdgeWalkIn G V v u es.reverse := by
  refine ⟨h.1.reverse, fun i hi => h.2 i (List.mem_reverse.mp hi)⟩

theorem walkStep_of_hend {E : List (ℕ × ℕ)} {u x j : ℕ}
    (hend : ((edgeAt E j).1 = u ∧ (edgeAt E j).2 = x) ∨
      ((edgeAt E j).1 = x ∧ (edgeAt E j).2 = u)) :
    walkStep E u j = x := by
  unfold walkStep
  rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, h2]
  · split_ifs with hEq
    · exact (hEq.symm.trans h1).symm ▸ h2
    · exact h1

theorem walkVerts_length (E : List (ℕ × ℕ)) (u : ℕ) (es : List ℕ) :
    (walkVerts E u es).length = es.length + 1 := by
  induction es generalizing u with
  | nil => simp [walkVerts]
  | cons j es ih => simp [walkVerts, ih]

theorem walkVerts_head (E : List (ℕ × ℕ)) (u : ℕ) (es : List ℕ) :
    (walkVerts E u es).head? = some u := by
  cases es <;> rfl

theorem mem_walkVerts_start (E : List (ℕ × ℕ)) (u : ℕ) (es : List ℕ) :
    u ∈ walkVerts E u es := by
  cases es <;> simp [walkVerts]

theorem IsEdgeWalk.mem_walkVerts_end {E : List (ℕ × ℕ)} {u v : ℕ} {es : List ℕ}
    (h : IsEdgeWalk E u v es) : v ∈ walkVerts E u es := by
  induction h with
  | nil u => simp [walkVerts]
  | cons _ hend _ ih =>
    simp only [walkVerts, walkStep_of_hend hend, List.mem_cons]
    exact Or.inr ih

theorem IsEdgeWalk.edge_endpoints_mem_walkVerts {E : List (ℕ × ℕ)} {u v : ℕ} {es : List ℕ}
    (h : IsEdgeWalk E u v es) {i : ℕ} (hi : i ∈ es) :
    (edgeAt E i).1 ∈ walkVerts E u es ∧ (edgeAt E i).2 ∈ walkVerts E u es := by
  induction h with
  | nil => simp at hi
  | cons _ hend hrest ih =>
    rename_i u' x' v' j' es'
    simp only [walkVerts, walkStep_of_hend hend]
    rcases List.mem_cons.mp hi with rfl | hi'
    · rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by simp [h1], by simp [h2, mem_walkVerts_start]⟩
      · exact ⟨by simp [h1, mem_walkVerts_start], by simp [h2]⟩
    · obtain ⟨h1, h2⟩ := ih hi'
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

/-- Vertex-disjoint walks are edge-disjoint. -/
theorem IsEdgeWalk.edge_disjoint_of_walkVerts_disjoint {E : List (ℕ × ℕ)}
    {u₁ v₁ u₂ v₂ : ℕ} {es₁ es₂ : List ℕ}
    (h1 : IsEdgeWalk E u₁ v₁ es₁) (h2 : IsEdgeWalk E u₂ v₂ es₂)
    (hdisj : ∀ w, w ∈ walkVerts E u₁ es₁ → w ∉ walkVerts E u₂ es₂) :
    ∀ i, i ∈ es₁ → i ∉ es₂ := by
  intro i hi1 hi2
  have hp1 := (h1.edge_endpoints_mem_walkVerts hi1).1
  have hp2 := (h2.edge_endpoints_mem_walkVerts hi2).1
  exact hdisj _ hp1 hp2

theorem IsEdgeWalkIn.walkVerts_subset {G : Graph} {V : Finset ℕ} {u v : ℕ} {es : List ℕ}
    (h : IsEdgeWalkIn G V u v es) (hu : u ∈ V) :
    ∀ w ∈ walkVerts G.edges u es, w ∈ V := by
  rcases h with ⟨hw, hin⟩
  revert hin hu
  induction hw with
  | nil u =>
    intro hu _ w hw'
    simp only [walkVerts, List.mem_singleton] at hw'
    exact hw' ▸ hu
  | cons hj hend hrest ih =>
    rename_i u' x' v' j' es'
    intro hu hin
    have hinj : insideB V (edgeAt G.edges j') = true := hin j' List.mem_cons_self
    unfold insideB at hinj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hinj
    have hxV : x' ∈ V := by
      rcases hend with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2 ▸ hinj.2
      · exact h1 ▸ hinj.1
    intro w hw'
    simp only [walkVerts, walkStep_of_hend hend, List.mem_cons] at hw'
    rcases hw' with rfl | hw'
    · exact hu
    · exact ih hxV (fun i hi => hin i (List.mem_cons_of_mem _ hi)) w hw'

/-- Splitting a walk `es` in `G[V]` at position `r ≤ es.length` gives a prefix walk of length `r`
and a suffix walk of length `es.length - r` meeting at `(walkVerts G.edges u es)[r]`. -/
theorem IsEdgeWalkIn.split_at {G : Graph} {V : Finset ℕ} {u v : ℕ} {es : List ℕ}
    (h : IsEdgeWalkIn G V u v es) {r : ℕ} (hr : r ≤ es.length) :
    ∃ x, (walkVerts G.edges u es).getD r 0 = x ∧
      IsEdgeWalkIn G V u x (es.take r) ∧
      IsEdgeWalkIn G V x v (es.drop r) := by
  rcases h with ⟨hw, hin⟩
  revert hin
  induction hw generalizing r with
  | nil u =>
    intro _
    have hr0 : r = 0 := by simpa using hr
    subst hr0
    exact ⟨u, rfl, IsEdgeWalkIn.nil G V u, IsEdgeWalkIn.nil G V u⟩
  | cons hj hend hrest ih =>
    rename_i u' x' v' j' es'
    intro hin
    cases r with
    | zero =>
      exact ⟨u', rfl, IsEdgeWalkIn.nil G V u',
        ⟨IsEdgeWalk.cons hj hend hrest, hin⟩⟩
    | succ r' =>
      have hr' : r' ≤ es'.length := by simpa using hr
      obtain ⟨y, hy, hpre, hsuf⟩ := ih hr' (fun i hi => hin i (List.mem_cons_of_mem _ hi))
      refine ⟨y, ?_, ?_, hsuf⟩
      · simp only [walkVerts, walkStep_of_hend hend, List.getD_cons_succ]
        exact hy
      · refine ⟨IsEdgeWalk.cons hj hend hpre.1, ?_⟩
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact hin i List.mem_cons_self
        · exact hpre.2 i hi

/-- A walk in `H_res = ⟨G.n, G.inside V_act⟩` whose edges are inside `V` gives a walk in `G`
of the same length whose edges are inside `V ∩ V_act` (and hence inside `V_act`). -/
theorem IsEdgeWalkIn.of_inside_graph {G : Graph} {V_act V : Finset ℕ} {u v : ℕ} {es : List ℕ}
    (h : IsEdgeWalkIn ⟨G.n, G.inside V_act⟩ V u v es) :
    ∃ es', es'.length = es.length ∧ IsEdgeWalkIn G (V ∩ V_act) u v es' := by
  rcases h with ⟨hw, hin⟩
  revert hin
  induction hw with
  | nil u =>
    intro _
    exact ⟨[], rfl, IsEdgeWalkIn.nil G (V ∩ V_act) u⟩
  | cons hj hend hrest ih =>
    rename_i u' x' v' j' es'
    intro hin
    have hmem_in : edgeAt (G.inside V_act) j' ∈ G.inside V_act := by
      unfold edgeAt
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    have hmem_in' : edgeAt (G.inside V_act) j' ∈ (insideEdgesIdx G V_act).map Prod.snd := by
      rwa [insideEdgesIdx_map_snd]
    rw [List.mem_map] at hmem_in'
    obtain ⟨⟨idx, e⟩, hidx, he_eq⟩ := hmem_in'
    rw [mem_insideEdgesIdx_iff] at hidx
    obtain ⟨hidx_lt, heq, hin_act⟩ := hidx
    have hedge : edgeAt (G.inside V_act) j' = edgeAt G.edges idx := he_eq.symm.trans heq
    have hinV : insideB V (edgeAt (G.inside V_act) j') = true := hin j' List.mem_cons_self
    obtain ⟨es'', hlen, hwalk''⟩ := ih (fun i hi => hin i (List.mem_cons_of_mem _ hi))
    refine ⟨idx :: es'', by simp [hlen], ?_⟩
    refine ⟨IsEdgeWalk.cons hidx_lt (hedge ▸ hend) hwalk''.1, ?_⟩
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [hedge] at hinV
      rw [heq] at hin_act
      unfold insideB at hinV hin_act ⊢
      simp only [Bool.and_eq_true, decide_eq_true_eq, Finset.mem_inter] at hinV hin_act ⊢
      exact ⟨⟨hinV.1, hin_act.1⟩, ⟨hinV.2, hin_act.2⟩⟩
    · exact hwalk''.2 i hi

/-! ### Terminal pairs demand bound -/

private lemma disjoint_foldr_pairs (S : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ))
    (h : ∀ q ∈ pairs, Disjoint S (q.1 ∪ q.2)) :
    Disjoint S (pairs.foldr (fun (q : Finset ℕ × Finset ℕ) (acc : Finset ℕ) => (q.1 ∪ q.2) ∪ acc) ∅) := by
  induction pairs with
  | nil => simp
  | cons q rest ih =>
    simp only [List.foldr_cons]
    exact Finset.disjoint_union_right.mpr
      ⟨h q List.mem_cons_self, ih fun r hr => h r (List.mem_cons_of_mem _ hr)⟩

private lemma card_biUnion_pairs_eq (pairs : List (Finset ℕ × Finset ℕ))
    (hpw : pairs.Pairwise fun p q => Disjoint (p.1 ∪ p.2) (q.1 ∪ q.2)) :
    (pairs.foldr (fun (p : Finset ℕ × Finset ℕ) (acc : Finset ℕ) => (p.1 ∪ p.2) ∪ acc) ∅).card =
      (pairs.map fun p => (p.1 ∪ p.2).card).sum := by
  induction pairs with
  | nil => simp
  | cons p rest ih =>
    rw [List.pairwise_cons] at hpw
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    have hdisj := disjoint_foldr_pairs (p.1 ∪ p.2) rest hpw.1
    rw [Finset.card_union_of_disjoint hdisj, ih hpw.2]

private lemma foldr_pairs_subset {X : Finset ℕ} (pairs : List (Finset ℕ × Finset ℕ))
    (hsub : ∀ p ∈ pairs, p.1 ⊆ X ∧ p.2 ⊆ X) :
    pairs.foldr (fun (p : Finset ℕ × Finset ℕ) (acc : Finset ℕ) => (p.1 ∪ p.2) ∪ acc) ∅ ⊆ X := by
  induction pairs with
  | nil => simp
  | cons p rest ih =>
    simp only [List.foldr_cons]
    have hp := hsub p List.mem_cons_self
    exact Finset.union_subset (Finset.union_subset hp.1 hp.2)
      (ih fun q hq => hsub q (List.mem_cons_of_mem _ hq))

/-- Equivalence from `MatchingPlayer.ValidTerminalPairs` to `RouteTerminalPairs`. -/
theorem routeTerminalPairs_of_validTerminalPairs {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} (h : ValidTerminalPairs X pairs) :
    RouteTerminalPairs X pairs := by
  refine ⟨fun p hp => ?_, ?_⟩
  · have h1 := h.1 p hp
    exact ⟨h1.1, h1.2.1, h1.2.2, h.disjoint_pair hp⟩
  · have hpw := h.2
    clear h
    induction pairs with
    | nil => exact List.Pairwise.nil
    | cons p rest ih =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.pairwise_cons] at hpw
      rw [List.pairwise_cons]
      refine ⟨fun q hq => ?_, ih hpw.2.2⟩
      have hq1 : q.1 ∈ rest.flatMap fun r => [r.1, r.2] :=
        List.mem_flatMap.mpr ⟨q, hq, by simp⟩
      have hq2 : q.2 ∈ rest.flatMap fun r => [r.1, r.2] :=
        List.mem_flatMap.mpr ⟨q, hq, by simp⟩
      exact Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_right.mpr
          ⟨hpw.1 q.1 (List.mem_cons_of_mem _ hq1), hpw.1 q.2 (List.mem_cons_of_mem _ hq2)⟩,
        Finset.disjoint_union_right.mpr
          ⟨hpw.2.1 q.1 hq1, hpw.2.1 q.2 hq2⟩⟩

/-- Since all terminal sets are pairwise disjoint subsets of `X` and `|A_i| ≤ |B_i|`,
`2 * totalDemand pairs ≤ |X|`. -/
theorem two_mul_totalDemand_le {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    (hvalid : RouteTerminalPairs X pairs) :
    2 * totalDemand pairs ≤ X.card := by
  have h1 : 2 * totalDemand pairs ≤ (pairs.map fun p => (p.1 ∪ p.2).card).sum := by
    unfold totalDemand
    have hmem := hvalid.1
    clear hvalid
    induction pairs with
    | nil => simp
    | cons p rest ih =>
      simp only [List.map_cons, List.sum_cons, Nat.mul_add]
      have hp := hmem p List.mem_cons_self
      have hcard : 2 * p.1.card ≤ (p.1 ∪ p.2).card := by
        rw [Finset.card_union_of_disjoint hp.2.2.2]
        omega
      have hrest := ih fun q hq => hmem q (List.mem_cons_of_mem _ hq)
      omega
  have h2 : (pairs.map fun p => (p.1 ∪ p.2).card).sum ≤ X.card := by
    rw [← card_biUnion_pairs_eq pairs hvalid.2]
    exact Finset.card_le_card (foldr_pairs_subset pairs fun p hp =>
      ⟨(hvalid.1 p hp).1, (hvalid.1 p hp).2.1⟩)
  exact le_trans h1 h2

/-! ### Cut composition and incremental boundary update -/

private lemma sum_map_filter_eq {α : Type*} (l : List α) (p : α → Bool) (f : α → ℕ) :
    ((l.filter p).map f).sum = (l.map fun x => if p x = true then f x else 0).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases h : p a
    · simp [h, ih]
    · simp [h, ih]

/-- Adding a ball `B ⊆ X \ U` to `U` increases `cutIn X` by at most `cutIn (X \ U) B`. -/
theorem cutIn_union_le (H : Graph) {X U B : Finset ℕ} (_hUX : U ⊆ X) (_hB : B ⊆ X \ U) :
    H.cutIn X (U ∪ B) ≤ H.cutIn X U + H.cutIn (X \ U) B := by
  have hfilt : H.inside (X \ U) =
      (H.inside X).filter fun e => decide (e.1 ∈ X \ U) && decide (e.2 ∈ X \ U) := by
    unfold Graph.inside
    rw [List.filter_filter]
    apply List.filter_congr
    intro e _
    by_cases h1 : e.1 ∈ X <;> by_cases h2 : e.2 ∈ X <;>
      by_cases hu1 : e.1 ∈ U <;> by_cases hu2 : e.2 ∈ U <;>
      simp [Finset.mem_sdiff, h1, h2, hu1, hu2]
  rw [cutIn_eq_sum_map, cutIn_eq_sum_map, cutIn_eq_sum_map, hfilt, sum_map_filter_eq,
    ← sum_map_add]
  apply sum_map_le_sum_map
  intro e he
  rw [mem_inside_iff] at he
  by_cases hu1 : e.1 ∈ U <;> by_cases hu2 : e.2 ∈ U <;>
    by_cases hb1 : e.1 ∈ B <;> by_cases hb2 : e.2 ∈ B <;>
    simp [he.2.1, he.2.2, hu1, hu2, hb1, hb2]

/-- Restoring edges incident to `X \ V_act` increases `cutIn X U` by at most `volIn X (X \ V_act)`. -/
theorem cutIn_le_cutIn_restrict_add_volIn (G : Graph) {X V_act U : Finset ℕ} (hVX : V_act ⊆ X) :
    G.cutIn X U ≤ (Graph.mk G.n (G.inside V_act)).cutIn X U + G.volIn X (X \ V_act) := by
  have hres_inside : (Graph.mk G.n (G.inside V_act)).inside X = G.inside V_act := by
    unfold Graph.inside
    rw [List.filter_filter]
    apply List.filter_congr
    intro e _
    by_cases h1 : e.1 ∈ V_act <;> by_cases h2 : e.2 ∈ V_act
    · simp [h1, h2, hVX h1, hVX h2]
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]
  have hfilt : G.inside V_act =
      (G.inside X).filter fun e => decide (e.1 ∈ V_act) && decide (e.2 ∈ V_act) := by
    unfold Graph.inside
    rw [List.filter_filter]
    apply List.filter_congr
    intro e _
    by_cases h1 : e.1 ∈ V_act <;> by_cases h2 : e.2 ∈ V_act
    · simp [h1, h2, hVX h1, hVX h2]
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]
  rw [cutIn_eq_sum_map, cutIn_eq_sum_map, hres_inside, hfilt, sum_map_filter_eq,
    volIn_eq_sum_map, ← sum_map_add]
  apply sum_map_le_sum_map
  intro e he
  rw [mem_inside_iff] at he
  by_cases hv1 : e.1 ∈ V_act <;> by_cases hv2 : e.2 ∈ V_act <;>
    by_cases hu1 : e.1 ∈ U <;> by_cases hu2 : e.2 ∈ U <;>
    simp [he.2.1, he.2.2, hv1, hv2, hu1, hu2]

/-- Incremental cut identity for inserting a single vertex `u ∈ V \ S` into `S`:
the new cut equals `oldCut + outDeg - inDeg`, where `inDeg` and `outDeg` are counted directly
from `adjOf G X u` filtered to `V`. -/
theorem cutIn_insert_add_in_eq (G : Graph) {X V S : Finset ℕ} (hVX : V ⊆ X) (hSV : S ⊆ V)
    {u : ℕ} (huV : u ∈ V) (huS : u ∉ S) :
    G.cutIn V (insert u S) +
      ((adjOf G X u).filter fun p => decide (p.1 ∈ S)).length =
    G.cutIn V S +
      ((adjOf G X u).filter fun p => decide (p.1 ∈ V) && decide (p.1 ∉ insert u S)).length := by
  have hcount : ∀ (P : ℕ → Bool),
      ((adjOf G X u).filter fun p => P p.1).length =
        ((G.inside X).map fun e =>
          (if e.1 = u ∧ P e.2 = true then 1 else 0) +
            (if e.2 = u ∧ P e.1 = true then 1 else 0)).sum := by
    intro P
    rw [← insideEdgesIdx_map_snd]
    unfold adjOf
    rw [List.filter_flatMap, List.length_flatMap, List.map_map]
    congr 1
    apply List.map_congr_left
    intro ie _
    simp only [Function.comp_apply, List.filter_append, List.length_append]
    by_cases h1 : ie.2.1 = u <;> by_cases h2 : ie.2.2 = u
    · simp only [h1, h2, ↓reduceIte, List.filter_cons, List.filter_nil]
      cases P u <;> simp
    · simp only [h1, h2, ↓reduceIte, List.filter_cons, List.filter_nil, List.length_nil]
      cases P ie.2.2 <;> simp
    · simp only [h1, h2, ↓reduceIte, List.filter_cons, List.filter_nil, List.length_nil]
      cases P ie.2.1 <;> simp
    · simp [h1, h2]
  have hV : G.inside V = (G.inside X).filter (insideB V) := by
    unfold Graph.inside insideB
    rw [List.filter_filter]
    apply List.filter_congr
    intro e _
    by_cases h1 : e.1 ∈ V <;> by_cases h2 : e.2 ∈ V
    · simp [h1, h2, hVX h1, hVX h2]
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]
  rw [cutIn_eq_sum_map, cutIn_eq_sum_map, hV, sum_map_filter_eq, sum_map_filter_eq,
    hcount (fun x => decide (x ∈ S)),
    hcount (fun x => decide (x ∈ V) && decide (x ∉ insert u S)),
    ← sum_map_add, ← sum_map_add]
  congr 1
  apply List.map_congr_left
  rintro ⟨a, b⟩ _
  unfold insideB
  dsimp only
  by_cases ha : a = u <;> by_cases hb : b = u
  · subst ha; subst hb
    simp [huV, huS]
  · subst ha
    by_cases h2V : b ∈ V <;> by_cases h2S : b ∈ S
    · simp [huV, huS, h2V, h2S, hb]
    · simp [huV, huS, h2V, h2S, hb]
    · exact False.elim (h2V (hSV h2S))
    · simp [huV, huS, h2V, h2S, hb]
  · subst hb
    by_cases h1V : a ∈ V <;> by_cases h1S : a ∈ S
    · simp [huV, huS, h1V, h1S, ha]
    · simp [huV, huS, h1V, h1S, ha]
    · exact False.elim (h1V (hSV h1S))
    · simp [huV, huS, h1V, h1S, ha]
  · by_cases h1V : a ∈ V <;> by_cases h2V : b ∈ V <;>
      by_cases h1S : a ∈ S <;> by_cases h2S : b ∈ S <;>
      simp [ha, hb, h1V, h2V, h1S, h2S]

end MinCostFlow.ExpanderDecomp
