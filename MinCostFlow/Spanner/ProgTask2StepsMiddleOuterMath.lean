module

public import MinCostFlow.Spanner.ProgTask2StepsMiddleVerts
public import MinCostFlow.Spanner.ProgTask2StepsMiddleInner

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Pure fold and composition-vertex lemmas for `t2MiddleEdgeBody` -/

lemma t2_isWalk_verts_length_le {H : Graph} {u v : ℕ} {P : Walk}
    (hP : P.IsWalk H u v) : P.verts.length ≤ P.edges.length + 1 := by
  rcases hP with ⟨_, _, ⟨hv, _, _⟩ | ⟨_, hlen, _⟩⟩
  · simp [hv]
  · simp [hlen]

lemma t2_composeAux_mem_verts_iff {B C : Graph} {embBC : ℕ → Walk}
    (hBC : IsEmbedding B C embBC) :
    ∀ (js vs : List ℕ) (u v : ℕ),
      vs.length = js.length + 1 → vs.head? = some u → vs.getLast? = some v →
      (∀ j ∈ js, j < B.m) →
      (∀ i : ℕ, i < js.length →
        Walk.EdgeMatches (B.edges.getD (js.getD i 0) (0, 0)) (vs.getD i 0) (vs.getD (i + 1) 0)) →
      v < B.n →
      ∀ x, x ∈ (composeAux B embBC vs js).verts ↔ ∃ j ∈ js, x ∈ (embBC j).verts := by
  intro js
  induction js with
  | nil =>
    intro vs u v hlen _ _ _ _ _ x
    cases vs with
    | nil => simp at hlen
    | cons a vs' =>
      cases vs' <;> simp at hlen ⊢
      simp [composeAux, Walk.empty]
  | cons j js ih =>
    intro vs u v hlen hhead hlast hedges hstep hv x
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
        have hBe : B.edges.getD j (0, 0) = B.edges[j]'hjB := List.getD_eq_getElem _ _ hjB
        have hj_walk := hBC.2 j hjB
        have hstep_walk : (if (B.edges.getD j (0, 0)).1 = u ∧ (B.edges.getD j (0, 0)).2 = b then
            embBC j else (embBC j).reverse).IsWalk C u b := by
          rw [hBe] at hstep0 ⊢
          rcases hstep0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · simp only [h1, h2, and_self, ↓reduceIte]
            simpa [h1, h2] using hj_walk
          · split_ifs with hcond
            · rw [hcond.1, hcond.2] at hj_walk; exact hj_walk
            · rw [← h1, ← h2]; exact Walk.isWalk_reverse hj_walk
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
          composeAux_isWalk hBC js (b :: vs'') b v hlen' rfl hlast' hedges' hstep' hv
        have hiff_app := Walk.mem_verts_append_iff hstep_walk htail_walk x
        have hiff_tail := ih (b :: vs'') b v hlen' rfl hlast' hedges' hstep' hv x
        have hstep_verts : x ∈ (if (B.edges.getD j (0, 0)).1 = u ∧ (B.edges.getD j (0, 0)).2 = b then
            embBC j else (embBC j).reverse).verts ↔ x ∈ (embBC j).verts := by
          split_ifs <;> simp [Walk.reverse]
        dsimp only [composeAux] at hiff_app ⊢
        rw [hiff_app, hstep_verts, hiff_tail]
        simp [List.mem_cons]

lemma t2_compose_partial_mem_verts_iff {H' J : Graph} {embJH : ℕ → Walk}
    (hJH : IsEmbedding J H' embJH) {emb' : ℕ → Option Walk} {eW u v : ℕ} {P_J : Walk}
    (hemb : emb' eW = some P_J) (hPJ : P_J.IsWalk J u v) (x : ℕ) :
    x ∈ (compose J embJH (partialToWalk emb') eW).verts ↔
      ∃ j ∈ P_J.edges, x ∈ (embJH j).verts := by
  have hpw : partialToWalk emb' eW = P_J := by simp [partialToWalk, hemb]
  unfold compose
  rw [hpw]
  rcases hPJ with ⟨hu, hv, ⟨hPv, hPe, _⟩ | ⟨_, hlen, hhead, hlast, hedges, hstep⟩⟩
  · rw [hPv, hPe]; simp [composeAux, Walk.empty]
  · exact t2_composeAux_mem_verts_iff hJH P_J.edges P_J.verts u v hlen hhead hlast hedges hstep hv x

noncomputable def t2MiddleOuterFold (embJH : ℕ → Walk) (procVerts : Finset ℕ)
    (vcong0 : ℕ → ℕ) (thresh wVal : ℕ) (jSubOrigEdges edges : List ℕ) (k : ℕ) :
    Finset ℕ × List ℕ :=
  (List.range k).foldl (fun p idx =>
    let eL_edge := edges.getD idx 0
    let eJ := jSubOrigEdges.getD eL_edge 0
    t2MiddleInnerFold embJH procVerts vcong0 thresh wVal eJ (embJH eJ).verts.length p) (∅, [])

lemma t2MiddleOuterFold_step {embJH : ℕ → Walk} {procVerts : Finset ℕ}
    {vcong0 : ℕ → ℕ} {thresh wVal : ℕ} {jSubOrigEdges edges : List ℕ} {k : ℕ} :
    t2MiddleOuterFold embJH procVerts vcong0 thresh wVal jSubOrigEdges edges (k + 1) =
      let p := t2MiddleOuterFold embJH procVerts vcong0 thresh wVal jSubOrigEdges edges k
      let eL_edge := edges.getD k 0
      let eJ := jSubOrigEdges.getD eL_edge 0
      t2MiddleInnerFold embJH procVerts vcong0 thresh wVal eJ (embJH eJ).verts.length p := by
  simp [t2MiddleOuterFold, List.range_succ, List.foldl_append]

def t2MiddleUpdVerts (embJH : ℕ → Walk) (jSubOrigEdges edges : List ℕ) (k : ℕ) : ℕ :=
  (List.range k).foldl (fun acc idx =>
    let eL_edge := edges.getD idx 0
    let eJ := jSubOrigEdges.getD eL_edge 0
    acc + (embJH eJ).verts.length) 0

lemma t2MiddleUpdVerts_step {embJH : ℕ → Walk} {jSubOrigEdges edges : List ℕ} {k : ℕ} :
    t2MiddleUpdVerts embJH jSubOrigEdges edges (k + 1) =
      t2MiddleUpdVerts embJH jSubOrigEdges edges k +
        (embJH (jSubOrigEdges.getD (edges.getD k 0) 0)).verts.length := by
  simp [t2MiddleUpdVerts, List.range_succ, List.foldl_append]

lemma t2MiddleUpdVerts_le {J H' : Graph} {embJH : ℕ → Walk}
    (hJH : IsEmbedding J H' embJH)
    {jSubOrigEdges edges : List ℕ}
    (h_orig : ∀ k < edges.length, jSubOrigEdges.getD (edges.getD k 0) 0 < J.m) :
    ∀ k ≤ edges.length, t2MiddleUpdVerts embJH jSubOrigEdges edges k ≤ k * (length J embJH + 1) := by
  intro k
  induction k with
  | zero => intro _; simp [t2MiddleUpdVerts]
  | succ k ih =>
    intro hk
    have hk_lt : k < edges.length := hk
    have heJ := h_orig k hk_lt
    have he_len := edges_length_le_length embJH heJ
    have hv_len : (embJH (jSubOrigEdges.getD (edges.getD k 0) 0)).verts.length ≤
        (embJH (jSubOrigEdges.getD (edges.getD k 0) 0)).edges.length + 1 :=
      t2_isWalk_verts_length_le (hJH.2 _ heJ)
    calc t2MiddleUpdVerts embJH jSubOrigEdges edges (k + 1)
        = t2MiddleUpdVerts embJH jSubOrigEdges edges k + _ := t2MiddleUpdVerts_step
      _ ≤ k * (length J embJH + 1) + (length J embJH + 1) :=
        Nat.add_le_add (ih (Nat.le_of_lt hk_lt)) (by omega)
      _ = (k + 1) * (length J embJH + 1) := by rw [Nat.add_mul, Nat.one_mul]

end MinCostFlow.Spanner
