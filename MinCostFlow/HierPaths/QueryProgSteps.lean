module

public import MinCostFlow.HierPaths.QueryRoute
public import MinCostFlow.HierPaths.Walks

/-!
# The steps of the routing walk

The program of `GetPath` does not build walks as pairs of lists. It writes the steps of the walk
(each edge with the vertex it reaches, `Walk.steps`) into a buffer, one connector walk after the
other, and the loop erasure procedure (`HierPaths/QueryProgEraseProc.lean`) reads them from there.
This file shows that this gives the steps of the walk: the steps of a concatenation are the steps
of its parts (`steps_append`), so the steps of the routing walk `route` are those of the connector
walks it uses, in order (`steps_route`).

The lemma needs the walks to be well formed (`WellFormed`): no edge, or one more vertex than
edges. Walks of a graph are (`IsWalk.wellFormed`), and concatenations and reverses keep it.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

/-- A walk is well formed when it has no edge or one more vertex than edges. -/
def WellFormed (P : Walk) : Prop :=
  P.edges = [] ∨ P.verts.length = P.edges.length + 1

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

public section

theorem wellFormed_empty : WellFormed Walk.empty := Or.inl rfl

theorem IsWalk.wellFormed {G : Graph} {u v : ℕ} {P : Walk} (hP : P.IsWalk G u v) :
    WellFormed P := by
  rcases hP.2.2 with ⟨_, he, _⟩ | ⟨_, hl, _⟩
  · exact Or.inl he
  · exact Or.inr hl

theorem WellFormed.reverse {P : Walk} (h : WellFormed P) : WellFormed P.reverse := by
  rcases h with h | h
  · left; simp [h]
  · right; simp [h]

theorem WellFormed.append {P Q : Walk} (hP : WellFormed P) (hQ : WellFormed Q) :
    WellFormed (P.append Q) := by
  unfold Walk.append
  by_cases h1 : P.edges.isEmpty
  · simp only [h1, ↓reduceIte]; exact hQ
  · by_cases h2 : Q.edges.isEmpty
    · simp only [h1, h2, ↓reduceIte, Bool.false_eq_true]; exact hP
    · simp only [h1, h2, ↓reduceIte, Bool.false_eq_true]
      have hP' : P.verts.length = P.edges.length + 1 :=
        hP.resolve_left (by simpa using h1)
      have hQ' : Q.verts.length = Q.edges.length + 1 :=
        hQ.resolve_left (by simpa using h2)
      right
      simp only [List.length_append, List.length_tail]
      omega

/-- The steps of a concatenation are the steps of its parts. -/
theorem steps_append {P : Walk} (hP : WellFormed P) (Q : Walk) :
    Walk.steps (P.append Q) = Walk.steps P ++ Walk.steps Q := by
  unfold Walk.append
  by_cases h1 : P.edges.isEmpty
  · have : P.edges = [] := by simpa using h1
    simp [Walk.steps, this]
  · by_cases h2 : Q.edges.isEmpty
    · have : Q.edges = [] := by simpa using h2
      simp [h1, Walk.steps, this]
    · simp only [h1, h2, ↓reduceIte, Bool.false_eq_true]
      have hP' : P.verts.length = P.edges.length + 1 :=
        hP.resolve_left (by simpa using h1)
      obtain ⟨x, t, hx⟩ : ∃ x t, P.verts = x :: t := by
        cases hv : P.verts with
        | nil => rw [hv] at hP'; simp at hP'
        | cons x t => exact ⟨x, t, rfl⟩
      unfold Walk.steps
      simp only [hx, List.cons_append, List.tail_cons]
      rw [List.zip_append]
      rw [hx] at hP'
      simp at hP'
      omega

namespace ConnectorSystem

variable (C : ConnectorSystem) (grp : ℕ → ℕ → ℕ) (pick : ℕ → ℕ → ℕ → ℕ)

/-- The routing walk is well formed when the connector walks it may use are. -/
theorem wellFormed_route (hC : ∀ j u v, WellFormed (C.walk (pickFor grp pick j u v))) :
    ∀ k j u v, WellFormed (C.route grp pick k j u v)
  | 0, _, _, _ => wellFormed_empty
  | k + 1, j, u, v => by
    unfold route
    split_ifs
    · exact wellFormed_empty
    · exact wellFormed_route hC k (j + 1) u v
    · have hcw : WellFormed (C.connWalk grp pick j u v) := by
        unfold connWalk
        split_ifs
        · exact hC _ _ _
        · exact (hC _ _ _).reverse
      exact (wellFormed_route hC k _ _ _).append (hcw.append (wellFormed_route hC k _ _ _))

/-- The steps of the routing walk: those of the first half, of the connector, and of the
second half. -/
theorem steps_route (hC : ∀ j u v, WellFormed (C.walk (pickFor grp pick j u v))) (k j u v : ℕ) :
    Walk.steps (C.route grp pick (k + 1) j u v) =
      if u = v then []
      else if grp (j + 1) u = grp (j + 1) v then Walk.steps (C.route grp pick k (j + 1) u v)
      else Walk.steps (C.route grp pick k (j + 1) u (C.connFrom grp pick j u v)) ++
        (Walk.steps (C.connWalk grp pick j u v) ++
          Walk.steps (C.route grp pick k (j + 1) (C.connTo grp pick j u v) v)) := by
  have hcw : WellFormed (C.connWalk grp pick j u v) := by
    unfold connWalk
    split_ifs
    · exact hC _ _ _
    · exact (hC _ _ _).reverse
  conv_lhs => unfold route
  split_ifs
  · simp [Walk.steps, Walk.empty]
  · rfl
  · rw [steps_append (C.wellFormed_route grp pick hC k _ _ _), steps_append hcw]

/-- Every connector visited by the route is in the connector table. -/
@[expose] def RouteReady :
    ℕ → ℕ → ℕ → ℕ → Prop
  | 0, _, _, _ => True
  | k + 1, j, u, v =>
    if u = v then True
    else if grp (j + 1) u = grp (j + 1) v then RouteReady k (j + 1) u v
    else pickFor grp pick j u v < C.numConn ∧
      RouteReady k (j + 1) u (C.connFrom grp pick j u v) ∧
      RouteReady k (j + 1) (C.connTo grp pick j u v) v

/-- A valid choice keeps all recursive calls on surviving terminals within one group. -/
theorem routeReady_of_choice {surv : Finset ℕ} (hchoice : C.IsConnectorChoice grp pick surv) :
    ∀ k j u v, u ∈ surv → v ∈ surv → grp j u = grp j v → C.RouteReady grp pick k j u v
  | 0, _, _, _, _, _, _ => trivial
  | k + 1, j, u, v, hu, hv, hgroup => by
    by_cases heq : u = v
    · simp [RouteReady, heq]
    by_cases hchild : grp (j + 1) u = grp (j + 1) v
    · simpa only [RouteReady, heq, hchild, ↓reduceIte] using
        routeReady_of_choice hchoice k (j + 1) u v hu hv hchild
    obtain ⟨hel, hside⟩ := hchoice j u v hu hv hgroup hchild
    simp only [RouteReady, heq, hchild, ↓reduceIte]
    refine ⟨hel.1, ?_⟩
    rcases hside with h | h
    · simp only [connFrom, connTo, fwd, pickFor, h.1, ↓reduceIte]
      exact ⟨routeReady_of_choice hchoice k _ _ _ hu hel.2.1 h.1.symm,
        routeReady_of_choice hchoice k _ _ _ hel.2.2 hv h.2⟩
    · have hrev : grp (j + 1) (C.endA (pickFor grp pick j u v)) ≠ grp (j + 1) u :=
        fun hf => hchild (hf.symm.trans h.2)
      simp only [connFrom, connTo, fwd, hrev, ↓reduceIte]
      exact ⟨routeReady_of_choice hchoice k _ _ _ hu hel.2.2 h.1.symm,
        routeReady_of_choice hchoice k _ _ _ hel.2.1 hv h.2⟩

/-- A route whose connector reads are in bounds is well formed if its stored walks are. -/
theorem wellFormed_route_ready (hC : ∀ c < C.numConn, WellFormed (C.walk c)) :
    ∀ k j u v, C.RouteReady grp pick k j u v → WellFormed (C.route grp pick k j u v)
  | 0, _, _, _, _ => wellFormed_empty
  | k + 1, j, u, v, h => by
    by_cases heq : u = v
    · simp [route, heq, wellFormed_empty]
    by_cases hchild : grp (j + 1) u = grp (j + 1) v
    · simp only [RouteReady, heq, hchild, ↓reduceIte] at h
      simpa only [route, heq, hchild, ↓reduceIte] using wellFormed_route_ready hC k _ _ _ h
    simp only [RouteReady, heq, hchild, ↓reduceIte] at h
    have hWalk : WellFormed (C.connWalk grp pick j u v) := by
      unfold connWalk
      split_ifs
      · exact hC _ h.1
      · exact (hC _ h.1).reverse
    simp only [route, heq, hchild, ↓reduceIte]
    exact (wellFormed_route_ready hC k _ _ _ h.2.1).append
      (hWalk.append (wellFormed_route_ready hC k _ _ _ h.2.2))

/-- Split the steps of an in-bounds route into the steps written by its program. -/
theorem steps_route_ready (hC : ∀ c < C.numConn, WellFormed (C.walk c)) (k j u v : ℕ)
    (h : C.RouteReady grp pick (k + 1) j u v) :
    Walk.steps (C.route grp pick (k + 1) j u v) =
      if u = v then []
      else if grp (j + 1) u = grp (j + 1) v then Walk.steps (C.route grp pick k (j + 1) u v)
      else Walk.steps (C.route grp pick k (j + 1) u (C.connFrom grp pick j u v)) ++
        (Walk.steps (C.connWalk grp pick j u v) ++
          Walk.steps (C.route grp pick k (j + 1) (C.connTo grp pick j u v) v)) := by
  conv_lhs => unfold route
  split_ifs with heq hchild
  · simp [Walk.steps, Walk.empty]
  · rfl
  · simp only [RouteReady, heq, hchild, ↓reduceIte] at h
    have hWalk : WellFormed (C.connWalk grp pick j u v) := by
      unfold connWalk
      split_ifs
      · exact hC _ h.1
      · exact (hC _ h.1).reverse
    rw [steps_append (C.wellFormed_route_ready grp pick hC k _ _ _ h.2.1), steps_append hWalk]

end ConnectorSystem

end

end MinCostFlow.HierPaths
