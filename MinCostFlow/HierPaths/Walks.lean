module

public import MinCostFlow.Spanner.Embedding

/-!
# Walks as lists of steps

The query of the path data structure builds walks of the input graph by joining stored walks,
reversing them, and taking prefixes. A `Spanner.Walk` stores its vertices and its edge numbers in
two lists, and `Spanner.Walk.IsWalk` speaks about them by index. That is awkward for induction.

This file gives a second view. A walk that starts at `u` is a list of *steps* `(e, y)`: cross edge
number `e` and arrive at `y`. The predicate `StepChain G x l` says that each step uses an edge of
`G` that joins the current vertex to the next one. The walk `ofSteps u l` has the vertices
`u :: l.map Prod.snd` and the edges `l.map Prod.fst`, and `isWalk_ofSteps_iff` shows that it is a
walk from `u` to the end of `l` exactly when `l` is a step chain. Every walk with edges has this
form (`eq_ofSteps`).

With this view we prove the facts the query needs: the vertices and edges of a concatenation and
of a reversal (the `IsWalk` facts themselves are `Spanner.Walk.isWalk_append` and
`Spanner.Walk.isWalk_reverse`), and prefix walks (`isWalk_prefix`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

/-- Each step `(e, y)` of `l`, starting at `x`, crosses an edge `e` of `G` that joins the current
vertex to `y`. -/
def StepChain (G : Graph) : ℕ → List (ℕ × ℕ) → Prop
  | _, [] => True
  | x, p :: l => p.1 < G.m ∧ Walk.EdgeMatches (G.edges.getD p.1 (0, 0)) x p.2 ∧ StepChain G p.2 l

/-- The vertex reached after the steps `l`, starting at `x`. -/
def stepsEnd : ℕ → List (ℕ × ℕ) → ℕ
  | x, [] => x
  | _, p :: l => stepsEnd p.2 l

/-- The walk from `u` with the steps `l`. With no steps it is the empty walk. -/
def ofSteps (u : ℕ) (l : List (ℕ × ℕ)) : Walk :=
  if l = [] then Walk.empty else ⟨u :: l.map Prod.snd, l.map Prod.fst⟩

/-- The steps of a walk: each edge number with the vertex reached by it. -/
def Walk.steps (P : Walk) : List (ℕ × ℕ) :=
  P.edges.zip P.verts.tail

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

public section

@[simp] theorem stepChain_nil (G : Graph) (x : ℕ) : StepChain G x [] := trivial

@[simp] theorem stepChain_cons (G : Graph) (x : ℕ) (p : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    StepChain G x (p :: l) ↔
      p.1 < G.m ∧ Walk.EdgeMatches (G.edges.getD p.1 (0, 0)) x p.2 ∧ StepChain G p.2 l :=
  Iff.rfl

@[simp] theorem stepsEnd_nil (x : ℕ) : stepsEnd x [] = x := rfl

@[simp] theorem stepsEnd_cons (x : ℕ) (p : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    stepsEnd x (p :: l) = stepsEnd p.2 l := rfl

/-- The last vertex of `x :: l.map Prod.snd` is the end of the steps `l`. -/
theorem getLast?_cons_map_snd (x : ℕ) (l : List (ℕ × ℕ)) :
    (x :: l.map Prod.snd).getLast? = some (stepsEnd x l) := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih => rw [List.map_cons, List.getLast?_cons_cons, ih]; rfl

theorem stepsEnd_append (x : ℕ) (l₁ l₂ : List (ℕ × ℕ)) :
    stepsEnd x (l₁ ++ l₂) = stepsEnd (stepsEnd x l₁) l₂ := by
  induction l₁ generalizing x with
  | nil => rfl
  | cons p l ih => simp [ih]

theorem stepChain_append (G : Graph) (x : ℕ) (l₁ l₂ : List (ℕ × ℕ)) :
    StepChain G x (l₁ ++ l₂) ↔ StepChain G x l₁ ∧ StepChain G (stepsEnd x l₁) l₂ := by
  induction l₁ generalizing x with
  | nil => simp
  | cons p l ih => simp [ih, and_assoc]

/-- A step chain stays a step chain after dropping steps at its end. -/
theorem StepChain.take {G : Graph} {x : ℕ} {l : List (ℕ × ℕ)} (h : StepChain G x l) (k : ℕ) :
    StepChain G x (l.take k) := by
  have h' := h
  rw [← List.take_append_drop k l, stepChain_append] at h'
  exact h'.1

/-- The end of a nonempty list of steps is the vertex of its last step. -/
theorem stepsEnd_of_ne_nil {x : ℕ} {l : List (ℕ × ℕ)} (hl : l ≠ []) :
    stepsEnd x l = (l.getLast hl).2 := by
  induction l generalizing x with
  | nil => exact (hl rfl).elim
  | cons p l ih =>
    cases l with
    | nil => rfl
    | cons q l => rw [stepsEnd_cons, ih (List.cons_ne_nil _ _), List.getLast_cons_cons]

/-- The index form of the step condition of `IsWalk`, for the walk `ofSteps u l`. -/
private theorem stepChain_iff_index (G : Graph) (u : ℕ) (l : List (ℕ × ℕ)) :
    StepChain G u l ↔ (∀ j ∈ l.map Prod.fst, j < G.m) ∧
      ∀ i : ℕ, i < (l.map Prod.fst).length →
        Walk.EdgeMatches (G.edges.getD ((l.map Prod.fst).getD i 0) (0, 0))
          ((u :: l.map Prod.snd).getD i 0) ((u :: l.map Prod.snd).getD (i + 1) 0) := by
  induction l generalizing u with
  | nil => simp
  | cons p l ih =>
    rw [stepChain_cons, ih]
    constructor
    · rintro ⟨hp, hm, hl, hi⟩
      refine ⟨?_, ?_⟩
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hp
        · exact hl j hj
      · intro i hil
        cases i with
        | zero => simpa using hm
        | succ i =>
          have := hi i (by simp at hil ⊢; omega)
          simpa using this
    · rintro ⟨hl, hi⟩
      refine ⟨hl _ (by simp), by simpa using hi 0 (by simp), fun j hj => hl j (by simp [hj]),
        fun i hil => ?_⟩
      have := hi (i + 1) (by simpa using hil)
      simpa using this

/-- The walk `ofSteps u l`, for a nonempty `l`, is a walk from `u` to `v` exactly when `u` and `v`
are vertices, `l` is a step chain from `u`, and `l` ends at `v`. -/
theorem isWalk_ofSteps_iff {G : Graph} {u v : ℕ} {l : List (ℕ × ℕ)} (hl : l ≠ []) :
    (ofSteps u l).IsWalk G u v ↔ u < G.n ∧ v < G.n ∧ StepChain G u l ∧ stepsEnd u l = v := by
  have hl' : l.map Prod.fst ≠ [] := by simpa using hl
  simp only [ofSteps, hl, ite_false, Walk.IsWalk, stepChain_iff_index]
  constructor
  · rintro ⟨hu, hv, ⟨_, he, _⟩ | ⟨_, _, _, hlast, hedges, hstep⟩⟩
    · exact (hl' he).elim
    · refine ⟨hu, hv, ⟨hedges, hstep⟩, ?_⟩
      rw [getLast?_cons_map_snd] at hlast
      exact Option.some.inj hlast
  · rintro ⟨hu, hv, ⟨hedges, hstep⟩, hend⟩
    refine ⟨hu, hv, Or.inr ⟨hl', by simp, by simp, ?_, hedges, hstep⟩⟩
    rw [getLast?_cons_map_snd, hend]

/-- Every walk with at least one edge is `ofSteps` of its steps. -/
theorem eq_ofSteps {G : Graph} {u v : ℕ} {P : Walk} (hP : P.IsWalk G u v) (he : P.edges ≠ []) :
    P = ofSteps u (Walk.steps P) := by
  rcases hP with ⟨_, _, ⟨_, hPe, _⟩ | ⟨_, hlen, hhead, _, _, _⟩⟩
  · exact (he hPe).elim
  · obtain ⟨vs, es⟩ := P
    cases vs with
    | nil => simp at hhead
    | cons a t =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hne : es.zip t ≠ [] := by
        intro h
        rw [List.zip_eq_nil_iff] at h
        rcases h with h | h
        · exact he h
        · subst h; exact he (List.length_eq_zero_iff.mp hlen.symm)
      simp only [ofSteps, Walk.steps, List.tail_cons, hne, ite_false]
      rw [List.map_snd_zip (by omega), List.map_fst_zip (by omega)]

/-- A walk with at least one edge is `ofSteps` of a nonempty step chain that ends at its last
vertex. -/
theorem isWalk_steps {G : Graph} {u v : ℕ} {P : Walk} (hP : P.IsWalk G u v) (he : P.edges ≠ []) :
    Walk.steps P ≠ [] ∧ StepChain G u (Walk.steps P) ∧ stepsEnd u (Walk.steps P) = v := by
  have heq := eq_ofSteps hP he
  have hne : Walk.steps P ≠ [] := by
    intro h
    rw [h] at heq
    simp only [ofSteps, ↓reduceIte] at heq
    exact he (by rw [heq]; rfl)
  rw [heq] at hP
  obtain ⟨_, _, hc, hend⟩ := (isWalk_ofSteps_iff hne).mp hP
  exact ⟨hne, hc, hend⟩

/-- The vertices of `ofSteps u l`, for a nonempty `l`. -/
theorem verts_ofSteps {u : ℕ} {l : List (ℕ × ℕ)} (hl : l ≠ []) :
    (ofSteps u l).verts = u :: l.map Prod.snd := by
  simp [ofSteps, hl]

@[simp] theorem edges_ofSteps (u : ℕ) (l : List (ℕ × ℕ)) :
    (ofSteps u l).edges = l.map Prod.fst := by
  by_cases hl : l = []
  · simp [ofSteps, hl, Walk.empty]
  · simp [ofSteps, hl]

/-! ### Concatenation and reversal -/

@[simp] theorem edges_reverse (P : Walk) : P.reverse.edges = P.edges.reverse := rfl

@[simp] theorem verts_reverse (P : Walk) : P.reverse.verts = P.verts.reverse := rfl

/-- The edges of a concatenation are the edges of the two parts. -/
theorem edges_append (P Q : Walk) : (P.append Q).edges = P.edges ++ Q.edges :=
  Walk.edges_append P Q

/-- A vertex of a concatenation is a vertex of one of the parts. -/
theorem mem_verts_append {P Q : Walk} {x : ℕ} (hx : x ∈ (P.append Q).verts) :
    x ∈ P.verts ∨ x ∈ Q.verts :=
  Walk.mem_verts_append_left hx

/-- A concatenation has as many edges as its two parts together. -/
theorem length_edges_append (P Q : Walk) :
    (P.append Q).edges.length = P.edges.length + Q.edges.length := by
  rw [edges_append, List.length_append]

/-! ### Prefixes -/

/-- The prefix of the walk `P` that stops at its vertex number `k`, written with steps. -/
def Walk.prefix (P : Walk) (k : ℕ) : Walk :=
  ofSteps (P.verts.headD 0) ((Walk.steps P).take k)

/-- The definition of `Walk.prefix`, for use in other files. -/
theorem Walk.prefix_eq (P : Walk) (k : ℕ) :
    Walk.prefix P k = ofSteps (P.verts.headD 0) ((Walk.steps P).take k) := by
  rw [Walk.prefix]

/-- The prefix of a walk up to its vertex number `k` is a walk from the start to that vertex. -/
theorem isWalk_prefix {G : Graph} {u v : ℕ} {P : Walk} (hG : G.IsValid) (hP : P.IsWalk G u v)
    {k : ℕ} (hk : k < P.verts.length) : (Walk.prefix P k).IsWalk G u (P.verts.getD k 0) := by
  have hu : u < G.n := hP.1
  by_cases he : P.edges = []
  · rcases hP with ⟨_, _, ⟨hv, _, _⟩ | ⟨hne, _⟩⟩
    · simp [hv] at hk
    · exact (hne he).elim
  · obtain ⟨hne, hc, _⟩ := isWalk_steps hP he
    have heq := eq_ofSteps hP he
    have hverts : P.verts = u :: (Walk.steps P).map Prod.snd := by
      conv_lhs => rw [heq]
      exact verts_ofSteps hne
    have hhead : P.verts.headD 0 = u := by rw [hverts]; rfl
    have hlt : ∀ x ∈ P.verts, x < G.n := Walk.isWalk_verts_lt hG hP
    unfold Walk.prefix
    rw [hhead]
    cases k with
    | zero =>
      have h0 : P.verts.getD 0 0 = u := by rw [hverts]; rfl
      rw [h0, List.take_zero]
      exact ⟨hu, hu, Or.inl ⟨rfl, rfl, rfl⟩⟩
    | succ k =>
      have hk' : k < (Walk.steps P).length := by
        rw [hverts] at hk; simpa using hk
      have htk : (Walk.steps P).take (k + 1) ≠ [] := by
        simp [List.take_eq_nil_iff, hne]
      have hx : P.verts.getD (k + 1) 0 ∈ P.verts :=
        List.getD_eq_getElem _ _ hk ▸ List.getElem_mem hk
      refine (isWalk_ofSteps_iff htk).mpr ⟨hu, hlt _ hx, hc.take _, ?_⟩
      rw [stepsEnd_of_ne_nil htk, hverts, List.getLast_take]
      simp [List.getD_eq_getElem?_getD, hk']

/-- The edges of a prefix are among the edges of the walk. -/
theorem edges_prefix_subset (P : Walk) (k : ℕ) :
    ∀ e ∈ (Walk.prefix P k).edges, e ∈ P.edges := by
  intro e he
  rw [Walk.prefix, edges_ofSteps] at he
  have hsub : (Walk.steps P).take k ⊆ Walk.steps P := List.take_subset _ _
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
  exact List.of_mem_zip (hsub hp) |>.1

/-- The vertices of a prefix are among the vertices of the walk. -/
theorem verts_prefix_subset {P : Walk} (k : ℕ) :
    ∀ x ∈ (Walk.prefix P k).verts, x ∈ P.verts := by
  intro x hx
  unfold Walk.prefix ofSteps at hx
  split_ifs at hx with hl
  · simp [Walk.empty] at hx
  · rcases List.mem_cons.mp hx with rfl | hx
    · cases h : P.verts with
      | nil => simp [Walk.steps, h] at hl
      | cons a t => simp
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact List.mem_of_mem_tail (List.of_mem_zip (List.take_subset _ _ hp)).2

/-- A prefix has at most as many edges as the walk. -/
theorem length_edges_prefix_le (P : Walk) (k : ℕ) :
    (Walk.prefix P k).edges.length ≤ P.edges.length := by
  rw [Walk.prefix, edges_ofSteps, List.length_map, List.length_take, Walk.steps,
    List.length_zip]
  omega

end

end MinCostFlow.HierPaths
