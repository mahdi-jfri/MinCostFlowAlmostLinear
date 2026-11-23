module

public import MinCostFlow.HierPaths.Live

/-!
# Routing between surviving terminals

The terminals are split into nested groups. Here a hierarchy is given by a group index
`grp j u`, the group of terminal `u` at depth `j`; at the leaf depth `L` the groups are single
terminals. The query joins two surviving terminals `u` and `v` of one group at depth `j`: if
`u = v` there is nothing to do; if they lie in the same child, recurse
there; otherwise take an eligible connector `a b` between their two children, and join the
recursive walk from `u` to `a`, the connector walk from `a` to `b`, and the recursive walk from
`b` to `v`.

The connector comes from a *connector choice* `pick j Y Z`, for the children `Y` and `Z` at depth
`j + 1`. The hypothesis `IsConnectorChoice` asks what `exists_surviving_matching_edge` gives: when `Y ≠ Z` are the
children of one group that hold surviving terminals `u` and `v`, the picked connector is eligible
and has one endpoint in `Y` and one in `Z`.

The recursion is `route`, on the height `k = L - j`. The main result is `route_spec`: for
surviving `u`, `v` in one group at depth `j`, `route` is a walk from the owner of `u` to the owner
of `v` that uses no deleted edge and only live vertices, with at most `2 ^ k - 1` connectors
(`routeCount_le`) and at most `(2 ^ k - 1) · λ` edges when each connector walk has at most `λ`
edges. `routeOps_le` bounds its step count by `2 ^ k · (λ + 3)`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

/-- The connector between the children of `u` and `v` at depth `j + 1`. -/
def pickFor (grp : ℕ → ℕ → ℕ) (pick : ℕ → ℕ → ℕ → ℕ) (j u v : ℕ) : ℕ :=
  pick j (grp (j + 1) u) (grp (j + 1) v)

namespace ConnectorSystem

variable (C : ConnectorSystem) (grp : ℕ → ℕ → ℕ) (pick : ℕ → ℕ → ℕ → ℕ)

/-- The connector choice is valid for the surviving terminals `surv`: whenever two surviving
terminals `u` and `v` lie in one group at depth `j` but in different children `Y` and `Z`, the
connector `pick j Y Z` is eligible and has one endpoint in `Y` and the other in `Z`. -/
def IsConnectorChoice (surv : Finset ℕ) : Prop :=
  ∀ j u v, u ∈ surv → v ∈ surv → grp j u = grp j v → grp (j + 1) u ≠ grp (j + 1) v →
    C.Eligible surv (pick j (grp (j + 1) u) (grp (j + 1) v)) ∧
      ((grp (j + 1) (C.endA (pick j (grp (j + 1) u) (grp (j + 1) v))) = grp (j + 1) u ∧
        grp (j + 1) (C.endB (pick j (grp (j + 1) u) (grp (j + 1) v))) = grp (j + 1) v) ∨
       (grp (j + 1) (C.endB (pick j (grp (j + 1) u) (grp (j + 1) v))) = grp (j + 1) u ∧
        grp (j + 1) (C.endA (pick j (grp (j + 1) u) (grp (j + 1) v))) = grp (j + 1) v))

/-- Whether the connector is used in its stored direction: its first endpoint lies in the child
of `u`. -/
def fwd (j u v : ℕ) : Prop :=
  grp (j + 1) (C.endA (pickFor grp pick j u v)) = grp (j + 1) u

instance (j u v : ℕ) : Decidable (C.fwd grp pick j u v) := by
  unfold fwd; infer_instance

/-- The endpoint of the connector in the child of `u`. -/
def connFrom (j u v : ℕ) : ℕ :=
  if C.fwd grp pick j u v then C.endA (pickFor grp pick j u v) else C.endB (pickFor grp pick j u v)

/-- The endpoint of the connector in the child of `v`. -/
def connTo (j u v : ℕ) : ℕ :=
  if C.fwd grp pick j u v then C.endB (pickFor grp pick j u v) else C.endA (pickFor grp pick j u v)

/-- The walk of the connector, oriented from the child of `u` to the child of `v`. -/
def connWalk (j u v : ℕ) : Walk :=
  if C.fwd grp pick j u v then C.walk (pickFor grp pick j u v)
  else (C.walk (pickFor grp pick j u v)).reverse

/-- The routing recursion at height `k` and depth `j`. -/
def route : ℕ → ℕ → ℕ → ℕ → Walk
  | 0, _, _, _ => Walk.empty
  | k + 1, j, u, v =>
    if u = v then Walk.empty
    else if grp (j + 1) u = grp (j + 1) v then route k (j + 1) u v
    else (route k (j + 1) u (C.connFrom grp pick j u v)).append
      ((C.connWalk grp pick j u v).append (route k (j + 1) (C.connTo grp pick j u v) v))

/-- The number of connectors that `route` uses. -/
def routeCount : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | k + 1, j, u, v =>
    if u = v then 0
    else if grp (j + 1) u = grp (j + 1) v then routeCount k (j + 1) u v
    else routeCount k (j + 1) u (C.connFrom grp pick j u v) + 1 +
      routeCount k (j + 1) (C.connTo grp pick j u v) v

/-- The step count of `route`: one per call, and for each connector one step per edge of its walk
and one more, to copy the walk into the output buffer. -/
def routeOps : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 1
  | k + 1, j, u, v =>
    if u = v then 1
    else if grp (j + 1) u = grp (j + 1) v then 1 + routeOps k (j + 1) u v
    else 1 + routeOps k (j + 1) u (C.connFrom grp pick j u v) +
      ((C.connWalk grp pick j u v).edges.length + 1) +
      routeOps k (j + 1) (C.connTo grp pick j u v) v

end ConnectorSystem

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

namespace ConnectorSystem

variable (C : ConnectorSystem) (grp : ℕ → ℕ → ℕ) (pick : ℕ → ℕ → ℕ → ℕ)

/-- The facts about the oriented connector that the recursion uses. -/
private theorem conn_spec {G : Graph} (hfit : C.FitsGraph G) {surv : Finset ℕ}
    (hpick : C.IsConnectorChoice grp pick surv) {j u v : ℕ} (hu : u ∈ surv) (hv : v ∈ surv)
    (huv : grp j u = grp j v) (hne : grp (j + 1) u ≠ grp (j + 1) v) :
    C.Eligible surv (pickFor grp pick j u v) ∧
      C.connFrom grp pick j u v ∈ surv ∧ C.connTo grp pick j u v ∈ surv ∧
      grp (j + 1) u = grp (j + 1) (C.connFrom grp pick j u v) ∧
      grp (j + 1) (C.connTo grp pick j u v) = grp (j + 1) v ∧
      (C.connWalk grp pick j u v).IsWalk G (C.owner (C.connFrom grp pick j u v))
        (C.owner (C.connTo grp pick j u v)) ∧
      (∀ e ∈ (C.connWalk grp pick j u v).edges, e ∈ (C.walk (pickFor grp pick j u v)).edges) ∧
      (∀ x ∈ (C.connWalk grp pick j u v).verts, x ∈ (C.walk (pickFor grp pick j u v)).verts) ∧
      (C.connWalk grp pick j u v).edges.length = (C.walk (pickFor grp pick j u v)).edges.length := by
  obtain ⟨hel, hside⟩ := hpick j u v hu hv huv hne
  have hw := (hfit.2 _ hel.1).2.2
  refine ⟨hel, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold connFrom; split_ifs
    · exact hel.2.1
    · exact hel.2.2
  · unfold connTo; split_ifs
    · exact hel.2.2
    · exact hel.2.1
  · unfold connFrom; split_ifs with h
    · exact h.symm
    · rcases hside with h' | h'
      · exact absurd h'.1 h
      · exact h'.1.symm
  · unfold connTo; split_ifs with h
    · rcases hside with h' | h'
      · exact h'.2
      · exact absurd (h.symm.trans h'.2) hne
    · rcases hside with h' | h'
      · exact absurd h'.1 h
      · exact h'.2
  · unfold connWalk connFrom connTo; split_ifs
    · exact hw
    · exact Walk.isWalk_reverse hw
  · intro e he
    unfold connWalk at he; split_ifs at he
    · exact he
    · exact List.mem_reverse.mp he
  · intro x hx
    unfold connWalk at hx; split_ifs at hx
    · exact hx
    · exact List.mem_reverse.mp hx
  · unfold connWalk; split_ifs
    · rfl
    · exact List.length_reverse

public section

/-- Query routing. Let `u` and `v` be surviving terminals in one group at depth `j`,
of height `k` (so `j + k` is the leaf depth `L`). Then `route k j u v` is a walk from the owner of
`u` to the owner of `v` that uses no deleted edge and only live vertices, and it has at most
`(2 ^ k - 1) · λ` edges when every connector walk has at most `λ` edges. Leaves are single
terminals by `hleaf`. The connector choice `hpick` is the hypothesis that `exists_surviving_matching_edge` provides. -/
theorem route_spec {G : Graph} (hG : G.IsValid) (hfit : C.FitsGraph G) {D surv : Finset ℕ}
    (hrule : C.ReverseIndexRule D surv) (hsurv : surv ⊆ Finset.range C.numTerm)
    (hpick : C.IsConnectorChoice grp pick surv) {L lam : ℕ}
    (hleaf : ∀ u ∈ surv, ∀ v ∈ surv, grp L u = grp L v → u = v)
    (hlam : ∀ c < C.numConn, (C.walk c).edges.length ≤ lam) :
    ∀ k j u v, j + k = L → u ∈ surv → v ∈ surv → grp j u = grp j v →
      (C.route grp pick k j u v).IsWalk G (C.owner u) (C.owner v) ∧
      (∀ e ∈ (C.route grp pick k j u v).edges, e ∉ D) ∧
      (∀ x ∈ (C.route grp pick k j u v).verts, x ∈ C.liveSet G surv) ∧
      (C.route grp pick k j u v).edges.length ≤ (2 ^ k - 1) * lam := by
  have hown : ∀ t ∈ surv, C.owner t < G.n := fun t ht =>
    hfit.1 t (Finset.mem_range.mp (hsurv ht))
  have hempty : ∀ t ∈ surv, Walk.empty.IsWalk G (C.owner t) (C.owner t) := fun t ht =>
    ⟨hown t ht, hown t ht, Or.inl ⟨rfl, rfl, rfl⟩⟩
  intro k
  induction k with
  | zero =>
    intro j u v hj hu hv huv
    have : u = v := hleaf u hu v hv (by simpa [← hj] using huv)
    subst this
    refine ⟨hempty u hu, ?_, ?_, ?_⟩ <;> simp [route, Walk.empty]
  | succ k ih =>
    intro j u v hj hu hv huv
    have hj' : j + 1 + k = L := by omega
    by_cases h1 : u = v
    · subst h1
      have hr : C.route grp pick (k + 1) j u u = Walk.empty := by simp [route]
      rw [hr]
      refine ⟨hempty u hu, ?_, ?_, ?_⟩ <;> simp [Walk.empty]
    by_cases h2 : grp (j + 1) u = grp (j + 1) v
    · have hr : C.route grp pick (k + 1) j u v = C.route grp pick k (j + 1) u v := by
        simp [route, h1, h2]
      obtain ⟨i1, i2, i3, i4⟩ := ih (j + 1) u v hj' hu hv h2
      refine ⟨hr ▸ i1, hr ▸ i2, hr ▸ i3, hr ▸ (i4.trans ?_)⟩
      apply Nat.mul_le_mul_right
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Nat.le_succ k)
      omega
    · obtain ⟨hel, ha, hb, hua, hbv, hW, hWe, hWv, hWl⟩ :=
        conn_spec C grp pick hfit hpick hu hv huv h2
      have hr : C.route grp pick (k + 1) j u v =
          (C.route grp pick k (j + 1) u (C.connFrom grp pick j u v)).append
            ((C.connWalk grp pick j u v).append
              (C.route grp pick k (j + 1) (C.connTo grp pick j u v) v)) := by
        simp [route, h1, h2]
      obtain ⟨a1, a2, a3, a4⟩ := ih (j + 1) u _ hj' hu ha hua
      obtain ⟨b1, b2, b3, b4⟩ := ih (j + 1) _ v hj' hb hv hbv
      rw [hr]
      refine ⟨Walk.isWalk_append a1 (Walk.isWalk_append hW b1), ?_, ?_, ?_⟩
      · intro e he
        rw [edges_append, edges_append] at he
        rcases List.mem_append.mp he with he | he
        · exact a2 e he
        rcases List.mem_append.mp he with he | he
        · exact C.eligible_edge_not_deleted hrule hel (hWe e he)
        · exact b2 e he
      · intro x hx
        rcases mem_verts_append hx with hx | hx
        · exact a3 x hx
        rcases mem_verts_append hx with hx | hx
        · exact C.eligible_vert_live hG hfit hel (hWv x hx)
        · exact b3 x hx
      · rw [length_edges_append, length_edges_append, hWl]
        have hc := hlam _ hel.1
        have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        have h2k : 2 ^ (k + 1) - 1 = (2 ^ k - 1) + 1 + (2 ^ k - 1) := by
          rw [pow_succ]; omega
        rw [h2k, Nat.add_mul, Nat.add_mul, one_mul]
        omega

/-- The routing recursion at height `k` uses at most `2 ^ k - 1` connectors. -/
theorem routeCount_le : ∀ k j u v, C.routeCount grp pick k j u v ≤ 2 ^ k - 1 := by
  intro k
  induction k with
  | zero => intro j u v; simp [routeCount]
  | succ k ih =>
    intro j u v
    have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h2k : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
    simp only [routeCount]
    split_ifs
    · exact Nat.zero_le _
    · have := ih (j + 1) u v; omega
    · have := ih (j + 1) u (C.connFrom grp pick j u v)
      have := ih (j + 1) (C.connTo grp pick j u v) v
      omega

/-- The routing recursion at height `k`, on surviving terminals of one group, takes at most
`2 ^ k · (λ + 3)` steps when every connector walk has at most `λ` edges. -/
theorem routeOps_le {G : Graph} (hfit : C.FitsGraph G) {surv : Finset ℕ}
    (hpick : C.IsConnectorChoice grp pick surv) {lam : ℕ}
    (hlam : ∀ c < C.numConn, (C.walk c).edges.length ≤ lam) :
    ∀ k j u v, u ∈ surv → v ∈ surv → grp j u = grp j v →
      C.routeOps grp pick k j u v + (lam + 2) ≤ 2 ^ k * (lam + 3) := by
  intro k
  induction k with
  | zero => intro j u v _ _ _; simp [routeOps]; omega
  | succ k ih =>
    intro j u v hu hv huv
    rw [pow_succ, mul_comm (2 ^ k) 2, mul_assoc]
    simp only [routeOps]
    split_ifs with h1 h2
    · have : lam + 3 ≤ 2 ^ k * (lam + 3) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos k)
      omega
    · have := ih (j + 1) u v hu hv h2; omega
    · obtain ⟨hel, ha, hb, hua, hbv, _, _, _, hWl⟩ :=
        conn_spec C grp pick hfit hpick hu hv huv h2
      have := ih (j + 1) u _ hu ha hua
      have := ih (j + 1) _ v hb hv hbv
      have := hlam _ hel.1
      rw [hWl]
      omega

/-- Choices that agree at the branches visited by the routing recursion give the same walk and step count. -/
theorem route_congr_choice (C : ConnectorSystem) {pick read : ℕ → ℕ → ℕ → ℕ}
    {group : ℕ → ℕ → ℕ} {surv : Finset ℕ} {G : Cited.Graph}
    (hfit : C.FitsGraph G) (hpick : C.IsConnectorChoice group pick surv) {L : ℕ}
    (hagree : ∀ j u v, j < L → u ∈ surv → v ∈ surv → group j u = group j v →
      group (j + 1) u ≠ group (j + 1) v → pickFor group read j u v = pickFor group pick j u v)
    (k j u v : ℕ) (hdepth : j + k ≤ L) (hu : u ∈ surv) (hv : v ∈ surv)
    (hgroup : group j u = group j v) :
    C.route group read k j u v = C.route group pick k j u v ∧
      C.routeOps group read k j u v = C.routeOps group pick k j u v := by
  induction k generalizing j u v with
  | zero => simp [route, routeOps]
  | succ k ih =>
    by_cases heq : u = v
    · simp [route, routeOps, heq]
    by_cases hchild : group (j + 1) u = group (j + 1) v
    · obtain ⟨hr, hc⟩ := ih (j + 1) u v (by omega) hu hv hchild
      simp [route, routeOps, heq, hchild, hr, hc]
    have hp := hagree j u v (by omega) hu hv hgroup hchild
    obtain ⟨_, hfrom, hto, hleft, hright, _⟩ :=
      C.conn_spec group pick hfit hpick hu hv hgroup hchild
    obtain ⟨hr₁, hc₁⟩ := ih (j + 1) u _ (by omega) hu hfrom hleft
    obtain ⟨hr₂, hc₂⟩ := ih (j + 1) _ v (by omega) hto hv hright
    have hf : C.connFrom group read j u v = C.connFrom group pick j u v := by
      simp only [connFrom, fwd, hp]
    have ht : C.connTo group read j u v = C.connTo group pick j u v := by
      simp only [connTo, fwd, hp]
    have hw : C.connWalk group read j u v = C.connWalk group pick j u v := by
      simp only [connWalk, fwd, hp]
    simp [route, routeOps, heq, hchild, hf, ht, hw, hr₁, hr₂, hc₁, hc₂]

end

end ConnectorSystem

end MinCostFlow.HierPaths
