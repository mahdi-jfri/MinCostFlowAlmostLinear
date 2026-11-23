module

public import MinCostFlow.LowStretch.Contract
public import MinCostFlow.LowStretch.KClust
public import MinCostFlow.LowStretch.Stretch3

/-!
# The record of a cluster

The program does not keep the vertex set of a cluster. It keeps a *record* (`Rec`):
* its super-vertices, as a list of Kruskal nodes. Each is a `θ`-node, and `X` is the set of
  vertices below them;
* its stored pairs `S`, each with a flag that says whether the pair is halved. Every stored pair
  joins two different super-vertices, and every active pair is stored;
* its highway without the light pairs.

`Rec.Ok` states this. The local index of a vertex is the position of its `θ`-node in the list
(`Rec.sv`). Two vertices have the same local index exactly when they are joined by light pairs
(`Rec.Ok.sv_iff`). A pair that is not stored is longer than the radius (`Rec.Ok.heavy`), so
Dijkstra on the stored pairs gives the distances (`Rec.Ok.ctr`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

/-- The record of a cluster. -/
structure Rec where
  /-- The super-vertices, as Kruskal nodes. -/
  nodes : List ℕ
  /-- The stored pairs, each with its half flag (`1` when halved). -/
  S : List (ℕ × ℕ)
  /-- The highway without its light pairs. -/
  hwc : List ℕ

namespace Rec

variable (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec)

/-- The local index of the super-vertex of `v`. -/
noncomputable def sv (v : ℕ) : ℕ := R.nodes.idxOf (T.top c.θ v)

/-- The record `R` holds the cluster `c` for the merge tree `T`. -/
structure Ok : Prop where
  inv : c.Inv G P
  tree : T.Ok G
  hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n
  hGo : G.Ok
  hB : 1 ≤ P.B
  hQ : 512 * P.B * G.n ^ 2 ≤ P.Q
  nodup : R.nodes.Nodup
  node_lt : ∀ k ∈ R.nodes, k < T.N
  node_top : ∀ k ∈ R.nodes, ∀ v < G.n, T.Under v k → T.top c.θ v = k
  X_iff : ∀ v, v ∈ c.X ↔ v < G.n ∧ T.top c.θ v ∈ R.nodes
  S_ok : ∀ e ∈ R.S, e.1 < G.m ∧ G.pu e.1 ∈ c.X ∧ G.pv e.1 ∈ c.X ∧
    T.top c.θ (G.pu e.1) ≠ T.top c.θ (G.pv e.1) ∧ e.2 ≤ 1 ∧ (e.2 = 1 ↔ e.1 ∈ c.half)
  S_nodup : (R.S.map Prod.fst).Nodup
  act_sub : ∀ p ∈ c.act G P, p ∈ R.S.map Prod.fst
  hwc_eq : R.hwc = c.hw.filter (fun p => c.θ ≤ G.pω p)

variable {T G P c R}

theorem Ok.n_of_mem (h : R.Ok T G P c) {v : ℕ} (hv : v ∈ c.X) : v < G.n := ((h.X_iff v).mp hv).1

theorem Ok.top_mem (h : R.Ok T G P c) {v : ℕ} (hv : v ∈ c.X) : T.top c.θ v ∈ R.nodes :=
  ((h.X_iff v).mp hv).2

/-- The vertex set is a union of `θ`-nodes. -/
theorem Ok.sat (h : R.Ok T G P c) : T.Sat G c.θ c.X := by
  intro a ha v hv hu
  have hk := h.top_mem ha
  exact (h.X_iff v).mpr ⟨hv, by rw [h.node_top _ hk v hv hu]; exact hk⟩

theorem Ok.sub (h : R.Ok T G P c) : c.X ⊆ Finset.range G.n := fun _ hv =>
  Finset.mem_range.mpr (h.n_of_mem hv)

theorem Ok.sv_lt (h : R.Ok T G P c) {v : ℕ} (hv : v ∈ c.X) : R.sv T c v < R.nodes.length :=
  List.idxOf_lt_length_of_mem (h.top_mem hv)

/-- The local index names the node. -/
theorem Ok.get_sv (h : R.Ok T G P c) {v : ℕ} (hv : v ∈ c.X) :
    R.nodes[R.sv T c v]'(h.sv_lt hv) = T.top c.θ v :=
  List.getElem_idxOf (h.sv_lt hv)

/-- **Local indices are the light classes.** -/
theorem Ok.sv_iff (h : R.Ok T G P c) {a b : ℕ} (ha : a ∈ c.X) (hb : b ∈ c.X) :
    R.sv T c a = R.sv T c b ↔ c.LConn G a b := by
  rw [Cl.lconn_iff h.tree h.hG h.sat h.sub h.inv.one_le ha hb]
  constructor
  · intro e
    rw [← h.get_sv ha, ← h.get_sv hb]
    simp only [e]
  · intro e
    unfold sv; rw [e]

/-- A pair inside `X` that joins two super-vertices and is not active is heavy: `4 Δ < ω`. -/
theorem Ok.heavy4 (h : R.Ok T G P c) {p : ℕ} (hm : p < G.m) (hu : G.pu p ∈ c.X)
    (hv : G.pv p ∈ c.X) (hnl : ¬ c.LConn G (G.pu p) (G.pv p)) (hna : p ∉ c.act G P) :
    4 * c.Δ G < G.pω p := by
  have hc := h.inv
  have hω : P.Q * (c.Δ G * c.θ) < G.pω p ^ 2 := by
    by_contra hle
    exact hna (Cl.mem_act.mpr ⟨hm, hu, hv, hnl, by omega⟩)
  set K := 32 * P.B * G.n ^ 2 with hK
  have h1 : c.Δ G ≤ K * c.θ := hc.small
  have h2 : 16 * K ≤ P.Q := by
    have e : 16 * K = 512 * P.B * G.n ^ 2 := by rw [hK]; ring
    have := h.hQ
    omega
  have h3 : P.Q * (c.Δ G * c.Δ G) ≤ K * (P.Q * (c.Δ G * c.θ)) := by
    calc P.Q * (c.Δ G * c.Δ G) ≤ P.Q * (c.Δ G * (K * c.θ)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
      _ = K * (P.Q * (c.Δ G * c.θ)) := by ring
  have h4 : 16 * K * (c.Δ G * c.Δ G) ≤ P.Q * (c.Δ G * c.Δ G) := Nat.mul_le_mul_right _ h2
  have hKpos : 0 < K := by
    have hn : 0 < G.n := by have := h.n_of_mem hu; omega
    have := h.hB
    rw [hK]; positivity
  have h5 : K * (16 * (c.Δ G * c.Δ G)) < K * (G.pω p * G.pω p) := by
    have : K * (P.Q * (c.Δ G * c.θ)) < K * G.pω p ^ 2 := Nat.mul_lt_mul_of_pos_left hω hKpos
    rw [pow_two] at this
    have e : K * (16 * (c.Δ G * c.Δ G)) = 16 * K * (c.Δ G * c.Δ G) := by ring
    omega
  have h6 : (4 * c.Δ G) * (4 * c.Δ G) < G.pω p * G.pω p := by
    have := Nat.lt_of_mul_lt_mul_left h5
    have e : (4 * c.Δ G) * (4 * c.Δ G) = 16 * (c.Δ G * c.Δ G) := by ring
    omega
  exact Nat.mul_self_lt_mul_self_iff.mp h6

/-- A pair that joins two super-vertices is not light. -/
theorem Ok.not_light (h : R.Ok T G P c) {p a b : ℕ} (hj : G.Joins p a b) (ha : a ∈ c.X)
    (hb : b ∈ c.X) (hnl : ¬ c.LConn G a b) : c.θ ≤ G.pω p := by
  by_contra hl
  push Not at hl
  exact hnl ⟨[p], .cons ha hl hj (.nil hb)⟩

/-- **Pairs that are not stored are long.** A pair inside `X` that joins two super-vertices and is
not stored, or is stored but longer than a bound `D ≥ Δ`, is longer than the radius. -/
theorem Ok.heavy (h : R.Ok T G P c) {D : ℕ} (hD : c.Δ G ≤ D) {p a b : ℕ} (hj : G.Joins p a b)
    (ha : a ∈ c.X) (hb : b ∈ c.X) (hnl : ¬ c.LConn G a b)
    (hp : ¬ (p ∈ R.S.map Prod.fst ∧ c.len G p ≤ D)) : c.Δ G < c.len G p := by
  have hθ := h.not_light hj ha hb hnl
  by_cases hS : p ∈ R.S.map Prod.fst
  · have : ¬ c.len G p ≤ D := fun hl => hp ⟨hS, hl⟩
    omega
  · have hna : p ∉ c.act G P := fun hp' => hS (h.act_sub p hp')
    obtain ⟨hm, hj'⟩ := hj
    have hlen := Cl.half_le_len (c := c) (G := G) hθ
    have hnl' : ¬ c.LConn G (G.pu p) (G.pv p) := by
      rcases hj' with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]; exact hnl
      · rw [e1, e2]; rintro ⟨ps, hps⟩; exact hnl ⟨ps.reverse, hps.reverse⟩
    have hu : G.pu p ∈ c.X := by rcases hj' with ⟨e1, -⟩ | ⟨e1, -⟩ <;> rw [e1] <;> assumption
    have hv : G.pv p ∈ c.X := by rcases hj' with ⟨-, e2⟩ | ⟨-, e2⟩ <;> rw [e2] <;> assumption
    have := h.heavy4 hm hu hv hnl' hna
    obtain ⟨-, -, -, h2, -⟩ := h.hGo p hm
    omega

/-- **The stored pairs carry Dijkstra.** An arc graph whose arcs are the stored pairs of length at
most `D ≥ Δ` between local indices, in both directions, sits on the cluster as `Cl.Ctr` asks. -/
theorem Ok.ctr (h : R.Ok T G P c) {D : ℕ} (hD : c.Δ G ≤ D) {g : AG}
    (hg : ∀ u v k, g.Arc u v k ↔ ∃ p ∈ R.S.map Prod.fst, c.len G p ≤ D ∧ ∃ a ∈ c.X, ∃ b ∈ c.X,
      G.Joins p a b ∧ R.sv T c a = u ∧ R.sv T c b = v ∧ k = c.len G p) :
    c.Ctr G g (R.sv T c) {p | p ∈ R.S.map Prod.fst ∧ c.len G p ≤ D} where
  sv_iff a ha b hb := h.sv_iff ha hb
  arc_iff u v k := by
    rw [hg]
    constructor
    · rintro ⟨p, hp, hl, rest⟩; exact ⟨p, ⟨hp, hl⟩, rest⟩
    · rintro ⟨p, ⟨hp, hl⟩, rest⟩; exact ⟨p, hp, hl, rest⟩
  heavy p a b hj ha hb hnl hp := h.heavy hD hj ha hb hnl hp

end Rec

end MinCostFlow.LowStretch
