module

public import MinCostFlow.LowStretch.DijAbs
public import MinCostFlow.LowStretch.Cluster

/-!
# Dijkstra on the super-vertices of a cluster

The program does not run Dijkstra on the vertices of a cluster. It runs it on the super-vertices:
the classes of vertices joined by light pairs inside `X`. A light pair has length `0`, so the
distance between two vertices depends only on their super-vertices. The arcs are the stored
pairs, with their lengths. A pair that is not stored joins two super-vertices but is longer than
the radius `Δ`, so no shortest walk from the center uses it.

`Cl.Ctr` states how the arc graph sits on the cluster. Then a run of Dijkstra from the
super-vertex of the center, once its queue is empty, has settled every super-vertex with the
distance of its vertices (`Cl.Ctr.tent_eq`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace PG

variable {G : PG}

theorem le_wlen {len : ℕ → ℕ} {ps : List ℕ} {p : ℕ} (hp : p ∈ ps) : len p ≤ wlen len ps := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    rw [wlen_cons]
    rcases List.mem_cons.mp hp with rfl | hp
    · omega
    · have := ih hp; omega

end PG

namespace Cl

variable {G : PG} {c : Cl}

/-- A walk of light pairs has length `0`. -/
theorem wlen_light {V : Set ℕ} {a b : ℕ} {ps : List ℕ} (h : G.IsWalk V (c.light G) a b ps) :
    PG.wlen (c.len G) ps = 0 := by
  induction h with
  | nil => rfl
  | cons _ hp _ _ ih =>
    rw [PG.wlen_cons, ih, c.len_eq_zero_of_light hp]

variable (G c) in
/-- How the arc graph `g` sits on the cluster: `sv` maps each vertex of `X` to its super-vertex,
the arcs are the pairs of `S` between super-vertices, with their lengths, and every pair that
joins two super-vertices and is not in `S` is longer than the radius. -/
structure Ctr (g : AG) (sv : ℕ → ℕ) (S : Set ℕ) : Prop where
  sv_iff : ∀ a ∈ c.X, ∀ b ∈ c.X, sv a = sv b ↔ c.LConn G a b
  arc_iff : ∀ u v k, g.Arc u v k ↔ ∃ p ∈ S, ∃ a ∈ c.X, ∃ b ∈ c.X,
    G.Joins p a b ∧ sv a = u ∧ sv b = v ∧ k = c.len G p
  heavy : ∀ p a b, G.Joins p a b → a ∈ c.X → b ∈ c.X → ¬ c.LConn G a b → p ∉ S →
    c.Δ G < c.len G p

variable {g : AG} {sv : ℕ → ℕ} {S : Set ℕ}

/-- **Arc walks give walks** in the cluster that are no longer. -/
theorem Ctr.sound (h : c.Ctr G g sv S) (hc : c.Conn G) {v k : ℕ}
    (hr : g.Reach (sv c.x0) v k) : ∀ y ∈ c.X, sv y = v → c.d G c.x0 y ≤ k := by
  induction hr with
  | refl =>
    intro y hy hsy
    obtain ⟨ps, hps⟩ := (h.sv_iff _ hc.1 _ hy).mp hsy.symm
    have := PG.dist_le (len := c.len G) (hps.mono le_rfl (Set.subset_univ _))
    rw [wlen_light hps] at this
    exact this
  | @step u v k k' _ ha ih =>
    intro y hy hsy
    obtain ⟨p, -, a, ha', b, hb, hj, hsa, hsb, rfl⟩ := (h.arc_iff _ _ _).mp ha
    have h1 := ih a ha' hsa
    obtain ⟨qs, hqs⟩ := (h.sv_iff _ hb _ hy).mp (hsb.trans hsy.symm)
    have hw : G.IsWalk ↑c.X Set.univ a y (p :: qs) :=
      .cons ha' (Set.mem_univ p) hj (hqs.mono le_rfl (Set.subset_univ _))
    have h2 := PG.dist_le (len := c.len G) hw
    rw [PG.wlen_cons, wlen_light hqs] at h2
    have h3 := PG.dist_triangle (c.len G) (hc.2 a ha') ⟨_, hw⟩
    unfold Cl.d at h1 ⊢
    omega

/-- A walk whose pairs are no longer than the radius gives an arc walk that is no longer. -/
theorem Ctr.lift (h : c.Ctr G g sv S) {s : ℕ} {a y : ℕ} {ps : List ℕ}
    (hw : G.IsWalk ↑c.X Set.univ a y ps) (hl : ∀ p ∈ ps, c.len G p ≤ c.Δ G) {k : ℕ}
    (hr : g.Reach s (sv a) k) : ∃ k' ≤ k + PG.wlen (c.len G) ps, g.Reach s (sv y) k' := by
  induction hw generalizing k with
  | nil => exact ⟨k, by simp, hr⟩
  | @cons a b y p qs ha _ hj hrest ih =>
    have hb : b ∈ c.X := hrest.start_mem
    rw [PG.wlen_cons]
    by_cases hL : c.LConn G a b
    · have hab : sv a = sv b := (h.sv_iff _ ha _ hb).mpr hL
      obtain ⟨k', hk', hr'⟩ := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) (hab ▸ hr)
      exact ⟨k', by omega, hr'⟩
    · by_cases hp : p ∈ S
      · have harc : g.Arc (sv a) (sv b) (c.len G p) :=
          (h.arc_iff _ _ _).mpr ⟨p, hp, a, ha, b, hb, hj, rfl, rfl, rfl⟩
        obtain ⟨k', hk', hr'⟩ := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) (hr.step harc)
        exact ⟨k', by omega, hr'⟩
      · have := h.heavy p a b hj ha hb hL hp
        have := hl p List.mem_cons_self
        omega

/-- **Shortest walks give arc walks.** -/
theorem Ctr.complete (h : c.Ctr G g sv S) (hc : c.Conn G) {y : ℕ} (hy : y ∈ c.X) :
    ∃ k ≤ c.d G c.x0 y, g.Reach (sv c.x0) (sv y) k := by
  obtain ⟨ps, hps, hl⟩ := PG.exists_walk_dist (c.len G) (hc.2 y hy)
  have hd := c.d_le_Δ (G := G) hy
  have hle : ∀ p ∈ ps, c.len G p ≤ c.Δ G := fun p hp => by
    have := PG.le_wlen (len := c.len G) hp
    unfold Cl.d at hd
    omega
  obtain ⟨k, hk, hr⟩ := h.lift hps hle (AG.Reach.refl (g := g) (s := sv c.x0))
  refine ⟨k, ?_, hr⟩
  unfold Cl.d
  omega

/-- **Dijkstra on the super-vertices gives the distances.** At the end of a run from the
super-vertex of the center, with an empty queue and `INF` above the radius, every super-vertex of
the cluster is settled at the distance of its vertices. -/
theorem Ctr.tent_eq (h : c.Ctr G g sv S) (hc : c.Conn G) {INF cur pos : ℕ} {d : DS}
    (hi : g.Inv (sv c.x0) INF cur pos d) (hdone : d.sett cur → g.hi cur ≤ pos) (hQ : d.Q = [])
    (hINF : c.Δ G < INF) {y : ℕ} (hy : y ∈ c.X) :
    d.sett (sv y) ∧ d.tent (sv y) = c.d G c.x0 y := by
  obtain ⟨k, hk, hr⟩ := h.complete hc hy
  have hd := c.d_le_Δ (G := G) hy
  have hp := hi.path hdone le_rfl hi.L_lt.le (by rw [hQ]; simp) hr
  have hs : d.sett (sv y) := by
    by_contra hn
    have := hp.2 hn
    omega
  refine ⟨hs, le_antisymm (by have := hp.1 hs; omega) ?_⟩
  exact h.sound hc (hi.reach_sett hs) y hy rfl

end Cl

end MinCostFlow.LowStretch
