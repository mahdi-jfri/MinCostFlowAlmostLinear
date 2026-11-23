module

public import MinCostFlow.LowStretch.Cluster

/-!
# An upper bound on the radius

The child step runs Dijkstra on each raw child with the value `INF` of the global block, so it
needs the radius below `INF`. A shortest walk can be shortened to one with fewer pairs than the
cluster has vertices (`IsWalk.exists_short`), and each pair is at most the largest weight. So the
radius is at most `|X|` times the largest weight (`Cl.Δ_le_card_mul`), which is below `INF` when
`INF` exceeds `2 n ω` for every pair (`Cl.Δ_lt_INF`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Cl

variable {G : PG} {c : Cl}

/-- A walk whose pairs weigh at most `Mw` has length at most its number of pairs times `Mw`. -/
theorem wlen_le_mul {V P : Set ℕ} {a b : ℕ} {ps : List ℕ} (h : G.IsWalk V P a b ps) {Mw : ℕ}
    (hM : ∀ p < G.m, G.pω p ≤ Mw) : PG.wlen (c.len G) ps ≤ ps.length * Mw := by
  unfold PG.wlen
  have := List.sum_le_card_nsmul (ps.map (c.len G)) Mw (fun x hx => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact (c.len_le q).trans (hM q (h.pair_lt hq)))
  simpa using this

/-- **The radius is at most `|X|` times the largest weight.** -/
theorem Δ_le_card_mul (hc : c.Conn G) {Mw : ℕ} (hM : ∀ p < G.m, G.pω p ≤ Mw) :
    c.Δ G ≤ c.X.card * Mw := by
  refine Finset.sup_le fun y hy => ?_
  obtain ⟨ps, hps⟩ := hc.2 y hy
  obtain ⟨qs, -, hqs, hlen⟩ := hps.exists_short
  have h1 : c.d G c.x0 y ≤ PG.wlen (c.len G) qs := PG.dist_le hqs
  have h2 := wlen_le_mul (c := c) hqs hM
  have h3 : qs.length * Mw ≤ c.X.card * Mw := Nat.mul_le_mul_right _ (by omega)
  exact h1.trans (h2.trans h3)

/-- **The radius is below `INF`**, when `INF` exceeds `2 n ω` for every pair and there is a pair. -/
theorem Δ_lt_INF (hc : c.Conn G) (hX : c.X ⊆ Finset.range G.n) (hm : 0 < G.m) {INF : ℕ}
    (hINF : ∀ p < G.m, 2 * G.n * G.pω p < INF) : c.Δ G < INF := by
  classical
  set Mw := (Finset.range G.m).sup G.pω with hMw
  have hM : ∀ p < G.m, G.pω p ≤ Mw := fun p hp =>
    Finset.le_sup (f := G.pω) (Finset.mem_range.mpr hp)
  obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_sup (Finset.range G.m)
    ⟨0, Finset.mem_range.mpr hm⟩ G.pω
  have hcard : c.X.card ≤ G.n := by
    have := Finset.card_le_card hX; rwa [Finset.card_range] at this
  have h1 := Δ_le_card_mul hc hM
  have h2 := hINF p (Finset.mem_range.mp hp)
  rw [← hMw] at hpe
  rw [← hpe] at h2
  have h3 : c.X.card * Mw ≤ G.n * Mw := Nat.mul_le_mul_right _ hcard
  have h4 : G.n * Mw ≤ 2 * G.n * Mw := Nat.mul_le_mul_right _ (by omega)
  omega

end Cl

end MinCostFlow.LowStretch
