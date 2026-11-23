module

public import MinCostFlow.LowStretch.ProgClusterSet10
public import MinCostFlow.LowStretch.WalkShort

/-!
# The setup of a cluster: the radius is below `INF`

The first run of Dijkstra needs `Δ < INF` (`drawPre`). The global block gives
`2 n ω(p) < INF` for every pair `p` (`GlobL.Ok.hINF`). Each vertex `y` of `X` is reached from the
center by a walk in `X` with fewer than `|X| ≤ n` pairs (`IsWalk.exists_short`), and each pair has
length at most its weight. So `2 n · d(y) ≤ (n - 1)(INF - 1) < 2 n · INF` when `0 < INF`
(`Cl.d_lt_INF`), and `Δ`, the largest of these distances, is below `INF`
(`Cl.Δ_lt_INF_of_pos`; `ProgChildDelta` has the form with `0 < m`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Cl

variable {G : PG} {c : Cl}

/-- The length of a pair is at most its weight. -/
theorem len_le_pω (p : ℕ) : c.len G p ≤ G.pω p := by
  unfold Cl.len; split_ifs <;> omega

/-- Along a walk, `2 n` times the length is at most the number of pairs times `INF - 1`. -/
theorem wlen_le_INF {INF : ℕ} (hINF : ∀ p < G.m, 2 * G.n * G.pω p < INF) {V : Set ℕ} {a b : ℕ}
    {ps : List ℕ} (h : G.IsWalk V Set.univ a b ps) :
    2 * G.n * PG.wlen (c.len G) ps ≤ ps.length * (INF - 1) := by
  induction h with
  | nil => simp
  | @cons a b c' p ps ha hp hj rest ih =>
    have h1 := hINF p hj.1
    have h2 : 2 * G.n * c.len G p ≤ 2 * G.n * G.pω p := Nat.mul_le_mul_left _ (len_le_pω p)
    simp only [PG.wlen_cons, List.length_cons, Nat.mul_add, Nat.add_mul, one_mul]
    omega

/-- **Each distance in the cluster is below `INF`.** -/
theorem d_lt_INF (hc : c.Conn G) (hXn : c.X.card ≤ G.n) {INF : ℕ} (hpos : 0 < INF)
    (hINF : ∀ p < G.m, 2 * G.n * G.pω p < INF) {y : ℕ} (hy : y ∈ c.X) : c.d G c.x0 y < INF := by
  obtain ⟨ps, hps⟩ := hc.2 y hy
  obtain ⟨qs, -, hq, hlen⟩ := hps.exists_short
  have hd : c.d G c.x0 y ≤ PG.wlen (c.len G) qs := PG.dist_le hq
  have hk := wlen_le_INF (c := c) hINF hq
  have h1 : 2 * G.n * c.d G c.x0 y ≤ 2 * G.n * PG.wlen (c.len G) qs := Nat.mul_le_mul_left _ hd
  have h2 : qs.length * (INF - 1) ≤ (G.n - 1) * (INF - 1) := Nat.mul_le_mul_right _ (by omega)
  by_contra hge
  push Not at hge
  have h3 : 2 * G.n * INF ≤ 2 * G.n * c.d G c.x0 y := Nat.mul_le_mul_left _ hge
  have h4 : (G.n - 1) * (INF - 1) ≤ G.n * INF := Nat.mul_le_mul (by omega) (by omega)
  have hn : 1 ≤ G.n := by
    have := Finset.card_pos.mpr ⟨y, hy⟩; omega
  have h5 : G.n * INF < 2 * G.n * INF := by nlinarith
  omega

/-- **The radius is below `INF`.** -/
theorem Δ_lt_INF_of_pos (hc : c.Conn G) (hXn : c.X.card ≤ G.n) {INF : ℕ} (hpos : 0 < INF)
    (hINF : ∀ p < G.m, 2 * G.n * G.pω p < INF) : c.Δ G < INF := by
  unfold Cl.Δ
  exact (Finset.sup_lt_iff (by simpa using hpos)).mpr fun y hy => d_lt_INF hc hXn hpos hINF hy

end Cl

end MinCostFlow.LowStretch
