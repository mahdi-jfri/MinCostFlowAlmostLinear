module

public import MinCostFlow.LowStretch.Stretch5

/-!
# The work of a run

This file starts item 2, the operation count. The program handles one cluster at a time. On a
cluster it spends a fixed amount `a` for the cluster and for each of its active pairs, and then it
handles the children. We write this count as the relation `Counted a c N`: the run below `c` may
cost `N` steps. It has the same shape as `Run`.

To bound `N` we use a potential, the *work* of a cluster:
`Wk c = gsum c + G0 · inact c + 2 |X| - 1`.
The first two terms are the ones of the stretch potential that pay for the active pairs: each
active pair has at most `G0` levels left, and a pair that is light-joined may later become active,
so it keeps `G0` levels in reserve. The last term pays `1` for each cluster, since a cluster with
at least two vertices has at least two children (`Wk_step`). So `N ≤ a · Wk c` (`Counted.le`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open Cl

variable {G : PG} {P : Par}

/-- The work of a cluster. -/
noncomputable def Cl.Wk (G : PG) (P : Par) (c : Cl) : ℝ :=
  c.gsum G P + G0 G P * inact G P c + (2 * (c.X.card : ℝ) - 1)

/-- `Counted a c N`: the run below `c` costs at most `N`, when each cluster costs `a` times one
plus its number of active pairs. -/
inductive Counted (G : PG) (P : Par) (a : ℕ) : Cl → ℕ → Prop
  | leaf {c : Cl} {N : ℕ} : c.X.card ≤ 1 → N ≤ a → Counted G P a c N
  | node {c : Cl} {N : ℕ} (D : Dec) (cs : ℕ → Cl) (Ns : ℕ → ℕ) :
      2 ≤ c.X.card → c.DecOk G P D → (∀ k < D.nch, Next G P (c.raw G D k) (cs k)) →
      (∀ k < D.nch, Counted G P a (cs k) (Ns k)) →
      N ≤ a * ((c.act G P).card + 1) + ∑ k ∈ Finset.range D.nch, Ns k → Counted G P a c N

theorem Cl.Wk_leaf (hGo : G.Ok) {c : Cl} (hc : c.Inv G P) (hX : c.X.card ≤ 1) : 1 ≤ c.Wk G P := by
  have h1 : 1 ≤ c.X.card := Finset.card_pos.mpr ⟨_, hc.good.conn.1⟩
  have h2 : (c.X.card : ℝ) = 1 := by exact_mod_cast le_antisymm hX h1
  have h3 := gsum_nonneg (P := P) hGo c
  have h4 := inact_nonneg (G := G) (P := P) c
  have h5 := G0_ge (G := G) (P := P)
  have h6 : 0 ≤ G0 G P * inact G P c := mul_nonneg (by linarith) h4
  unfold Wk
  rw [h2]
  linarith

/-- **One step**: the work of a cluster pays for the cluster, its active pairs and the work of its
children. -/
theorem Cl.Wk_step (hGo : G.Ok) (hB : 1 ≤ P.B) (hcw : ∀ p, 1 ≤ P.cw p) {c : Cl} (hc : c.Inv G P)
    (hX : 2 ≤ c.X.card) {D : Dec} (hD : c.DecOk G P D) {cs : ℕ → Cl}
    (hn : ∀ k < D.nch, Next G P (c.raw G D k) (cs k)) :
    ((c.act G P).card : ℝ) + 1 + ∑ k ∈ Finset.range D.nch, (cs k).Wk G P ≤ c.Wk G P := by
  classical
  have hg := gsum_step hGo hB hc hX hD hn
  have hi := inact_sum hGo hB hc hX hD hn
  have hG0 := G0_ge (G := G) (P := P)
  have hcard : ((c.act G P).card : ℝ) ≤ ∑ p ∈ c.act G P, (P.cw p : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    exact Finset.sum_le_sum fun p _ => by exact_mod_cast hcw p
  -- the sizes of the children add up to `|X|`, and there are at least two children
  have hsz : ∑ k ∈ Finset.range D.nch, (2 * ((cs k).X.card : ℝ) - 1) =
      2 * (c.X.card : ℝ) - D.nch := by
    have e : ∀ k ∈ Finset.range D.nch, (cs k).X.card = (c.raw G D k).X.card := fun k hk =>
      by rw [(hn k (Finset.mem_range.mp hk)).X_eq]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    have : ∑ k ∈ Finset.range D.nch, ((cs k).X.card : ℝ) = c.X.card := by
      rw [← sum_card_raw (G := G) (c := c) (D := D), Nat.cast_sum]
      exact Finset.sum_congr rfl fun k hk => by rw [e k hk]
    rw [this]
  have hnch : (2 : ℝ) ≤ D.nch := by
    have := len_pos hB hc hX hD
    unfold Dec.nch
    exact_mod_cast (show 2 ≤ D.ps.length + 1 by omega)
  have hsplit : ∑ k ∈ Finset.range D.nch, (cs k).Wk G P =
      ∑ k ∈ Finset.range D.nch, (cs k).gsum G P +
        G0 G P * ∑ k ∈ Finset.range D.nch, inact G P (cs k) +
        ∑ k ∈ Finset.range D.nch, (2 * ((cs k).X.card : ℝ) - 1) := by
    unfold Wk
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  have hi' : G0 G P * ∑ k ∈ Finset.range D.nch,
        ∑ p ∈ (cs k).act G P \ c.act G P, (P.cw p : ℝ) +
      G0 G P * ∑ k ∈ Finset.range D.nch, inact G P (cs k) ≤ G0 G P * inact G P c := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    exact mul_le_mul_of_nonneg_left hi (by linarith)
  rw [hsplit, hsz]
  unfold Wk
  linarith

/-- **The count is at most `a` times the work.** -/
theorem Counted.le (hGo : G.Ok) (hB : 1 ≤ P.B) (hcw : ∀ p, 1 ≤ P.cw p) {a : ℕ} {c : Cl} {N : ℕ}
    (h : Counted G P a c N) (hc : c.Inv G P) : (N : ℝ) ≤ a * c.Wk G P := by
  induction h with
  | @leaf c N hX hN =>
    have := Cl.Wk_leaf hGo hc hX
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    have : (N : ℝ) ≤ a := by exact_mod_cast hN
    nlinarith
  | @node c N D cs Ns hX hD hn _ hN ih =>
    have hinv : ∀ k < D.nch, (cs k).Inv G P := fun k hk => child_inv hGo hB hc hX hD hk (hn k hk)
    have hstep := Cl.Wk_step hGo hB hcw hc hX hD hn
    have hks : ∑ k ∈ Finset.range D.nch, (Ns k : ℝ) ≤
        ∑ k ∈ Finset.range D.nch, (a : ℝ) * (cs k).Wk G P :=
      Finset.sum_le_sum fun k hk => ih k (Finset.mem_range.mp hk) (hinv k (Finset.mem_range.mp hk))
    have hN' : (N : ℝ) ≤ a * (((c.act G P).card : ℝ) + 1) + ∑ k ∈ Finset.range D.nch, (Ns k : ℝ) := by
      exact_mod_cast hN
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hstep ha
    rw [← Finset.mul_sum] at hks
    nlinarith

end MinCostFlow.LowStretch
