module

public import MinCostFlow.LowStretch.Arcs

/-!
# The excess of a petal vertex

If the target reaches `v` by a directed walk of cost `k`, then some highway vertex `h` reaches `v`
by an undirected walk `S` inside the petal of radius `k` with

  `(d(x0, t) - d(x0, h)) + 2 · len S + 2 · d(x0, h) ≤ k + 2 · d(x0, v)`.

Here `d(x0, t) - d(x0, h)` is the distance from the target to `h` along the highway, called `k`
in [AN19], and the inequality is inequality (14) of [AN19] with the walk `S` in place of a
shortest path from `h` to `v`. We also show that the highway vertices that stay in `Y` lie in the
petal of radius equal to their distance from the target.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Cl

variable {G : PG} {c : Cl} {t : ℕ} {hw : List ℕ}

theorem hv_zero (G : PG) (t : ℕ) (hw : List ℕ) : hv G t hw 0 = t := by
  cases hw <;> rfl

theorem IsHighway.joins (hh : c.IsHighway G t hw) {i : ℕ} (hi : i < hw.length) :
    G.Joins (hw.getD i 0) (hv G t hw i) (hv G t hw (i + 1)) := hh.1.joins_getD hi

theorem IsHighway.hv_mem (hh : c.IsHighway G t hw) {i : ℕ} (hi : i ≤ hw.length) :
    hv G t hw i ∈ c.X := hh.1.getD_mem hi

theorem IsHighway.hv_length (hh : c.IsHighway G t hw) : hv G t hw hw.length = c.x0 :=
  hh.1.getD_length

/-- Along the highway the distance to the center does not grow. -/
theorem d_hv_le (hh : c.IsHighway G t hw) {i : ℕ} (hi : i ≤ hw.length) :
    c.d G c.x0 (hv G t hw i) ≤ c.d G c.x0 t := by
  induction i with
  | zero => rw [hv_zero]
  | succ i ih =>
    have := hh.2 i (by omega)
    have := ih (by omega)
    omega

/-- Inequality (14) of [AN19] for the rounded petals. -/
theorem exists_excess (hc : c.Conn G) {Y : Set ℕ} (hY : Y ⊆ ↑c.X)
    (hh : c.IsHighway G t hw) {v k : ℕ} (h : c.DR G t hw Y v k) :
    ∃ i ≤ hw.length, ∃ S, G.IsWalk (c.Petal G t hw Y k) Set.univ (hv G t hw i) v S ∧
      (c.d G c.x0 t - c.d G c.x0 (hv G t hw i)) + 2 * PG.wlen (c.len G) S +
        2 * c.d G c.x0 (hv G t hw i) ≤ k + 2 * c.d G c.x0 v := by
  induction h with
  | start ht =>
    refine ⟨0, Nat.zero_le _, [], ?_, ?_⟩
    · rw [hv_zero]; exact .nil ⟨0, le_rfl, .start ht⟩
    · rw [hv_zero]; simp
  | @step a b k k' ha harc hb ih =>
    have hbP : b ∈ c.Petal G t hw Y (k + k') := ⟨_, le_rfl, .step ha harc hb⟩
    cases harc with
    | @normal p _ _ hj =>
      obtain ⟨i, hi, S, hS, hineq⟩ := ih
      refine ⟨i, hi, S ++ [p], (hS.mono (Petal.mono (by omega)) le_rfl).snoc
        (Set.mem_univ p) hj hbP, ?_⟩
      have h1 := d_le_add_len hc hj (hY ha.mem) (hY hb)
      have h2 := le_rc c.θ (c.wbar G p a b)
      have h3 : c.wbar G p a b + c.d G c.x0 b = c.d G c.x0 a + c.len G p := by
        unfold wbar; omega
      simp only [PG.wlen_append, PG.wlen_cons, PG.wlen_nil, add_zero]
      omega
    | @high i hi =>
      refine ⟨i + 1, hi, [], .nil hbP, ?_⟩
      have h1 := potential hc hY hh ha
      have h2 := hh.2 i hi
      simp only [PG.wlen_nil, Nat.mul_zero, Nat.add_zero]
      omega

/-- A highway vertex whose earlier highway vertices all lie in `Y` is reached at the cost of its
distance from the target along the highway. -/
theorem dr_hv (hh : c.IsHighway G t hw) {Y : Set ℕ} {i : ℕ} (hi : i ≤ hw.length)
    (hY : ∀ j ≤ i, hv G t hw j ∈ Y) :
    c.DR G t hw Y (hv G t hw i) (c.d G c.x0 t - c.d G c.x0 (hv G t hw i)) := by
  induction i with
  | zero =>
    have := hY 0 le_rfl
    rw [hv_zero] at this ⊢
    simpa using DR.start (c := c) (G := G) (hw := hw) this
  | succ i ih =>
    have h1 := ih (by omega) fun j hj => hY j (by omega)
    have h2 := hh.2 i (by omega)
    have h3 := d_hv_le hh (i := i) (by omega)
    have := DR.step h1 (Arc.high (c := c) (by omega)) (hY (i + 1) le_rfl)
    convert this using 1
    omega

end Cl

end MinCostFlow.LowStretch
