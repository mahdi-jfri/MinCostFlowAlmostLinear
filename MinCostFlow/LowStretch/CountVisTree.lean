module

public import MinCostFlow.LowStretch.ProgChildSpec

/-!
# The splits of the merge tree, summed over all nodes

A reset of a child pays, for each merge node that it splits, the leaves of the light child of the
node, the pairs whose lowest common node it is, and one (`KT.visW`). Each merge node is split at
most once along the whole run, so the total is at most the sum `KT.visTot` of these amounts over
all merge nodes. This file bounds that sum by `n (log n + 1) + m + N` (`visTot_le`):
* a vertex lies in the light child of at most `log n + 1` merge nodes, since the size at least
  doubles from one such light child to the next (`card_light_above_le`);
* every pair has one lowest common node (`IsLca.unique`).

It also shows that a node of weight below `x` above a vertex `v` lies below the `x`-node of `v`
(`under_top`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace KT

variable {T : KT} {G : PG}

/-- The amount that a split of the merge node `u` costs. -/
noncomputable def splitW (T : KT) (G : PG) (u : ℕ) : ℕ := T.sz G (T.light G u) + T.nLca G u + 1

/-- The merge nodes. -/
noncomputable def merges (T : KT) (G : PG) : Finset ℕ := (Finset.range T.N).filter (G.n ≤ ·)

/-- The sum of `splitW` over all merge nodes. -/
noncomputable def visTot (T : KT) (G : PG) : ℕ := ∑ u ∈ T.merges G, T.splitW G u

theorem visW_eq (r : Cl) (x : ℕ) : T.visW G r x = ∑ u ∈ T.splitSet G r x, T.splitW G u := rfl

/-- A node of weight below `x` above `v` is below the `x`-node of `v`. -/
theorem under_top (h : T.Ok G) {x v u : ℕ} (hv : v < G.n) (hx : 1 ≤ x) (hvu : T.Under v u)
    (hu : T.mw u < x) : T.Under u (T.top x v) := by
  have ht := isTop_top h hv hx
  have hvN : v < T.N := by have := h.n_lt; omega
  have huN := hvu.lt_N h hvN
  rcases Under.total hvu ht.1 with h1 | h1
  · exact h1
  · by_cases he : T.top x v = u
    · rw [he]; exact Under.refl _
    have htN := ht.1.lt_N h hvN
    have hle := h1.le h htN
    have hp := h1.par_of_ne h he
    have h2 := ht.2.2 (by omega)
    have h3 := hp.mw_le h (par_lt_N h htN)
    omega

theorem par_light (h : T.Ok G) {u : ℕ} (hn : G.n ≤ u) (hu : u < T.N) :
    T.par (T.light G u) = u ∧ T.light G u < u := by
  obtain ⟨hp1, hp2, -, hlt1, hlt2⟩ := h.ch u hn hu
  unfold light; split_ifs <;> simp [*]

/-- From one light child above `v` to a higher one, the size at least doubles. -/
theorem log_light_lt (h : T.Ok G) {u u' : ℕ} (hu : u ∈ T.merges G) (hu' : u' ∈ T.merges G)
    (hne : u ≠ u') (hl : T.Under (T.light G u) (T.light G u')) :
    Nat.log 2 (T.sz G (T.light G u)) < Nat.log 2 (T.sz G (T.light G u')) := by
  simp only [merges, Finset.mem_filter, Finset.mem_range] at hu hu'
  obtain ⟨e1, l1⟩ := par_light h hu.2 hu.1
  obtain ⟨e2, l2⟩ := par_light h hu'.2 hu'.1
  have hne' : T.light G u ≠ T.light G u' := fun he => hne (by rw [← e1, ← e2, he])
  have hp := hl.par_of_ne h hne'
  rw [e1] at hp
  have h2 := two_sz_light h hu.2 hu.1
  have h3 := hp.sz_le (G := G)
  have hpos := sz_pos h (show T.light G u < T.N by omega)
  have : Nat.log 2 (2 * T.sz G (T.light G u)) = Nat.log 2 (T.sz G (T.light G u)) + 1 := by
    rw [mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
  have := Nat.log_mono_right (b := 2) (h2.trans h3)
  omega

open Classical in
/-- A vertex lies in the light child of at most `log n + 1` merge nodes. -/
theorem card_light_above_le (h : T.Ok G) (v : ℕ) :
    ((T.merges G).filter fun u => T.Under v (T.light G u)).card ≤ Nat.log 2 G.n + 1 := by
  classical
  have := Finset.card_le_card_of_injOn (fun u => Nat.log 2 (T.sz G (T.light G u)))
    (s := (T.merges G).filter fun u => T.Under v (T.light G u))
    (t := Finset.range (Nat.log 2 G.n + 1)) ?_ ?_
  · simpa using this
  · intro u _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (Nat.log_mono_right (sz_le_n _))
  · intro u hu u' hu' he
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hu hu'
    by_contra hne
    rcases Under.total hu.2 hu'.2 with hl | hl
    · have := log_light_lt h hu.1 hu'.1 hne hl; simp only at he; omega
    · have := log_light_lt h hu'.1 hu.1 (Ne.symm hne) hl; simp only at he; omega

open Classical in
theorem sum_light_le (h : T.Ok G) :
    ∑ u ∈ T.merges G, T.sz G (T.light G u) ≤ G.n * (Nat.log 2 G.n + 1) := by
  classical
  have e : ∀ u, T.sz G (T.light G u) =
      ∑ v ∈ Finset.range G.n, if T.Under v (T.light G u) then 1 else 0 := by
    intro u
    unfold sz lv
    rw [Finset.card_filter]
  simp_rw [e]
  rw [Finset.sum_comm]
  calc ∑ v ∈ Finset.range G.n, ∑ u ∈ T.merges G, (if T.Under v (T.light G u) then 1 else 0)
      = ∑ v ∈ Finset.range G.n, ((T.merges G).filter fun u => T.Under v (T.light G u)).card := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.card_filter]
    _ ≤ ∑ _v ∈ Finset.range G.n, (Nat.log 2 G.n + 1) :=
        Finset.sum_le_sum fun v _ => card_light_above_le h v
    _ = G.n * (Nat.log 2 G.n + 1) := by simp

theorem IsLca.unique (h : T.Ok G) {a b u u' : ℕ} (ha : a < T.N) (h1 : T.IsLca a b u)
    (h2 : T.IsLca a b u') : u = u' := by
  have hu := h1.1.lt_N h ha
  have hu' := h2.1.lt_N h ha
  have e1 := (h1.2.2 u' h2.1 h2.2.1).le h hu
  have e2 := (h2.2.2 u h1.1 h1.2.1).le h hu'
  omega

theorem sum_nLca_le (h : T.Ok G) (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n) :
    ∑ u ∈ T.merges G, T.nLca G u ≤ G.m := by
  classical
  unfold nLca
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  calc ∑ p ∈ Finset.range G.m, ∑ u ∈ T.merges G, (if T.IsLca (G.pu p) (G.pv p) u then 1 else 0)
      = ∑ p ∈ Finset.range G.m, ((T.merges G).filter fun u =>
          T.IsLca (G.pu p) (G.pv p) u).card := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.card_filter]
    _ ≤ ∑ _p ∈ Finset.range G.m, 1 := by
        refine Finset.sum_le_sum fun p hp => Finset.card_le_one.mpr fun u hu u' hu' => ?_
        simp only [Finset.mem_filter] at hu hu'
        have := (hG p (Finset.mem_range.mp hp)).1
        exact IsLca.unique h (by have := h.n_lt; omega) hu.2 hu'.2
    _ = G.m := by simp

/-- **The total of all splits.** -/
theorem visTot_le (h : T.Ok G) (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n) :
    T.visTot G ≤ G.n * (Nat.log 2 G.n + 1) + G.m + T.N := by
  unfold visTot splitW
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h1 := sum_light_le h
  have h2 := sum_nLca_le h hG
  have h3 : ∑ _u ∈ T.merges G, 1 ≤ T.N := by
    rw [Finset.sum_const, smul_eq_mul, mul_one]
    exact (Finset.card_filter_le _ _).trans (by simp)
  omega

end KT

end MinCostFlow.LowStretch
