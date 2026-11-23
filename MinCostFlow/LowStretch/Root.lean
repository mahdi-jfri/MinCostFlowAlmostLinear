module

public import MinCostFlow.LowStretch.Exist4

/-!
# The first cluster

The first cluster holds every vertex, has center and target `0`, nothing halved and no highway.
Its threshold is the largest `θ` with `B n θ ≤ Δ(θ)` below the largest weight plus one. At
`θ = 1` the test passes, since every pair is heavier than `8 B n`. Above every weight it fails,
since then every pair has length `0`. So the largest `θ` is followed by a failing `θ + 1`, and
`Δ(θ) ≤ Δ(θ + 1) + n (θ + 1) < (B + 1) n (θ + 1) ≤ 32 B n² θ` (`exists_root`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

variable {G : PG} {P : Par}

/-- The first cluster, with threshold `θ`. -/
def root (G : PG) (θ : ℕ) : Cl :=
  { X := Finset.range G.n, x0 := 0, t := 0, half := ∅, θ := θ, hw := [] }

theorem root_eq_reset (θ x : ℕ) : (root G θ).reset x = root G x := rfl

/-- The largest weight. -/
def PG.maxω (G : PG) : ℕ := ((List.range G.m).map G.pω).foldr max 0

theorem PG.le_maxω {p : ℕ} (hp : p < G.m) : G.pω p ≤ G.maxω := by
  unfold PG.maxω
  have hmem : G.pω p ∈ (List.range G.m).map G.pω := List.mem_map.mpr ⟨p, List.mem_range.mpr hp, rfl⟩
  generalize (List.range G.m).map G.pω = l at hmem
  induction l with
  | nil => simp at hmem
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hmem with h | h
    · rw [h]; exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem root_Δ_big (hc : (root G 1).Conn G) : (root G (G.maxω + 1)).Δ G = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold Cl.Δ
  refine Finset.sup_le fun y hy => ?_
  obtain ⟨ps, hps⟩ := hc.2 y hy
  have := PG.dist_le (len := (root G (G.maxω + 1)).len G) hps
  have h0 : PG.wlen ((root G (G.maxω + 1)).len G) ps = 0 := by
    unfold PG.wlen
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    apply Cl.len_eq_zero_of_light
    show G.pω p < G.maxω + 1
    have := PG.le_maxω (hps.pair_lt hp)
    omega
  unfold Cl.d
  exact this.trans h0.le

/-- **The first cluster** meets the invariant for some threshold. -/
theorem exists_root (hGo : G.Ok) (hB : 1 ≤ P.B) (hω : ∀ p < G.m, 8 * P.B * G.n ≤ G.pω p)
    (hc : (root G 1).Conn G) : ∃ θ, (root G θ).Inv G P := by
  have hgood : ∀ θ, (root G θ).Good G := fun θ =>
    ⟨hc, ⟨.nil (by simpa [root] using hc.1), fun i hi => absurd hi (by simp [root])⟩,
      fun p hp => absurd hp (by simp [root])⟩
  have hn : 1 ≤ G.n := by
    have := hc.1; simp [root] at this; omega
  have hcard : (root G 1).X.card = G.n := by simp [root]
  by_cases hX : G.n ≤ 1
  · refine ⟨1, hgood 1, le_rfl, Or.inl (by simp [root]; omega), ?_, fun _ h => h⟩
    have hz : (root G 1).Δ G = 0 := by
      apply Nat.eq_zero_of_le_zero
      unfold Cl.Δ
      refine Finset.sup_le fun y hy => ?_
      have : y = 0 := by simp [root] at hy; omega
      subst this
      exact (PG.dist_self (by simpa [root] using hc.1)).le
    rw [hz]; exact Nat.zero_le _
  push Not at hX
  set U := G.maxω + 1 with hU
  have hq1 : P.B * G.n * 1 ≤ (root G 1).Δ G := by
    set K := P.B * G.n with hK
    have e : 8 * P.B * G.n = 8 * K := by rw [hK]; ring
    have hK1 : 1 ≤ K := by rw [hK]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    have := Cl.Δ_one (r := root G 1) hc (by rw [hcard]; omega) hω (M := 8 * P.B * G.n) (by omega)
    rw [root_eq_reset] at this
    omega
  classical
  set x := Nat.findGreatest (fun x => 1 ≤ x ∧ P.B * G.n * x ≤ (root G x).Δ G) U with hx
  have hU1 : 1 ≤ U := by omega
  have hxs : 1 ≤ x ∧ P.B * G.n * x ≤ (root G x).Δ G :=
    Nat.findGreatest_spec (P := fun x => 1 ≤ x ∧ P.B * G.n * x ≤ (root G x).Δ G) hU1 ⟨le_rfl, hq1⟩
  have hxU : x < U := by
    rcases Nat.lt_or_ge x U with h | h
    · exact h
    · have hxe : x = U := le_antisymm (Nat.findGreatest_le U) h
      have := hxs.2
      rw [hxe, hU, root_Δ_big hc] at this
      have : 1 ≤ P.B * G.n * (G.maxω + 1) := by
        have : 0 < G.n := by omega
        exact Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
  have hfail := Nat.findGreatest_is_greatest
    (P := fun x => 1 ≤ x ∧ P.B * G.n * x ≤ (root G x).Δ G) (show x < x + 1 by omega) (by omega)
  push Not at hfail
  have hf := hfail (by omega)
  have hst := Cl.Δ_step (r := root G 1) hc x
  rw [root_eq_reset, root_eq_reset, hcard] at hst
  have hup : (root G x).Δ G ≤ 32 * P.B * G.n ^ 2 * x := by
    set s := G.n
    have e1 : P.B * s * (x + 1) + s * (x + 1) = (P.B + 1) * (s * (x + 1)) := by ring
    have e2 : (P.B + 1) * (s * (x + 1)) ≤ (2 * P.B) * (s * (2 * x)) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (by omega))
    have e3 : (2 * P.B) * (s * (2 * x)) = 4 * (P.B * s * x) := by ring
    have e4 : 4 * (P.B * s * x) ≤ 32 * P.B * s ^ 2 * x := by
      have : P.B * s * x ≤ P.B * s * x * s := Nat.le_mul_of_pos_right _ (by omega)
      have e : 32 * P.B * s ^ 2 * x = 32 * (P.B * s * x * s) := by ring
      omega
    omega
  have hcx : (root G x).X.card = G.n := by simp [root]
  exact ⟨x, hgood x, hxs.1, Or.inr (by rw [hcx]; exact hxs.2), hup, fun _ h => h⟩

end MinCostFlow.LowStretch
