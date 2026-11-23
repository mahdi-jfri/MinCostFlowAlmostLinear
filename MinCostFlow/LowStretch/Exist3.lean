module

public import MinCostFlow.LowStretch.Exist2

/-!
# A threshold for every child

A child with a small radius (`Δ < B s θ` for `s = |X|`) gets a new threshold `θ'`. We take the
largest `θ'` in `[1, θ/4]` with `B s θ' ≤ Δ(θ')`, where `Δ(θ')` is the radius of the child with
threshold `θ'`, nothing halved and no highway.
* `θ' = 1` qualifies, because every pair is heavier than `8 B n` (`Δ_one`).
* Raising the threshold by `1` lowers the radius by at most `s (θ' + 1)` (`Δ_step`). So if
  `θ' + 1` does not qualify, `Δ(θ') < (B + 1) s (θ' + 1) ≤ 32 B s² θ'`.
* At `θ' = θ/4` the radius is at most `2 Δ + s θ < 3 B s θ`.
The threshold `θ ≥ 4` is large enough: below `4`, no pair is light and the radius is at least
`4 B n`, so the child keeps its threshold (`θ_ge_four`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

variable {G : PG} {P : Par}

namespace Cl

/-- The child `r` reset to threshold `x`. -/
def reset (r : Cl) (x : ℕ) : Cl := { X := r.X, x0 := r.x0, t := r.x0, half := ∅, θ := x, hw := [] }

variable {r : Cl}

/-- If every pair has length at least `M`, every vertex other than the center is at distance at
least `M`. -/
theorem le_d_of_ne {c : Cl} (hc : c.Conn G) {M : ℕ} (hM : ∀ p < G.m, M ≤ c.len G p) {y : ℕ}
    (hy : y ∈ c.X) (hne : y ≠ c.x0) : M ≤ c.d G c.x0 y := by
  obtain ⟨ps, hps, hl⟩ := G.exists_walk_dist (c.len G) (hc.2 y hy)
  unfold d; rw [← hl]
  cases hps with
  | nil _ => exact absurd rfl hne
  | @cons a b _ p ps _ _ hj _ =>
    simp only [PG.wlen_cons]
    have := hM p hj.1
    omega

theorem le_Δ_of_ne {c : Cl} (hc : c.Conn G) {M : ℕ} (hM : ∀ p < G.m, M ≤ c.len G p)
    (hX : 2 ≤ c.X.card) : M ≤ c.Δ G := by
  obtain ⟨y, hy, hne⟩ := Finset.exists_mem_ne (show 1 < c.X.card by omega) c.x0
  exact (le_d_of_ne hc hM hy hne).trans (d_le_Δ hy)

theorem reset_conn (hr : r.Conn G) (x : ℕ) : (r.reset x).Conn G := hr

theorem reset_len {x p : ℕ} (h : x ≤ G.pω p) : (r.reset x).len G p = G.pω p := by
  unfold len reset; simp; omega

theorem Δ_one (hr : r.Conn G) (hX : 2 ≤ r.X.card) {M : ℕ} (hω : ∀ p < G.m, M ≤ G.pω p)
    (hM : 1 ≤ M) : M ≤ (r.reset 1).Δ G :=
  le_Δ_of_ne (reset_conn hr 1) (fun p hp => by
    rw [reset_len (by have := hω p hp; omega)]; exact hω p hp) hX

theorem Δ_step (hr : r.Conn G) (x : ℕ) :
    (r.reset x).Δ G ≤ (r.reset (x + 1)).Δ G + r.X.card * (x + 1) := by
  change (r.X.sup fun y => (r.reset x).d G r.x0 y) ≤ _
  refine Finset.sup_le fun y hy => ?_
  obtain ⟨ps, hps, hl⟩ := G.exists_walk_dist ((r.reset (x + 1)).len G) (hr.2 y hy)
  have h1 := d_le_of_walk (c' := r.reset x) (f := (r.reset (x + 1)).len G) (θ := x + 1)
    (a := r.x0) (b := y) (ps := ps) hps (fun p _ => by
      unfold len reset; simp only [Finset.notMem_empty, ↓reduceIte]
      split_ifs <;> omega)
  have h2 : (r.reset (x + 1)).d G r.x0 y ≤ (r.reset (x + 1)).Δ G :=
    d_le_Δ (c := r.reset (x + 1)) (G := G) hy
  have e2 : (r.reset (x + 1)).d G r.x0 y = PG.wlen ((r.reset (x + 1)).len G) ps := hl.symm
  have e : (r.reset x).X = r.X := rfl
  rw [e] at h1
  omega

theorem Δ_reset_le (hGo : G.Ok) (hr : r.Good G) {x : ℕ} :
    (r.reset x).Δ G ≤ 2 * r.Δ G + r.X.card * r.θ := by
  unfold Δ
  refine Finset.sup_le fun y hy => ?_
  have h1 := d_le_two_of hGo hr (c' := r.reset x) rfl rfl hy
  have h2 := d_le_Δ (c := r) (G := G) hy
  unfold Δ at h2
  show (r.reset x).d G r.x0 y ≤ _
  have : (r.reset x).x0 = r.x0 := rfl
  rw [this] at h1
  omega

/-- A good child whose radius is below `B s θ` has `θ ≥ 4`, when every pair is heavier than
`8 B n`. -/
theorem θ_ge_four (hB : 1 ≤ P.B) (hr : r.Good G) (hX : 2 ≤ r.X.card) (hXn : r.X.card ≤ G.n)
    (hω : ∀ p < G.m, 8 * P.B * G.n ≤ G.pω p) (hlt : r.Δ G < P.B * r.X.card * r.θ) :
    4 ≤ r.θ := by
  by_contra h4
  set K := P.B * G.n with hK
  have hK1 : 1 ≤ K := by
    have : 0 < G.n := by omega
    rw [hK]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hM : ∀ p < G.m, 4 * K ≤ r.len G p := fun p hp => by
    have h1 := hω p hp
    have e : 8 * P.B * G.n = 8 * K := by rw [hK]; ring
    have := half_le_len (c := r) (G := G) (p := p) (by omega)
    omega
  have h1 := le_Δ_of_ne hr.conn hM hX
  have h2 : P.B * r.X.card * r.θ ≤ P.B * G.n * 3 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hXn) (by omega)
  rw [← hK] at h2
  omega

/-- **Every child has a threshold**: `Next` can always be met. -/
theorem exists_next (hGo : G.Ok) (hB : 1 ≤ P.B) (hr : r.Good G) (hXn : r.X.card ≤ G.n)
    (hω : ∀ p < G.m, 8 * P.B * G.n ≤ G.pω p) : ∃ c', Next G P r c' := by
  by_cases hkeep : r.X.card ≤ 1 ∨ P.B * r.X.card * r.θ ≤ r.Δ G
  · exact ⟨r, Or.inl ⟨rfl, hkeep⟩⟩
  push Not at hkeep
  obtain ⟨hX, hlt⟩ := hkeep
  have hX : 2 ≤ r.X.card := hX
  set s := r.X.card with hs
  have h4 := θ_ge_four hB hr hX hXn hω hlt
  set U := r.θ / 4 with hU
  have hU1 : 1 ≤ U := by omega
  have hq1 : P.B * s * 1 ≤ (r.reset 1).Δ G := by
    set K := P.B * G.n with hK
    have e : 8 * P.B * G.n = 8 * K := by rw [hK]; ring
    have hK1 : 1 ≤ K := by
      have : 0 < G.n := by omega
      rw [hK]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    have := Δ_one hr.conn hX hω (M := 8 * P.B * G.n) (by omega)
    have : P.B * s ≤ K := Nat.mul_le_mul_left _ hXn
    omega
  classical
  set x := Nat.findGreatest (fun x => 1 ≤ x ∧ P.B * s * x ≤ (r.reset x).Δ G) U with hx
  have hxs : 1 ≤ x ∧ P.B * s * x ≤ (r.reset x).Δ G :=
    Nat.findGreatest_spec (P := fun x => 1 ≤ x ∧ P.B * s * x ≤ (r.reset x).Δ G) hU1 ⟨le_rfl, hq1⟩
  have hxU : x ≤ U := Nat.findGreatest_le U
  have hup : (r.reset x).Δ G ≤ 32 * P.B * s ^ 2 * x := by
    rcases Nat.lt_or_ge x U with hxl | hxe
    · have hfail := Nat.findGreatest_is_greatest (P := fun x => 1 ≤ x ∧ P.B * s * x ≤ (r.reset x).Δ G)
        (show x < x + 1 by omega) (by omega)
      push Not at hfail
      have hf := hfail (by omega)
      have hst := Δ_step hr.conn x
      rw [← hs] at hst
      -- `Δ(x) < (B + 1) s (x + 1) ≤ 4 B s x ≤ 32 B s² x`
      have e1 : P.B * s * (x + 1) + s * (x + 1) = (P.B + 1) * (s * (x + 1)) := by ring
      have e2 : (P.B + 1) * (s * (x + 1)) ≤ (2 * P.B) * (s * (2 * x)) :=
        Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (by omega))
      have e3 : (2 * P.B) * (s * (2 * x)) = 4 * (P.B * s * x) := by ring
      have e4 : 4 * (P.B * s * x) ≤ 32 * P.B * s ^ 2 * x := by
        have : P.B * s * x ≤ P.B * s * x * s := Nat.le_mul_of_pos_right _ (by omega)
        have e : 32 * P.B * s ^ 2 * x = 32 * (P.B * s * x * s) := by ring
        omega
      omega
    · have hxU' : x = U := le_antisymm hxU hxe
      have h1 := Δ_reset_le hGo hr (x := x)
      rw [← hs] at h1
      -- `Δ(x) ≤ 2 Δ + s θ < 3 B s θ ≤ 21 B s x`
      have hθ : r.θ ≤ 7 * x := by omega
      have h2 : s * r.θ ≤ P.B * s * r.θ := by
        calc s * r.θ = 1 * s * r.θ := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hB)
      have h3 : P.B * s * r.θ ≤ P.B * s * (7 * x) := Nat.mul_le_mul_left _ hθ
      have e4 : 3 * (P.B * s * (7 * x)) ≤ 32 * P.B * s ^ 2 * x := by
        have : P.B * s * x ≤ P.B * s * x * s := Nat.le_mul_of_pos_right _ (by omega)
        have e : 32 * P.B * s ^ 2 * x = 32 * (P.B * s * x * s) := by ring
        have e' : 3 * (P.B * s * (7 * x)) = 21 * (P.B * s * x) := by ring
        omega
      omega
  refine ⟨r.reset x, Or.inr ⟨hlt, rfl, rfl, rfl, rfl, rfl, show 4 * x ≤ r.θ by omega, hxs.1, Or.inr hxs.2, hup⟩⟩

end Cl

end MinCostFlow.LowStretch
