module

public import MinCostFlow.LowStretch.ChildPetal2
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# The invariant of a run

Every cluster of a run is good, has a threshold at least `1`, and is either a single vertex or has
radius at least `B · |X| · θ`. A cluster with two or more vertices therefore has a positive radius.
This file shows that the children of such a cluster keep the invariant, and it collects the facts
about the pieces of a step that the tree needs: they lie in `X`, they are disjoint, and their sizes
add up to `|X|`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

variable {G : PG} {P : Par}

namespace Cl

variable (G P) in
/-- The invariant of the clusters of a run. -/
structure Inv (c : Cl) : Prop where
  good : c.Good G
  one_le : 1 ≤ c.θ
  big : c.X.card ≤ 1 ∨ P.B * c.X.card * c.θ ≤ c.Δ G
  small : c.Δ G ≤ 32 * P.B * G.n ^ 2 * c.θ
  sub : c.X ⊆ Finset.range G.n

theorem Inv.Δ_pos {c : Cl} (h : c.Inv G P) (hB : 1 ≤ P.B) (hX : 2 ≤ c.X.card) : 0 < c.Δ G := by
  rcases h.big with h1 | h1
  · omega
  · have : 1 * 2 * 1 ≤ P.B * c.X.card * c.θ :=
      Nat.mul_le_mul (Nat.mul_le_mul hB hX) h.one_le
    omega

end Cl

theorem Next.X_eq {r c' : Cl} (h : Next G P r c') : c'.X = r.X := by
  rcases h with ⟨rfl, -⟩ | h
  · rfl
  · exact h.2.1

theorem Next.x0_eq {r c' : Cl} (h : Next G P r c') : c'.x0 = r.x0 := by
  rcases h with ⟨rfl, -⟩ | h
  · rfl
  · exact h.2.2.1

/-- A child that follows `Next` from a good cluster with threshold at least `1` keeps the
invariant. -/
theorem Next.inv {r c' : Cl} (h : Next G P r c') (hr : r.Good G) (hθ : 1 ≤ r.θ)
    (hs : r.Δ G ≤ 32 * P.B * G.n ^ 2 * r.θ) (hsub : r.X ⊆ Finset.range G.n) : c'.Inv G P := by
  rcases h with ⟨rfl, hb⟩ | ⟨-, hX, hx, ht, hh, hw, -, h1, hb, hs'⟩
  · exact ⟨hr, hθ, hb, hs, hsub⟩
  · have hcard : r.X.card ≤ G.n := by
      simpa using Finset.card_le_card hsub
    have : r.X.card ^ 2 ≤ G.n ^ 2 := Nat.pow_le_pow_left hcard 2
    have : 32 * P.B * r.X.card ^ 2 * c'.θ ≤ 32 * P.B * G.n ^ 2 * c'.θ :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)
    refine ⟨⟨?_, ?_, ?_⟩, h1, by rw [hX]; exact hb, by omega, by rw [hX]; exact hsub⟩
    · unfold Cl.Conn; rw [hX, hx]; exact hr.conn
    · rw [ht, hw, ← hx]
      exact ⟨.nil (by rw [hX, hx]; exact hr.conn.1), fun i hi => by simp at hi⟩
    · intro p hp; rw [hh] at hp; simp at hp

namespace Cl

variable {c : Cl} {D : Dec}

theorem raw_good (hc : c.Good G) (hD : c.DecOk G P D) (hΔ : 0 < c.Δ G) (hGo : G.Ok) {k : ℕ}
    (hk : k < D.nch) : (c.raw G D k).Good G := by
  cases k with
  | zero => exact raw0_good hc hD hΔ
  | succ k => exact rawP_good hc hD (by unfold Dec.nch at hk; omega) hGo

theorem raw_θ (k : ℕ) : (c.raw G D k).θ = c.θ := by
  cases k with
  | zero => exact raw0_θ
  | succ k => rfl

theorem raw_Δ (hc : c.Good G) (hD : c.DecOk G P D) (hGo : G.Ok) {k : ℕ}
    (hk : k < D.nch) : 4 * (c.raw G D k).Δ G ≤ 3 * c.Δ G := by
  cases k with
  | zero => exact raw0_Δ hc.conn hD
  | succ k => exact rawP_Δ hc hD (by unfold Dec.nch at hk; omega) hGo

/-! ### The pieces -/

theorem raw_X_subset (k : ℕ) : (c.raw G D k).X ⊆ c.X := by
  cases k with
  | zero => rw [raw0_X]; exact stem_subset_X
  | succ k => exact W_subset_X k

/-- The pieces are disjoint. -/
theorem raw_disj {j k : ℕ} (hk : k < D.nch) (hjk : j < k) {z : ℕ} (hj : z ∈ (c.raw G D j).X)
    (hk' : z ∈ (c.raw G D k).X) : False := by
  unfold Dec.nch at hk
  cases k with
  | zero => omega
  | succ k =>
    cases j with
    | zero => rw [raw0_X] at hj; exact stem_disj (by omega) hj hk'
    | succ j => exact W_disj (by omega) hj hk'

theorem card_Z {k : ℕ} (hk : k ≤ D.ps.length) :
    (c.Z G D k).card = (c.stem G D).card +
      ∑ j ∈ Finset.Ico k D.ps.length, (c.W G D j).card := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hk
  induction n generalizing k with
  | zero => subst hn; simp [stem]
  | succ n ih =>
    have h1 := ih (k := k + 1) (by omega) (by omega)
    have h2 : (c.Z G D (k + 1)).card + (c.W G D k).card = (c.Z G D k).card := by
      rw [Z_succ]; exact Finset.card_sdiff_add_card_eq_card (W_subset D k)
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    omega

/-- The sizes of the pieces add up to `|X|`. -/
theorem sum_card_raw :
    ∑ k ∈ Finset.range D.nch, (c.raw G D k).X.card = c.X.card := by
  unfold Dec.nch
  rw [Finset.sum_range_succ', raw0_X]
  have := card_Z (c := c) (G := G) (D := D) (k := 0) (Nat.zero_le _)
  rw [Finset.range_eq_Ico] at *
  simp only [rawP_X]
  have e : c.Z G D 0 = c.X := rfl
  rw [e] at this
  omega

/-- The children of a cluster of a run keep the invariant. -/
theorem child_inv (hGo : G.Ok) (hB : 1 ≤ P.B) (hc : c.Inv G P) (hX : 2 ≤ c.X.card)
    (hD : c.DecOk G P D) {k : ℕ} (hk : k < D.nch) {c' : Cl} (hn : Next G P (c.raw G D k) c') :
    c'.Inv G P := by
  have hΔ := hc.Δ_pos hB hX
  refine hn.inv (raw_good hc.good hD hΔ hGo hk) (by rw [raw_θ]; exact hc.one_le) ?_
    ((raw_X_subset k).trans hc.sub)
  have := raw_Δ hc.good hD hGo hk
  have := hc.small
  rw [raw_θ]
  omega

end Cl

end MinCostFlow.LowStretch
