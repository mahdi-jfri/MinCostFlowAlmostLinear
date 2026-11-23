module

public import MinCostFlow.LowStretch.Light
public import Mathlib.Tactic.Ring

/-!
# Radii, thresholds and volumes from a cluster to its children

* A reset child has distances at most twice those before the reset, plus `|X| · θ`.
* The product `Δ · θ` shrinks by a factor `3/4` from a cluster to each child. So a pair is active
  (`Cl.Active`) only while this product is in a window of ratio `n^O(1)`, which takes `O(log n)`
  levels.
* An active pair that leaves a petal does so before the radius passes its far end, so it adds at
  most its volume weight to the volume of the petal.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

variable {G : PG} {P : Par}

namespace Cl

/-- A cluster with the same vertices and center as a good cluster `r` has distances at most
`2 d_r + |X| · θ_r`, whatever its threshold and halved pairs. -/
theorem d_le_two_of (hGo : G.Ok) {r c' : Cl} (hr : r.Good G) (hX : c'.X = r.X)
    (hx : c'.x0 = r.x0) {y : ℕ} (hy : y ∈ r.X) :
    c'.d G c'.x0 y ≤ 2 * r.d G r.x0 y + r.X.card * r.θ := by
  obtain ⟨ps, hps, hl⟩ := G.exists_walk_dist (r.len G) (hr.conn.2 y hy)
  have := d_le_of_walk (c' := c') (f := fun p => 2 * r.len G p) (θ := r.θ)
    (a := c'.x0) (b := y) (ps := ps) (by rw [hX, hx]; exact hps) (fun p _ => by
      have h1 := len_le (c := c') (G := G) p
      have he := PG.pω_even hGo p
      by_cases hl : G.pω p < r.θ
      · omega
      · have := half_le_len (c := r) (G := G) (p := p) (by omega)
        omega)
  rw [PG.wlen_mul, hl, hX] at this
  exact this

end Cl

theorem Next.Δ_le (hGo : G.Ok) {r c' : Cl} (hn : Next G P r c') (hr : r.Good G) :
    c'.Δ G ≤ 2 * r.Δ G + r.X.card * r.θ := by
  have hX := hn.X_eq
  have hx := hn.x0_eq
  unfold Cl.Δ
  refine Finset.sup_le fun y hy => ?_
  rw [hX] at hy
  have h1 := Cl.d_le_two_of hGo hr hX hx hy
  have h2 := Cl.d_le_Δ (c := r) (G := G) hy
  unfold Cl.Δ at h2
  omega

namespace Cl

variable {c : Cl} {D : Dec}

/-- The product of radius and threshold shrinks by a factor `3/4` from a cluster to each child. -/
theorem psi_child (hGo : G.Ok) (hB : 1 ≤ P.B) (hc : c.Inv G P) (hX : 2 ≤ c.X.card)
    (hD : c.DecOk G P D) {k : ℕ} (hk : k < D.nch) {c' : Cl} (hn : Next G P (c.raw G D k) c') :
    4 * (c'.Δ G * c'.θ) ≤ 3 * (c.Δ G * c.θ) := by
  have hr := raw_Δ hc.good hD hGo hk
  have hθ := raw_θ (G := G) (c := c) (D := D) k
  have hgood := raw_good hc.good hD (hc.Δ_pos hB hX) hGo hk
  have hΔ' := Next.Δ_le hGo hn hgood
  have hcard : (c.raw G D k).X.card ≤ c.X.card := Finset.card_le_card (raw_X_subset k)
  have hbig : P.B * c.X.card * c.θ ≤ c.Δ G := hc.big.resolve_left (by omega)
  rcases hn with ⟨rfl, -⟩ | ⟨-, -, -, -, -, -, h4, -⟩
  · rw [hθ]
    have := Nat.mul_le_mul_right c.θ hr
    have e1 : 4 * (c.raw G D k).Δ G * c.θ = 4 * ((c.raw G D k).Δ G * c.θ) := by ring
    have e2 : 3 * c.Δ G * c.θ = 3 * (c.Δ G * c.θ) := by ring
    omega
  · rw [hθ] at h4 hΔ'
    have h5 : (c.raw G D k).X.card * c.θ ≤ c.Δ G := by
      have h1 := Nat.mul_le_mul_right c.θ hcard
      have h2 : c.X.card * c.θ ≤ P.B * c.X.card * c.θ :=
        calc c.X.card * c.θ = 1 * c.X.card * c.θ := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hB)
      omega
    have h6 : 2 * c'.Δ G ≤ 5 * c.Δ G := by omega
    have h7 := Nat.mul_le_mul_left (c'.Δ G) h4
    have h8 := Nat.mul_le_mul_right c.θ h6
    have e1 : c'.Δ G * (4 * c'.θ) = 4 * (c'.Δ G * c'.θ) := by ring
    have e2 : 2 * c'.Δ G * c.θ = 2 * (c'.Δ G * c.θ) := by ring
    have e3 : 5 * c.Δ G * c.θ = 5 * (c.Δ G * c.θ) := by ring
    omega

end Cl

end MinCostFlow.LowStretch
