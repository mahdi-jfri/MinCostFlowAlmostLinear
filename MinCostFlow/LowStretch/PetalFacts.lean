module

public import MinCostFlow.LowStretch.Closed

/-!
# Facts about one petal

Fix a cluster `c` and a petal `pd` carved from a closed set `Y` by the rules `Cl.PetalOk`. Write
`W` for the petal, `h_k` for vertex number `k` of its highway, and `i` for the index of its
portal. This file shows:
* the whole highway lies in `Y`, its vertices up to `h_i` lie in `W`, and the ones after lie in
  `Y \ W` (so the highway leaves the petal once and for all);
* every vertex `z` of the petal has `d(x0, t_j) ≤ r + d(x0, z)`, and `r ≤ lo + Δ/8`;
* the portal pair is not light, and `d(x0, t_j) - d(x0, h_(i+1)) > r`;
* inequality (14) of [AN19]: every vertex `z` of the petal is reached from some `h_(i')` with
  `i' ≤ i` by a walk `S` inside the petal with small excess.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Cl

variable {G : PG} {P : Par} {c : Cl}

theorem coe_carve (Y : Finset ℕ) (pd : PD) :
    (↑(c.carve G Y pd) : Set ℕ) = c.Petal G pd.tj pd.hw ↑Y pd.r := by
  ext v
  simp only [Finset.mem_coe, mem_carve]
  exact ⟨fun h => h.2, fun h => ⟨Petal.subset h, h⟩⟩

theorem hv_mem_Y {Y : Finset ℕ} {lo : ℕ} {pd : PD} (hY : c.Closed G Y)
    (hp : c.PetalOk G P Y lo pd) {k : ℕ} (hk : k ≤ pd.hw.length) :
    hv G pd.tj pd.hw k ∈ Y :=
  hY.hv_mem hp.2.1 (i := 0) (by rw [hv_zero]; exact hp.1) k (Nat.zero_le _) hk

theorem hv_mem_rest {Y : Finset ℕ} {lo : ℕ} {pd : PD} (hY : c.Closed G Y)
    (hp : c.PetalOk G P Y lo pd) {k : ℕ} (hik : pd.i + 1 ≤ k) (hk : k ≤ pd.hw.length) :
    hv G pd.tj pd.hw k ∈ Y \ c.carve G Y pd := by
  refine (hY.sdiff pd).hv_mem hp.2.1 (i := pd.i + 1) ?_ k hik hk
  exact Finset.mem_sdiff.mpr ⟨hv_mem_Y hY hp hp.2.2.1, hp.2.2.2.2.1⟩

theorem hv_not_mem {Y : Finset ℕ} {lo : ℕ} {pd : PD} (hY : c.Closed G Y)
    (hp : c.PetalOk G P Y lo pd) {k : ℕ} (hik : pd.i + 1 ≤ k) (hk : k ≤ pd.hw.length) :
    hv G pd.tj pd.hw k ∉ c.carve G Y pd :=
  (Finset.mem_sdiff.mp (hv_mem_rest hY hp hik hk)).2

/-- Every vertex of the petal is not much closer to the center than the target. -/
theorem d_tj_le {Y : Finset ℕ} {lo : ℕ} {pd : PD} (hc : c.Conn G) (hY : c.Closed G Y)
    (hp : c.PetalOk G P Y lo pd) {z : ℕ} (hz : z ∈ c.carve G Y pd) :
    c.d G c.x0 pd.tj ≤ pd.r + c.d G c.x0 z := by
  obtain ⟨-, k, hk, hdr⟩ := mem_carve.mp hz
  have := potential hc (Finset.coe_subset.mpr hY.1) hp.2.1 hdr
  omega

theorem L_mul_bw_le : P.L * c.bw G P ≤ c.Δ G / 8 := by
  unfold bw
  exact Nat.mul_div_le _ _

theorem r_le {Y : Finset ℕ} {lo : ℕ} {pd : PD} (hp : c.PetalOk G P Y lo pd) :
    pd.r ≤ lo + c.Δ G / 8 := by
  obtain ⟨q, -, hqL, -, hr, -⟩ := hp.2.2.2.2.2
  have h1 : q * c.bw G P ≤ P.L * c.bw G P := Nat.mul_le_mul_right _ hqL
  have h2 := L_mul_bw_le (G := G) (P := P) (c := c)
  omega

/-- The portal is not light: a light pair costs nothing on the highway, so the petal would go on
along it. -/
theorem portal_not_light {Y : Finset ℕ} {lo : ℕ} {pd : PD} (hY : c.Closed G Y)
    (hp : c.PetalOk G P Y lo pd) : c.θ ≤ G.pω (pd.hw.getD pd.i 0) := by
  by_contra hlt
  have h0 : c.len G (pd.hw.getD pd.i 0) = 0 := len_eq_zero_of_light (by omega)
  obtain ⟨-, k, hk, hdr⟩ := mem_carve.mp (hp.2.2.2.1 pd.i le_rfl)
  have hY1 : hv G pd.tj pd.hw (pd.i + 1) ∈ Y := hv_mem_Y hY hp hp.2.2.1
  have := DR.step hdr (Arc.high (c := c) (G := G) hp.2.2.1) (by simpa using hY1)
  rw [h0, Nat.add_zero] at this
  exact hp.2.2.2.2.1 (mem_carve.mpr ⟨hY1, k, hk, this⟩)

/-- The outer end of the portal is too far from the target along the highway. -/
theorem r_lt_out {Y : Finset ℕ} {lo : ℕ} {pd : PD} (hY : c.Closed G Y)
    (hp : c.PetalOk G P Y lo pd) :
    pd.r < c.d G c.x0 pd.tj - c.d G c.x0 (hv G pd.tj pd.hw (pd.i + 1)) := by
  by_contra hle
  have := dr_hv hp.2.1 (Y := ↑Y) (i := pd.i + 1) hp.2.2.1
    (fun j hj => by simpa using hv_mem_Y hY hp (k := j) (by have := hp.2.2.1; omega))
  refine hp.2.2.2.2.1 (mem_carve.mpr ⟨hv_mem_Y hY hp hp.2.2.1, _, by omega, this⟩)

/-- Inequality (14) of [AN19] for the petal. -/
theorem excess {Y : Finset ℕ} {lo : ℕ} {pd : PD} (hc : c.Conn G) (hY : c.Closed G Y)
    (hp : c.PetalOk G P Y lo pd) {z : ℕ} (hz : z ∈ c.carve G Y pd) :
    ∃ i' ≤ pd.i, ∃ S, G.IsWalk ↑(c.carve G Y pd) Set.univ (hv G pd.tj pd.hw i') z S ∧
      (c.d G c.x0 pd.tj - c.d G c.x0 (hv G pd.tj pd.hw i')) + 2 * PG.wlen (c.len G) S +
        2 * c.d G c.x0 (hv G pd.tj pd.hw i') ≤ pd.r + 2 * c.d G c.x0 z := by
  obtain ⟨-, k, hk, hdr⟩ := mem_carve.mp hz
  obtain ⟨i', hi', S, hS, hineq⟩ :=
    exists_excess hc (Finset.coe_subset.mpr hY.1) hp.2.1 hdr
  have hS' : G.IsWalk ↑(c.carve G Y pd) Set.univ (hv G pd.tj pd.hw i') z S := by
    rw [coe_carve]; exact hS.mono (Petal.mono hk) le_rfl
  refine ⟨i', ?_, S, hS', by omega⟩
  by_contra hlt
  exact hv_not_mem hY hp (by omega) hi' (by simpa using hS'.start_mem)

end Cl

end MinCostFlow.LowStretch
