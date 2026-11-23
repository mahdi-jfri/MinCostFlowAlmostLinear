module

public import MinCostFlow.LowStretch.Grow

/-!
# Highways and petals exist

Every vertex of a connected cluster has a highway: a shortest walk to the center is one, since
every tail of a shortest walk is again shortest (`exists_highway`). Every far target has a petal:
region growing finds a radius (`Cl.exists_radius`). The target is in the petal and the center is
not, because the petal is reached from the target at cost at most `r`, which is less than the
distance of the target. So the highway leaves the petal, and its first exit is the portal
(`exists_petal`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

variable {G : PG} {P : Par}

namespace Cl

variable {c : Cl}

theorem hv_cons {a b p : ℕ} (rest : List ℕ) (hj : G.Joins p a b) (j : ℕ) :
    hv G a (p :: rest) (j + 1) = hv G b rest j := by
  simp [hv, PG.vtx, hj.other_eq]

theorem hv_cons_zero {a p : ℕ} (rest : List ℕ) : hv G a (p :: rest) 0 = a := by
  simp [hv, PG.vtx]

/-- A shortest walk to the center is a highway. -/
theorem highway_of_short (hc : c.Conn G) {z e : ℕ} {ps : List ℕ}
    (hw : G.IsWalk ↑c.X Set.univ z e ps) (he : e = c.x0)
    (hl : PG.wlen (c.len G) ps = c.d G c.x0 z) : c.IsHighway G z ps := by
  induction hw with
  | nil ha =>
    subst he
    exact ⟨.nil ha, fun i hi => absurd hi (by simp)⟩
  | @cons a b e p rest ha hp hj hrest ih =>
    subst he
    have hb : b ∈ c.X := hrest.start_mem
    have h1 : c.d G c.x0 b ≤ PG.wlen (c.len G) rest := by
      unfold d; rw [PG.dist_comm]; exact PG.dist_le hrest
    have h2 := d_le_add_len hc hj.symm hb ha
    simp only [PG.wlen_cons] at hl
    have h3 : PG.wlen (c.len G) rest = c.d G c.x0 b := by omega
    have ih' := ih rfl h3
    refine ⟨.cons ha hp hj hrest, fun i hi => ?_⟩
    cases i with
    | zero =>
      rw [hv_cons_zero, hv_cons rest hj, hv_zero]
      simp only [List.getD_cons_zero]
      omega
    | succ j =>
      rw [hv_cons rest hj, hv_cons rest hj]
      simp only [List.getD_cons_succ]
      exact ih'.2 j (by simpa using hi)

/-- Every vertex of a connected cluster has a highway. -/
theorem exists_highway (hc : c.Conn G) {z : ℕ} (hz : z ∈ c.X) : ∃ hw, c.IsHighway G z hw := by
  obtain ⟨ps, hps, hl⟩ := G.exists_walk_dist (c.len G) (hc.2 z hz).symm
  refine ⟨ps, highway_of_short hc hps rfl ?_⟩
  rw [hl]; unfold d; exact PG.dist_comm _ _ _ _

theorem carve_congr {Y : Finset ℕ} {pd pd' : PD} (h1 : pd.tj = pd'.tj) (h2 : pd.hw = pd'.hw)
    (h3 : pd.r = pd'.r) : c.carve G Y pd = c.carve G Y pd' := by
  obtain ⟨_, _, _, _⟩ := pd; obtain ⟨_, _, _, _⟩ := pd'
  simp only at h1 h2 h3; subst h1 h2 h3; rfl

theorem vol_congr {Y : Finset ℕ} {pd pd' : PD} (h1 : pd.tj = pd'.tj) (h2 : pd.hw = pd'.hw)
    (h3 : pd.r = pd'.r) : c.vol G P Y pd = c.vol G P Y pd' := by
  obtain ⟨_, _, _, _⟩ := pd; obtain ⟨_, _, _, _⟩ := pd'
  simp only at h1 h2 h3; subst h1 h2 h3; rfl

theorem cost_congr {Y : Finset ℕ} {pd pd' : PD} (h1 : pd.tj = pd'.tj) (h2 : pd.hw = pd'.hw)
    (h3 : pd.r = pd'.r) : c.cost G P Y pd = c.cost G P Y pd' := by
  obtain ⟨_, _, _, _⟩ := pd; obtain ⟨_, _, _, _⟩ := pd'
  simp only at h1 h2 h3; subst h1 h2 h3; rfl

/-- **A petal exists** for every target that is far enough. -/
theorem exists_petal (hGo : G.Ok) (hc : c.Conn G) {Y : Finset ℕ} (hY : Y ⊆ c.X) {tj : ℕ}
    {hw : List ℕ} (htj : tj ∈ Y) (hh : c.IsHighway G tj hw) (lo : ℕ)
    (hfar : lo + c.Δ G / 8 < c.d G c.x0 tj) (hκ : 1 ≤ P.κ) (hL : 1 ≤ P.L)
    (hΔ : 8 * P.L * (lam P 0 + 3) ≤ c.Δ G) (hV : c.V G P ≤ 2 ^ lam P 0 * P.κ) :
    ∃ pd : PD, pd.tj = tj ∧ pd.hw = hw ∧ c.PetalOk G P Y lo pd := by
  classical
  let pd0 : PD := ⟨tj, hw, 0, 0⟩
  obtain ⟨r, q, hq1, hqL, ha, hb, hcost, hvol⟩ := exists_radius hGo hc hY pd0 lo hκ hL hΔ hV
  have hr : r ≤ lo + c.Δ G / 8 := by
    have h1 : q * c.bw G P ≤ P.L * c.bw G P := Nat.mul_le_mul_right _ hqL
    have h2 := L_mul_bw_le (G := G) (P := P) (c := c)
    omega
  -- the carved set does not depend on the portal index
  set W := c.carve G Y (pd0.withR r) with hW
  have htW : tj ∈ W := mem_carve.mpr ⟨htj, 0, Nat.zero_le _, .start (by simpa using htj)⟩
  have hx0 : c.x0 ∉ W := by
    intro h
    obtain ⟨-, k, hk, hdr⟩ := mem_carve.mp h
    have := potential hc (Finset.coe_subset.mpr hY) hh hdr
    have h0 : c.d G c.x0 c.x0 = 0 := PG.dist_self (by simpa using hc.1)
    simp only [PD.withR_r] at hk
    omega
  have hlen : hv G tj hw hw.length = c.x0 := hh.hv_length
  have hne : 0 < hw.length := by
    by_contra h0
    have : hw = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [show ([] : List ℕ).length = 0 from rfl, hv_zero] at hlen
    exact hx0 (hlen ▸ htW)
  have hex : ∃ j, hv G tj hw (j + 1) ∉ W := ⟨hw.length - 1, by
    rw [Nat.sub_add_cancel hne, hlen]; exact hx0⟩
  set i := Nat.find hex with hi
  have hiW : hv G tj hw (i + 1) ∉ W := Nat.find_spec hex
  have hile : i < hw.length := by
    have := Nat.find_min' hex (show hv G tj hw (hw.length - 1 + 1) ∉ W by
      rw [Nat.sub_add_cancel hne, hlen]; exact hx0)
    omega
  have hin : ∀ k ≤ i, hv G tj hw k ∈ W := by
    intro k hk
    cases k with
    | zero => rw [hv_zero]; exact htW
    | succ j =>
      have := Nat.find_min hex (show j < i by omega)
      push Not at this
      exact this
  let pd : PD := ⟨tj, hw, r, i⟩
  have hcv : c.carve G Y pd = W := carve_congr rfl rfl rfl
  refine ⟨pd, rfl, rfl, htj, hh, hile, fun k hk => by rw [hcv]; exact hin k hk,
    by rw [hcv]; exact hiW, q, hq1, hqL, ha, hb, ?_, ?_⟩
  · rw [cost_congr (pd := pd) (pd' := pd0.withR r) rfl rfl rfl,
      vol_congr (pd := pd) (pd' := pd0.withR r) rfl rfl rfl]
    exact hcost
  · rw [vol_congr (pd := pd) (pd' := pd0.withR r) rfl rfl rfl]
    exact hvol

end Cl

end MinCostFlow.LowStretch
