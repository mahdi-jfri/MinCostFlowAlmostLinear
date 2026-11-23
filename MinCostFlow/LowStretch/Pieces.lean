module

public import MinCostFlow.LowStretch.Segments

/-!
# The pieces of one step

Fix a cluster `c` with radius `Δ > 0` and a decomposition `D` that follows the rules
`Cl.DecOk`. The petals and the stem split `X`: petal `k` is carved from `Z k`, and `Z k` is the
union of the stem and the petals `k, k + 1, …`. This file shows:
* a regular petal has only vertices `z` with `8 d(x0, z) > 5Δ`, and the special petal only
  vertices with `2 d(x0, z) ≥ Δ` (Claim 5 of [AN19]);
* the outer end of the special portal has `8 d(x0, y) + 4 ≤ 5Δ`, so it lies in the stem
  (Claim 7);
* the center lies in the stem, and the highway of `c` lies in the stem, except for its part up to
  the special portal, which lies in the special petal (Claim 8).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Cl

variable {G : PG} {P : Par} {c : Cl} {D : Dec}

/-- The start of the range of petal `k`. -/
noncomputable def lo (G : PG) (c : Cl) (D : Dec) (k : ℕ) : ℕ :=
  if D.sp = true ∧ k = 0 then c.loS G else 0

theorem petalOk (hD : c.DecOk G P D) {k : ℕ} (hk : k < D.ps.length) :
    c.PetalOk G P (c.Z G D k) (c.lo G D k) (D.pd k) := by
  unfold lo
  split_ifs with hs
  · obtain ⟨h1, rfl⟩ := hs
    exact (hD.2.1 h1).2.2.2
  · exact (hD.2.2.1 k hk fun h => fun hk0 => hs ⟨h, hk0⟩).2

theorem far_reg (hc : c.Conn G) (hD : c.DecOk G P D) {k : ℕ} (hk : k < D.ps.length)
    (hs : ¬ (D.sp = true ∧ k = 0)) {z : ℕ} (hz : z ∈ c.W G D k) :
    5 * c.Δ G < 8 * c.d G c.x0 z := by
  have h1 := (hD.2.2.1 k hk fun h hk0 => hs ⟨h, hk0⟩).1
  have hp := petalOk hD hk
  have h2 := d_tj_le hc (closed_Z D k) hp hz
  have h3 := r_le hp
  unfold lo at h3
  simp only [hs, ↓reduceIte] at h3
  omega

theorem far_sp (hc : c.Conn G) (hD : c.DecOk G P D) (hs : D.sp = true) {z : ℕ}
    (hz : z ∈ c.W G D 0) : c.Δ G ≤ 2 * c.d G c.x0 z := by
  have hsp := hD.2.1 hs
  have h0 := hD.1.mp hs
  have hp := petalOk hD hsp.1
  have h2 := d_tj_le hc (closed_Z D 0) hp hz
  have h3 := r_le hp
  unfold lo loS at h3
  simp only [hs, and_self, ↓reduceIte] at h3
  rw [hsp.2.1] at h2
  omega

/-- The outer end of the special portal is near the center. -/
theorem out_sp (hD : c.DecOk G P D) (hs : D.sp = true) :
    8 * c.d G c.x0 (D.yc G 0) + 4 ≤ 5 * c.Δ G := by
  have hsp := hD.2.1 hs
  have h0 := hD.1.mp hs
  have hp := petalOk hD hsp.1
  have h1 := r_lt_out (closed_Z D 0) hp
  obtain ⟨q, hq1, -, hlo, -⟩ := hp.2.2.2.2.2
  unfold lo loS at hlo
  simp only [hs, and_self, ↓reduceIte] at hlo
  rw [hsp.2.1] at h1
  unfold Dec.yc
  rw [hsp.2.1]
  omega

theorem W_subset_Z {j k : ℕ} (h : j ≤ k) : c.W G D k ⊆ c.Z G D j :=
  (W_subset D k).trans (Z_antitone D h)

theorem stem_subset_Z (k : ℕ) (hk : k ≤ D.ps.length) : c.stem G D ⊆ c.Z G D k :=
  Z_antitone D hk

/-- A vertex of `Z k` that is in none of the petals `k, k + 1, …` is in the stem. -/
theorem mem_stem_of {k : ℕ} {z : ℕ} (hz : z ∈ c.Z G D k)
    (hW : ∀ j, k ≤ j → j < D.ps.length → z ∉ c.W G D j) : z ∈ c.stem G D := by
  unfold stem
  by_cases hk : k ≤ D.ps.length
  · obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hk
    clear hk
    induction n generalizing k with
    | zero => simpa [hn] using hz
    | succ n ih =>
      refine ih (k := k + 1) ?_ (fun j hj hjl => hW j (by omega) hjl) (by omega)
      rw [Z_succ]
      exact Finset.mem_sdiff.mpr ⟨hz, hW k le_rfl (by omega)⟩
  · have : c.Z G D k ⊆ c.Z G D D.ps.length := by
      have hle : D.ps.length ≤ k := by omega
      clear hz hW hk
      induction k, hle using Nat.le_induction with
      | base => exact subset_rfl
      | succ k _ ih => exact (Z_antitone D (Nat.le_succ k)).trans ih
    exact this hz

/-- `Z k` is the stem together with the petals `k, k + 1, …`. -/
theorem mem_Z_iff {k z : ℕ} (hk : k ≤ D.ps.length) :
    z ∈ c.Z G D k ↔ z ∈ c.stem G D ∨ ∃ j, k ≤ j ∧ j < D.ps.length ∧ z ∈ c.W G D j := by
  constructor
  · intro hz
    by_contra hne
    push Not at hne
    exact hne.1 (mem_stem_of hz fun j hj hjl hzj => hne.2 j hj hjl hzj)
  · rintro (h | ⟨j, hj, -, h⟩)
    · exact stem_subset_Z k hk h
    · exact W_subset_Z hj h

theorem W_disj {j k : ℕ} (hjk : j < k) {z : ℕ} (hj : z ∈ c.W G D j) (hk : z ∈ c.W G D k) :
    False := by
  have := W_subset_Z (G := G) (c := c) (D := D) (show j + 1 ≤ k by omega) hk
  rw [Z_succ] at this
  exact (Finset.mem_sdiff.mp this).2 hj

theorem stem_disj {k : ℕ} (hk : k < D.ps.length) {z : ℕ} (hs : z ∈ c.stem G D)
    (hz : z ∈ c.W G D k) : False := by
  have := stem_subset_Z (G := G) (c := c) (D := D) (k + 1) (by omega) hs
  rw [Z_succ] at this
  exact (Finset.mem_sdiff.mp this).2 hz

theorem stem_subset_X : c.stem G D ⊆ c.X := Z_subset_X D _

theorem W_subset_X (k : ℕ) : c.W G D k ⊆ c.X := (W_subset D k).trans (Z_subset_X D k)

/-- The center lies in the stem. -/
theorem x0_mem_stem (hc : c.Conn G) (hD : c.DecOk G P D) (hΔ : 0 < c.Δ G) :
    c.x0 ∈ c.stem G D := by
  refine mem_stem_of (k := 0) hc.1 fun j _ hj hz => ?_
  have hd : c.d G c.x0 c.x0 = 0 := PG.dist_self (by simpa using hc.1)
  by_cases hs : D.sp = true ∧ j = 0
  · obtain ⟨hs, rfl⟩ := hs
    have := far_sp hc hD hs hz
    omega
  · have := far_reg hc hD hj hs hz
    omega

theorem xc_mem (hD : c.DecOk G P D) {k : ℕ} (hk : k < D.ps.length) :
    D.xc G k ∈ c.W G D k := (petalOk hD hk).2.2.2.1 _ le_rfl

theorem yc_mem (hD : c.DecOk G P D) {k : ℕ} (hk : k < D.ps.length) :
    D.yc G k ∈ c.Z G D (k + 1) := by
  rw [Z_succ]
  have hp := petalOk hD hk
  exact hv_mem_rest (closed_Z D k) hp le_rfl hp.2.2.1

/-- The outer end of the special portal lies in the stem. -/
theorem yc_sp_mem_stem (hc : c.Conn G) (hD : c.DecOk G P D) (hs : D.sp = true) :
    D.yc G 0 ∈ c.stem G D := by
  have hsp := hD.2.1 hs
  refine mem_stem_of (yc_mem hD hsp.1) fun j hj hjl hz => ?_
  have := far_reg hc hD hjl (by omega) hz
  have := out_sp hD hs
  omega

/-- Where the highway of the cluster lies: in the stem, except for its part up to the special
portal, which lies in the special petal. -/
theorem hw_mem (hc : c.Conn G) (hh : c.IsHighway G c.t c.hw) (hD : c.DecOk G P D) {m : ℕ}
    (hm : m ≤ c.hw.length) :
    (D.sp = true ∧ m ≤ (D.pd 0).i ∧ hv G c.t c.hw m ∈ c.W G D 0) ∨
      (¬ (D.sp = true ∧ m ≤ (D.pd 0).i) ∧ hv G c.t c.hw m ∈ c.stem G D) := by
  by_cases hs : D.sp = true
  · have hsp := hD.2.1 hs
    have hp := petalOk hD hsp.1
    by_cases hmi : m ≤ (D.pd 0).i
    · left
      refine ⟨hs, hmi, ?_⟩
      have := hp.2.2.2.1 m hmi
      rwa [hsp.2.1, hsp.2.2.1] at this
    · right
      refine ⟨fun h => hmi h.2, ?_⟩
      have hy := yc_sp_mem_stem hc hD hs
      unfold Dec.yc at hy
      rw [hsp.2.1, hsp.2.2.1] at hy
      have hil := hp.2.2.1
      rw [hsp.2.2.1] at hil
      exact (closed_Z D _).hv_mem hh hy m (by omega) hm
  · right
    refine ⟨fun h => hs h.1, ?_⟩
    have h0 : 8 * c.d G c.x0 c.t ≤ 5 * c.Δ G := by
      by_contra h; exact hs (hD.1.mpr (by omega))
    have ht : c.t ∈ c.stem G D := by
      have ht0 : c.t ∈ c.Z G D 0 := by
        have := hh.hv_mem (i := 0) (Nat.zero_le _)
        rw [hv_zero] at this; exact this
      refine mem_stem_of ht0 fun j _ hj hz => ?_
      have := far_reg hc hD hj (fun h => hs h.1) hz
      omega
    exact (closed_Z D _).hv_mem hh (i := 0) (by rw [hv_zero]; exact ht) m (Nat.zero_le _) hm

/-- No vertex of the highway of the cluster lies in a regular petal. -/
theorem hw_not_mem_reg (hc : c.Conn G) (hh : c.IsHighway G c.t c.hw) (hD : c.DecOk G P D)
    {m : ℕ} (hm : m ≤ c.hw.length) {k : ℕ} (hk : k < D.ps.length)
    (hs : ¬ (D.sp = true ∧ k = 0)) : hv G c.t c.hw m ∉ c.W G D k := by
  intro hz
  rcases hw_mem hc hh hD hm with ⟨h1, -, h2⟩ | ⟨-, h2⟩
  · have hk0 : k ≠ 0 := fun h => hs ⟨h1, h⟩
    exact W_disj (show 0 < k by omega) h2 hz
  · exact stem_disj hk h2 hz

end Cl

end MinCostFlow.LowStretch
