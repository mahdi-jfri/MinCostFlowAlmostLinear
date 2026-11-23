module

public import MinCostFlow.LowStretch.ChildPetal

/-!
# The petal children are good, and small

Each petal child is good: it is connected (every vertex is reached from a highway vertex inside
the petal, by inequality (14)), its highway is a shortest walk to its center, and its halved pairs
that are not light lie on its highway. Its radius is at most `3/4` of the radius of the cluster
(Claim 6 of [AN19]). We also prove the two inequalities that the bound on the radius of the tree
uses.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Cl

variable {G : PG} {P : Par} {c : Cl} {D : Dec}

section petal

variable (hG : c.Good G) (hD : c.DecOk G P D) {k : ℕ} (hk : k < D.ps.length)
include hG hD hk

theorem rawP_reach {z : ℕ} (hz : z ∈ c.W G D k) :
    ∃ i' ≤ (D.pd k).i, ∃ S, G.IsWalk ↑(c.W G D k) Set.univ (hv G (D.pd k).tj (D.pd k).hw i') z S ∧
      G.Reach ↑(c.W G D k) (D.xc G k) (hv G (D.pd k).tj (D.pd k).hw i') ∧
      (c.d G c.x0 (D.pd k).tj - c.d G c.x0 (hv G (D.pd k).tj (D.pd k).hw i')) +
        2 * PG.wlen (c.len G) S + 2 * c.d G c.x0 (hv G (D.pd k).tj (D.pd k).hw i') ≤
        (D.pd k).r + 2 * c.d G c.x0 z := by
  obtain ⟨i', hi', S, hS, hineq⟩ := excess hG.conn (closed_Z D k) (petalOk hD hk) hz
  exact ⟨i', hi', S, hS, ⟨_, seg_walk_rawP hD hk hi'⟩, hineq⟩

theorem rawP_conn : (c.raw G D (k + 1)).Conn G := by
  refine ⟨xc_mem hD hk, fun z hz => ?_⟩
  rw [rawP_X] at hz
  obtain ⟨i', -, S, hS, hr, -⟩ := rawP_reach hG hD hk hz
  rw [rawP_X, rawP_x0]
  exact hr.trans ⟨S, hS⟩

theorem rawP_high (hGo : G.Ok) :
    (c.raw G D (k + 1)).IsHighway G (c.raw G D (k + 1)).t (c.raw G D (k + 1)).hw := by
  have hpk := petalOk hD hk
  have hil := hpk.2.2.1
  have hlen : ((D.pd k).hw.take (D.pd k).i).length = (D.pd k).i := by
    rw [List.length_take]; omega
  have hhv : ∀ m ≤ (D.pd k).i, hv G (D.pd k).tj ((D.pd k).hw.take (D.pd k).i) m =
      hv G (D.pd k).tj (D.pd k).hw m := fun m hm => PG.getD_vtx_take hm
  refine ⟨?_, fun m hm => ?_⟩
  · rw [rawP_X, rawP_x0, rawP_t, rawP_hw]
    have hw := hpk.2.1.1.take (D.pd k).i hil.le
    refine hw.restrict fun x hx => ?_
    obtain ⟨m, hm1, -, rfl⟩ := PG.mem_vtx_take hx
    exact hpk.2.2.2.1 m hm1
  · rw [rawP_hw, hlen] at hm
    rw [rawP_t, rawP_hw, rawP_x0, hhv m hm.le, hhv (m + 1) hm]
    have e : ((D.pd k).hw.take (D.pd k).i).getD m 0 = (D.pd k).hw.getD m 0 := by
      simp [List.getD_eq_getElem?_getD, hm]
    rw [e]
    have h1 := fac_d_hv hG hD hk hGo (m := m) hm.le
    have h2 := fac_d_hv hG hD hk hGo (m := m + 1) hm
    have h3 := hpk.2.1.2 m (by omega)
    have h4 := fac_seg hG hD hk hGo hm
    have hf := fac_pos (D := D) (k := k)
    apply Nat.eq_of_mul_eq_mul_left hf
    rw [Nat.mul_add]
    omega

theorem rawP_half_inv :
    ∀ p ∈ (c.raw G D (k + 1)).half, p < G.m → G.pu p ∈ (c.raw G D (k + 1)).X →
      G.pv p ∈ (c.raw G D (k + 1)).X → (c.raw G D (k + 1)).θ ≤ G.pω p →
      p ∈ (c.raw G D (k + 1)).hw := by
  intro p hp hpm hu hv' hθ
  rw [rawP_X] at hu hv'
  rw [rawP_θ] at hθ
  rw [rawP_hw]
  have hpk := petalOk hD hk
  have hhalf : p ∈ c.half → p ∈ c.hw := fun h =>
    hG.half p h hpm (W_subset_X k hu) (W_subset_X k hv') hθ
  have hjp : G.Joins p (G.pu p) (G.pv p) := ⟨hpm, Or.inl ⟨rfl, rfl⟩⟩
  rw [rawP_half] at hp
  split_ifs at hp with hs
  · -- the special petal: the pair lies on the highway of the cluster, before the portal
    obtain ⟨hs, rfl⟩ := hs
    have hsp := hD.2.1 hs
    obtain ⟨m', hm', he, hj'⟩ := PG.ends_of_mem hG.high.1 (hhalf hp)
    have hmi : m' < (D.pd 0).i := by
      by_contra hmi
      have hout := hv_not_mem (closed_Z D 0) hpk (k := m' + 1) (by omega)
        (by rw [hsp.2.2.1]; omega)
      rw [hsp.2.1, hsp.2.2.1] at hout
      rcases hj'.symm.end_eq hjp with h | h
      · exact hout (by show (G.vtx c.t c.hw).getD (m' + 1) 0 ∈ _; rw [h]; exact hu)
      · exact hout (by show (G.vtx c.t c.hw).getD (m' + 1) 0 ∈ _; rw [h]; exact hv')
    rw [hsp.2.2.1, ← he, List.getD_eq_getElem _ _ hm']
    exact List.mem_iff_getElem.mpr ⟨m', by rw [List.length_take]; omega, by simp⟩
  · rcases Finset.mem_union.mp hp with h | h
    · exfalso
      obtain ⟨m', hm', -, hj'⟩ := PG.ends_of_mem hG.high.1 (hhalf h)
      rcases hj'.end_eq hjp with h1 | h1
      · exact hw_not_mem_reg hG.conn hG.high hD (m := m') (by omega) hk hs
          (by show (G.vtx c.t c.hw).getD m' 0 ∈ _; rw [h1]; exact hu)
      · exact hw_not_mem_reg hG.conn hG.high hD (m := m') (by omega) hk hs
          (by show (G.vtx c.t c.hw).getD m' 0 ∈ _; rw [h1]; exact hv')
    · exact List.mem_toFinset.mp h

theorem rawP_good (hGo : G.Ok) : (c.raw G D (k + 1)).Good G :=
  ⟨rawP_conn hG hD hk, rawP_high hG hD hk hGo, rawP_half_inv hG hD hk⟩

theorem rawP_tri (hGo : G.Ok) {z : ℕ} (hz : z ∈ c.W G D k) :
    ∃ i' ≤ (D.pd k).i, ∃ w,
      fac D k * (c.raw G D (k + 1)).d G (D.xc G k) z + c.d G c.x0 (D.xc G k) ≤
        c.d G c.x0 (hv G (D.pd k).tj (D.pd k).hw i') + fac D k * w ∧
      (c.d G c.x0 (D.pd k).tj - c.d G c.x0 (hv G (D.pd k).tj (D.pd k).hw i')) + 2 * w +
        2 * c.d G c.x0 (hv G (D.pd k).tj (D.pd k).hw i') ≤ (D.pd k).r + 2 * c.d G c.x0 z := by
  obtain ⟨i', hi', S, hS, hr, hineq⟩ := rawP_reach hG hD hk hz
  refine ⟨i', hi', PG.wlen (c.len G) S, ?_, hineq⟩
  have htri : (c.raw G D (k + 1)).d G (D.xc G k) z ≤
      (c.raw G D (k + 1)).d G (D.xc G k) (hv G (D.pd k).tj (D.pd k).hw i') +
        (c.raw G D (k + 1)).d G (hv G (D.pd k).tj (D.pd k).hw i') z := by
    unfold d; rw [rawP_X]; exact PG.dist_triangle _ hr ⟨S, hS⟩
  have hS1 : (c.raw G D (k + 1)).d G (hv G (D.pd k).tj (D.pd k).hw i') z ≤
      PG.wlen ((c.raw G D (k + 1)).len G) S := by
    unfold d; rw [rawP_X]; exact PG.dist_le hS
  have hS2 := PG.wlen_mono (rawP_len_le (G := G) (c := c) (D := D) k) S
  have hf := fac_d_hv hG hD hk hGo hi'
  have h1 := Nat.mul_le_mul_left (fac D k) htri
  have h2 := Nat.mul_le_mul_left (fac D k) (hS1.trans hS2)
  rw [Nat.mul_add] at h1
  omega

/-- The core inequality for a regular petal. -/
theorem rawP_core_reg (hGo : G.Ok) (hs : ¬ (D.sp = true ∧ k = 0)) {z : ℕ}
    (hz : z ∈ c.W G D k) :
    2 * (c.raw G D (k + 1)).d G (D.xc G k) z + c.d G c.x0 (D.xc G k) +
      c.d G c.x0 (D.pd k).tj ≤ (D.pd k).r + 2 * c.d G c.x0 z := by
  obtain ⟨i', hi', w, h1, h2⟩ := rawP_tri hG hD hk hGo hz
  have hf : fac D k = 2 := by unfold fac; simp [hs]
  rw [hf] at h1
  have hpk := petalOk hD hk
  have h3 := d_hv_le hpk.2.1 (i := i') (by have := hpk.2.2.1; omega)
  omega

/-- The core inequality for the special petal. -/
theorem rawP_core_sp (hGo : G.Ok) (hs : D.sp = true ∧ k = 0) {z : ℕ} (hz : z ∈ c.W G D k) :
    2 * (c.raw G D (k + 1)).d G (D.xc G k) z + 2 * c.d G c.x0 (D.xc G k) +
      c.d G c.x0 (D.pd k).tj ≤ (D.pd k).r + 2 * c.d G c.x0 z + c.Δ G := by
  obtain ⟨i', hi', w, h1, h2⟩ := rawP_tri hG hD hk hGo hz
  have hf : fac D k = 1 := by unfold fac; simp [hs]
  rw [hf] at h1
  have hpk := petalOk hD hk
  have hil := hpk.2.2.1
  have h3 := d_hv_le hpk.2.1 (i := i') (by omega)
  have h4 := d_le_Δ (c := c) (G := G) (hpk.2.1.hv_mem (i := i') (by omega))
  omega

theorem rawP_Δ (hGo : G.Ok) : 4 * (c.raw G D (k + 1)).Δ G ≤ 3 * c.Δ G := by
  have hpk := petalOk hD hk
  have key : ∀ z ∈ c.W G D k, 4 * (c.raw G D (k + 1)).d G (D.xc G k) z ≤ 3 * c.Δ G := by
    intro z hz
    have hzX := d_le_Δ (c := c) (G := G) (W_subset_X k hz)
    have hx := d_tj_le hG.conn (closed_Z D k) hpk (xc_mem hD hk)
    have hr := r_le hpk
    unfold lo at hr
    by_cases hs : D.sp = true ∧ k = 0
    · have h1 := rawP_core_sp hG hD hk hGo hs hz
      obtain ⟨hs1, rfl⟩ := hs
      have hsp := hD.2.1 hs1
      have h0 := hD.1.mp hs1
      have hfar := far_sp hG.conn hD hs1 (xc_mem hD hk)
      simp only [hs1, and_self, ↓reduceIte] at hr
      unfold loS at hr
      rw [hsp.2.1] at h1 hx
      omega
    · have h1 := rawP_core_reg hG hD hk hGo hs hz
      have h0 := (hD.2.2.1 k hk fun h hk0 => hs ⟨h, hk0⟩).1
      simp only [hs, ↓reduceIte] at hr
      omega
  generalize c.Δ G = Δ0 at key ⊢
  have : (c.raw G D (k + 1)).Δ G ≤ 3 * Δ0 / 4 := by
    unfold Δ
    refine Finset.sup_le fun z hz => ?_
    rw [rawP_X] at hz
    have := key z hz
    rw [rawP_x0]
    omega
  omega

end petal

end Cl

end MinCostFlow.LowStretch
