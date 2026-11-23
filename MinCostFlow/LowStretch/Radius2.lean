module

public import MinCostFlow.LowStretch.Radius

/-!
# The radius of the tree, by induction on the run

This is the induction behind Claim 12 and Lemma 13 of [AN19]. For a vertex `y` of petal `k`, the
walk in the tree goes from the center to the outer end `y_k` of the portal (through later pieces,
by induction from the last piece back to the first), then over the portal to the center `x_k` of
the petal, then inside the petal to `y`. The core inequalities of `Cl.rawP_core_reg` and
`Cl.rawP_core_sp` show that the length stays below `2 d(x0, y)`, plus the errors of the pieces
on the way.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

variable {G : PG} {P : Par}

namespace Cl

variable {c : Cl} {D : Dec}

/-- The portal of petal `k` in the tree: its tree length and the outer end's distance add up to at
most the distance of the center of the petal. -/
theorem portal_step (hD : c.DecOk G P D) {k : ℕ} (hk : k < D.ps.length) :
    G.hl (D.portal k) + c.d G c.x0 (D.yc G k) ≤ c.d G c.x0 (D.xc G k) := by
  have hpk := petalOk hD hk
  have h1 := hpk.2.1.2 (D.pd k).i hpk.2.2.1
  have h2 := half_le_len (c := c) (G := G) (portal_not_light (closed_Z D k) hpk)
  unfold PG.hl Dec.portal Dec.xc Dec.yc
  omega

theorem card_Z_succ (k : ℕ) :
    (c.Z G D (k + 1)).card + (c.W G D k).card = (c.Z G D k).card := by
  rw [Z_succ]; exact Finset.card_sdiff_add_card_eq_card (W_subset D k)

theorem raw0_t_sp (hD : c.DecOk G P D) (hs : D.sp = true) : (c.raw G D 0).t = D.yc G 0 := by
  unfold raw; simp [hs]

theorem raw0_t_nsp (hs : ¬ D.sp = true) : (c.raw G D 0).t = c.t := by
  unfold raw; simp [hs]

end Cl

open Cl in
/-- **Claim 12 and Lemma 13 of [AN19]**, with errors: the radius bounds hold for every cluster of
a run. -/
theorem Run.radius (hGo : G.Ok) (hB : 1 ≤ P.B) {c : Cl} {T : List ℕ} (h : Run G P c T)
    (hc : c.Inv G P) : RadOk G P c T := by
  induction h with
  | @leaf c hX =>
    have hx0 := hc.good.conn.1
    have hall : ∀ y ∈ c.X, y = c.x0 := fun y hy => Finset.card_le_one.mp hX y hy _ hx0
    have htX : c.t ∈ c.X := by
      have := hc.good.high.hv_mem (i := 0) (Nat.zero_le _); rwa [hv_zero] at this
    refine ⟨fun y hy => by rw [hall y hy]; exact TW.refl _ _ _, ?_⟩
    rw [hall _ htX]; exact TW.refl _ _ _
  | @node c D cs Ts hX hD hn hr ih =>
    have hΔ := hc.Δ_pos hB hX
    have hgood : ∀ k < D.nch, (c.raw G D k).Good G := fun k hk =>
      raw_good hc.good hD hΔ hGo hk
    have hinv : ∀ k < D.nch, (cs k).Inv G P := fun k hk =>
      Cl.child_inv hGo hB hc hX hD hk (hn k hk)
    set T := (List.range D.nch).flatMap Ts ++ D.portals with hT
    have hsub : ∀ k < D.nch, ∀ p ∈ Ts k, p ∈ T := fun k hk p hp =>
      List.mem_append_left _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, hp⟩)
    have hportT : ∀ k < D.ps.length, D.portal k ∈ T := fun k hk =>
      List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
    have hcg : ∀ k < D.nch, RadOk G P (c.raw G D k) T := fun k hk => by
      have := (hn k hk).radOk hGo (hgood k hk) (ih k hk (hinv k hk))
      exact ⟨fun y hy => (this.1 y hy).mono (hsub k hk) le_rfl, this.2.mono (hsub k hk) le_rfl⟩
    have hlen : D.nch = D.ps.length + 1 := rfl
    -- the portal of petal `k`, as a walk in the tree
    have hpw : ∀ k < D.ps.length, TW G T (D.yc G k) (D.xc G k) (G.hl (D.portal k)) :=
      fun k hk => TW.pair (hportT k hk) (portal_joins hD hk).symm
    -- the walk inside petal `k`
    have hinside : ∀ k < D.ps.length, ∀ y ∈ c.W G D k, TW G T (D.xc G k) y
        (2 * (c.raw G D (k + 1)).d G (D.xc G k) y + P.A * (c.W G D k).card * c.θ) :=
      fun k hk y hy => (hcg (k + 1) (by omega)).1 y hy
    -- the walk to the outer end of the special portal, through the stem
    have hsp_out : D.sp = true → TW G T c.x0 (D.yc G 0)
        (c.d G c.x0 (D.yc G 0) + P.A * (c.stem G D).card * c.θ) := by
      intro hs
      have h0 := (hcg 0 (by omega)).2
      rw [raw0_t_sp hD hs, raw0_d hc.good.conn (yc_sp_mem_stem hc.good.conn hD hs), raw0_x0,
        raw0_X, raw0_θ] at h0
      exact h0
    -- the bound for the vertices of `Z k`, from the last piece back to the first
    have hP : ∀ n k, k + n = D.ps.length → ∀ y ∈ c.Z G D k,
        TW G T c.x0 y (2 * c.d G c.x0 y + P.A * (c.Z G D k).card * c.θ) := by
      intro n
      induction n with
      | zero =>
        intro k hk y hy
        have hy' : y ∈ c.stem G D := by unfold stem; rw [← hk, Nat.add_zero]; exact hy
        have h0 := (hcg 0 (by omega)).1 y (by rw [raw0_X]; exact hy')
        rw [raw0_d hc.good.conn hy', raw0_x0, raw0_X, raw0_θ] at h0
        refine h0.mono (fun _ h => h) ?_
        unfold stem; rw [← hk, Nat.add_zero]
      | succ n ihn =>
        intro k hk y hy
        have hkl : k < D.ps.length := by omega
        have hcz := card_Z_succ (c := c) (G := G) (D := D) k
        have hA : P.A * (c.Z G D (k + 1)).card * c.θ + P.A * (c.W G D k).card * c.θ =
            P.A * (c.Z G D k).card * c.θ := by
          rw [← hcz, Nat.mul_add, Nat.add_mul]
        by_cases hy1 : y ∈ c.Z G D (k + 1)
        · refine (ihn (k + 1) (by omega) y hy1).mono (fun _ h => h) ?_
          omega
        have hyW : y ∈ c.W G D k := by
          rw [Z_succ] at hy1
          by_contra h; exact hy1 (Finset.mem_sdiff.mpr ⟨hy, h⟩)
        have hpk := petalOk hD hkl
        have hps := portal_step hD hkl
        have hin := hinside k hkl y hyW
        by_cases hs : D.sp = true ∧ k = 0
        · obtain ⟨hs1, rfl⟩ := hs
          have hsp := hD.2.1 hs1
          have h0 := hD.1.mp hs1
          have hout := hsp_out hs1
          have hcore := rawP_core_sp hc.good hD hkl hGo ⟨hs1, rfl⟩ hyW
          have hfar := far_sp hc.good.conn hD hs1 (xc_mem hD hkl)
          have hr := r_le hpk
          unfold lo loS at hr
          simp only [hs1, and_self, ↓reduceIte] at hr
          rw [hsp.2.1] at hcore
          have hst : (c.stem G D).card ≤ (c.Z G D 1).card :=
            Finset.card_le_card (stem_subset_Z 1 (by omega))
          have hst' : P.A * (c.stem G D).card * c.θ ≤ P.A * (c.Z G D 1).card * c.θ :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hst)
          simp only [Nat.zero_add] at hA
          refine ((hout.trans (hpw 0 hkl)).trans hin).mono (fun _ h => h) ?_
          omega
        · have hout := ihn (k + 1) (by omega) (D.yc G k) (yc_mem hD hkl)
          have hcore := rawP_core_reg hc.good hD hkl hGo hs hyW
          have hrl := r_lt_out (closed_Z D k) hpk
          unfold Dec.yc at hout hps
          unfold Dec.xc at hps hcore hin
          refine ((hout.trans (hpw k hkl)).trans hin).mono (fun _ h => h) ?_
          omega
    refine ⟨fun y hy => hP D.ps.length 0 (by omega) y hy, ?_⟩
    -- the target
    by_cases hs : D.sp = true
    · have hsp := hD.2.1 hs
      have hpk := petalOk hD hsp.1
      have hout := hsp_out hs
      have hps := portal_step hD hsp.1
      have h1 := (hcg 1 (by omega)).2
      rw [rawP_x0, rawP_t, rawP_X, raw_θ] at h1
      have hf := fac_d_hv hc.good hD hsp.1 hGo (m := 0) (Nat.zero_le _)
      have hfac : fac D 0 = 1 := by unfold fac; simp [hs]
      rw [hfac, hv_zero] at hf
      simp only [Nat.zero_add] at hf
      have hst : (c.stem G D).card + (c.W G D 0).card ≤ c.X.card := by
        have := card_Z_succ (c := c) (G := G) (D := D) 0
        have h2 := Finset.card_le_card (stem_subset_Z (c := c) (G := G) (D := D) 1 (by omega))
        have e : c.Z G D 0 = c.X := rfl
        rw [e] at this
        simp only [Nat.zero_add] at this
        omega
      have hst' : P.A * (c.stem G D).card * c.θ + P.A * (c.W G D 0).card * c.θ ≤
          P.A * c.X.card * c.θ := by
        rw [← Nat.add_mul, ← Nat.mul_add]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hst)
      rw [hsp.2.1] at h1 hf
      refine ((hout.trans (hpw 0 hsp.1)).trans h1).mono (fun _ h => h) ?_
      omega
    · have h0 := (hcg 0 (by omega)).2
      have htS : c.t ∈ c.stem G D := by
        rcases hw_mem hc.good.conn hc.good.high hD (m := 0) (Nat.zero_le _) with
          ⟨h1, -⟩ | ⟨-, h2⟩
        · exact absurd h1 hs
        · rwa [hv_zero] at h2
      rw [raw0_t_nsp hs, raw0_d hc.good.conn htS, raw0_x0, raw0_X, raw0_θ] at h0
      refine h0.mono (fun _ h => h) ?_
      have := Finset.card_le_card (stem_subset_X (c := c) (G := G) (D := D))
      have := Nat.mul_le_mul_right c.θ (Nat.mul_le_mul_left P.A this)
      omega

end MinCostFlow.LowStretch
