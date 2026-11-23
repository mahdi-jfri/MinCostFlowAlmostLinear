module

public import MinCostFlow.LowStretch.Volume
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr

/-!
# The volumes of the pieces

The *parts* of a step are the stem, with volume `κ` plus the weights of the active pairs inside
it, and the petals, with their volumes from region growing. We show:
* each active pair adds at most its weight `cw` to the parts, in total, so the parts add up to at
  most `V + s · κ` for `s` petals (`parts_sum`);
* a child has volume at most its part plus the weights of its *new* active pairs: those that are
  active in the child but not in the cluster (`child_V`);
* a new active pair of a child is joined by light pairs in the cluster but not in the child. So
  the new pairs of the children and the light-joined pairs of the children are different pairs,
  all light-joined in the cluster (`inact_sum`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

variable {G : PG} {P : Par}

namespace Cl

variable {c : Cl} {D : Dec}

theorem ent_spec {Y : Finset ℕ} {pd : PD} {u : ℕ} (hu : u ∈ c.carve G Y pd) :
    c.DR G pd.tj pd.hw ↑Y u (c.ent G Y pd u) ∧ c.ent G Y pd u ≤ pd.r := by
  obtain ⟨-, k, hk, hdr⟩ := mem_carve.mp hu
  have hne : {k | c.DR G pd.tj pd.hw ↑Y u k}.Nonempty := ⟨k, hdr⟩
  exact ⟨Nat.sInf_mem hne, (Nat.sInf_le hdr).trans hk⟩

theorem Active.not_light {Q p : ℕ} (h : c.Active G Q p) : c.θ ≤ G.pω p := by
  by_contra hl
  exact h.2.2.2.1 ⟨[p], .cons h.2.1 (show G.pω p < c.θ by omega) ⟨h.1, Or.inl ⟨rfl, rfl⟩⟩
    (.nil h.2.2.1)⟩

theorem mem_act {p : ℕ} : p ∈ c.act G P ↔ c.Active G P.Q p := by
  unfold act
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- An active pair that leaves a petal does so before the radius passes its far end. -/
theorem leaves_lt (hc : c.Conn G) {Y : Finset ℕ} (hY : Y ⊆ c.X) {pd : PD} {p : ℕ}
    (hp : p ∈ c.act G P) (hl : Leaves G Y (c.carve G Y pd) p) :
    pd.r < c.ent G Y pd (inEnd G (c.carve G Y pd) p) + 8 * G.pω p := by
  have ha := mem_act.mp hp
  have hθ := ha.not_light
  have hj : G.Joins p (G.pu p) (G.pv p) := ⟨ha.1, Or.inl ⟨rfl, rfl⟩⟩
  rcases hl with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · have he : inEnd G (c.carve G Y pd) p = G.pu p := by simp [inEnd, hu]
    rw [he]
    obtain ⟨hdr, -⟩ := ent_spec hu
    obtain ⟨k', hk', hdr'⟩ := step_le hc (Finset.coe_subset.mpr hY) hdr hj
      (by simpa using (Finset.mem_sdiff.mp hv).1) hθ
    by_contra hge
    exact (Finset.mem_sdiff.mp hv).2 (mem_carve.mpr ⟨(Finset.mem_sdiff.mp hv).1, k', by omega, hdr'⟩)
  · have he : inEnd G (c.carve G Y pd) p = G.pv p := by
      simp [inEnd, (Finset.mem_sdiff.mp hu).2]
    rw [he]
    obtain ⟨hdr, -⟩ := ent_spec hv
    obtain ⟨k', hk', hdr'⟩ := step_le hc (Finset.coe_subset.mpr hY) hdr hj.symm
      (by simpa using (Finset.mem_sdiff.mp hu).1) hθ
    by_contra hge
    exact (Finset.mem_sdiff.mp hu).2 (mem_carve.mpr ⟨(Finset.mem_sdiff.mp hu).1, k', by omega, hdr'⟩)

open Classical in
variable (G P c) in
/-- What pair `p` adds to the volume of the petal of `pd` carved from `Y`. -/
noncomputable def contrib (Y : Finset ℕ) (pd : PD) (p : ℕ) : ℝ :=
  if Inside G (c.carve G Y pd) p then (P.cw p : ℝ)
  else if Leaves G Y (c.carve G Y pd) p then
    (P.cw p : ℝ) * ((pd.r - c.ent G Y pd (inEnd G (c.carve G Y pd) p) : ℕ) : ℝ) / (8 * G.pω p)
  else 0

theorem vol_eq (Y : Finset ℕ) (pd : PD) :
    c.vol G P Y pd = P.κ + ∑ p ∈ c.act G P, c.contrib G P Y pd p := by
  classical
  unfold vol contrib
  simp only
  rw [Finset.sum_filter, Finset.sum_filter, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h1 : Inside G (c.carve G Y pd) p
  · have h2 : ¬ Leaves G Y (c.carve G Y pd) p := by
      rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact (Finset.mem_sdiff.mp h).2 h1.2
      · exact (Finset.mem_sdiff.mp h).2 h1.1
    simp [h1, h2]
  · simp [h1]

theorem contrib_nonneg (Y : Finset ℕ) (pd : PD) (p : ℕ) : 0 ≤ c.contrib G P Y pd p := by
  unfold contrib
  split_ifs
  · exact Nat.cast_nonneg _
  · positivity
  · exact le_rfl

theorem contrib_le (hGo : G.Ok) (hc : c.Conn G) {Y : Finset ℕ} (hY : Y ⊆ c.X) (pd : PD) {p : ℕ}
    (hp : p ∈ c.act G P) : c.contrib G P Y pd p ≤ P.cw p := by
  unfold contrib
  split_ifs with h1 h2
  · exact le_rfl
  · have hlt := leaves_lt hc hY hp h2
    have hω : 0 < G.pω p := (hGo p (mem_act.mp hp).1).2.2.2.2
    have h3 : ((pd.r - c.ent G Y pd (inEnd G (c.carve G Y pd) p) : ℕ) : ℝ) ≤ 8 * G.pω p := by
      have : pd.r - c.ent G Y pd (inEnd G (c.carve G Y pd) p) ≤ 8 * G.pω p := by omega
      exact_mod_cast this
    have h4 : (0 : ℝ) < 8 * G.pω p := by positivity
    rw [mul_div_assoc]
    calc (P.cw p : ℝ) * (((pd.r - c.ent G Y pd (inEnd G (c.carve G Y pd) p) : ℕ) : ℝ) /
          (8 * G.pω p)) ≤ P.cw p * 1 := by
          gcongr
          rw [div_le_one h4]; exact h3
      _ = P.cw p := mul_one _
  · exact Nat.cast_nonneg _

/-- A pair that adds to petal `k` has both ends in `Z k` and one end in petal `k`. -/
theorem contrib_ne_zero {k p : ℕ} (h : c.contrib G P (c.Z G D k) (D.pd k) p ≠ 0) :
    (G.pu p ∈ c.Z G D k ∧ G.pv p ∈ c.Z G D k) ∧ (G.pu p ∈ c.W G D k ∨ G.pv p ∈ c.W G D k) := by
  unfold contrib at h
  split_ifs at h with h1 h2
  · exact ⟨⟨W_subset D k h1.1, W_subset D k h1.2⟩, Or.inl h1.1⟩
  · rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact ⟨⟨W_subset D k h3, (Finset.mem_sdiff.mp h4).1⟩, Or.inl h3⟩
    · exact ⟨⟨(Finset.mem_sdiff.mp h4).1, W_subset D k h3⟩, Or.inr h3⟩
  · exact absurd rfl h

open Classical in
variable (G P c D) in
/-- The volume of the stem: `κ` plus the weights of the active pairs inside it. -/
noncomputable def vstem : ℝ :=
  P.κ + ∑ p ∈ c.act G P, if Inside G (c.stem G D) p then (P.cw p : ℝ) else 0

/-- The parts add up to at most `V + s · κ`. -/
theorem parts_sum (hGo : G.Ok) (hc : c.Conn G) :
    c.vstem G P D + ∑ k ∈ Finset.range D.ps.length, c.vol G P (c.Z G D k) (D.pd k) ≤
      c.V G P + D.ps.length * P.κ := by
  classical
  simp only [vol_eq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold vstem V
  rw [Finset.sum_comm]
  have key : ∀ p ∈ c.act G P, ((if Inside G (c.stem G D) p then (P.cw p : ℝ) else 0) +
      ∑ k ∈ Finset.range D.ps.length, c.contrib G P (c.Z G D k) (D.pd k) p) ≤ P.cw p := by
    intro p hp
    by_cases hex : ∃ j ∈ Finset.range D.ps.length, c.contrib G P (c.Z G D j) (D.pd j) p ≠ 0
    · obtain ⟨j, hj, hne⟩ := hex
      have hj' := Finset.mem_range.mp hj
      obtain ⟨-, hW⟩ := contrib_ne_zero hne
      have hsum : ∑ k ∈ Finset.range D.ps.length, c.contrib G P (c.Z G D k) (D.pd k) p =
          c.contrib G P (c.Z G D j) (D.pd j) p := by
        refine Finset.sum_eq_single_of_mem j hj fun k hk hkj => ?_
        by_contra hne'
        obtain ⟨⟨hu, hv⟩, -⟩ := contrib_ne_zero hne'
        rcases Nat.lt_or_gt_of_ne hkj with hlt | hlt
        · obtain ⟨-, hW'⟩ := contrib_ne_zero hne'
          obtain ⟨⟨hu', hv'⟩, -⟩ := contrib_ne_zero hne
          have hsub := Z_antitone (c := c) (G := G) D (show k + 1 ≤ j by omega)
          rw [Z_succ] at hsub
          rcases hW' with h | h
          · exact (Finset.mem_sdiff.mp (hsub (by first | exact hu' | exact hv'))).2 h
          · exact (Finset.mem_sdiff.mp (hsub hv')).2 h
        · have hsub := Z_antitone (c := c) (G := G) D (show j + 1 ≤ k by omega)
          rw [Z_succ] at hsub
          rcases hW with h | h
          · exact (Finset.mem_sdiff.mp (hsub hu)).2 h
          · exact (Finset.mem_sdiff.mp (hsub hv)).2 h
      have hstem : ¬ Inside G (c.stem G D) p := by
        rintro ⟨hu, hv⟩
        rcases hW with h | h
        · exact stem_disj hj' hu h
        · exact stem_disj hj' hv h
      rw [hsum]
      simp only [hstem, ↓reduceIte, zero_add]
      exact contrib_le hGo hc (Z_subset_X D j) _ hp
    · push Not at hex
      rw [Finset.sum_eq_zero hex, add_zero]
      split_ifs
      · exact le_rfl
      · exact Nat.cast_nonneg _
  have := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib] at this
  linarith

end Cl

end MinCostFlow.LowStretch
