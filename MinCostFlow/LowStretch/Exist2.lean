module

public import MinCostFlow.LowStretch.Exist1
public import MinCostFlow.LowStretch.Stretch5

/-!
# A correct step exists

We build the petals one by one. If the target is far, the special petal comes first. Then, while
some vertex `z` that is left has `4 d(x0, z) > 3Δ`, we carve a regular petal around it. Each petal
holds its target, so what is left shrinks, and the loop ends (`exists_dec`). Adding a petal at the
end does not change the sets `Z k` before it (`Z_append`), so the rules already checked stay true.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

variable {G : PG} {P : Par}

namespace Cl

variable {c : Cl}

theorem pd_append (sp : Bool) (ps qs : List PD) {k : ℕ} (hk : k < ps.length) :
    Dec.pd ⟨sp, ps ++ qs⟩ k = Dec.pd ⟨sp, ps⟩ k := by
  unfold Dec.pd
  simp only
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hk,
    List.getElem_append_left hk]

theorem pd_last (sp : Bool) (ps : List PD) (x : PD) :
    Dec.pd ⟨sp, ps ++ [x]⟩ ps.length = x := by
  unfold Dec.pd
  simp

theorem Z_append (sp : Bool) (ps qs : List PD) {k : ℕ} (hk : k ≤ ps.length) :
    c.Z G ⟨sp, ps ++ qs⟩ k = c.Z G ⟨sp, ps⟩ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show c.Z G ⟨sp, ps ++ qs⟩ k \ c.carve G (c.Z G ⟨sp, ps ++ qs⟩ k) (Dec.pd ⟨sp, ps ++ qs⟩ k) =
      c.Z G ⟨sp, ps⟩ k \ c.carve G (c.Z G ⟨sp, ps⟩ k) (Dec.pd ⟨sp, ps⟩ k)
    rw [ih (by omega), pd_append sp ps qs (by omega)]

variable (G P c) in
/-- The rules for the petals of a step, without the stopping rule. -/
def Pre (D : Dec) : Prop :=
  (D.sp = true → 0 < D.ps.length ∧ (D.pd 0).tj = c.t ∧ (D.pd 0).hw = c.hw ∧
    c.PetalOk G P c.X (c.loS G) (D.pd 0)) ∧
  (∀ k < D.ps.length, (D.sp = true → k ≠ 0) →
    3 * c.Δ G < 4 * c.d G c.x0 (D.pd k).tj ∧ c.PetalOk G P (c.Z G D k) 0 (D.pd k))

/-- The hypotheses under which petals can be grown. -/
structure Grows (G : PG) (P : Par) (c : Cl) : Prop where
  ok : G.Ok
  conn : c.Conn G
  κ : 1 ≤ P.κ
  L : 1 ≤ P.L
  Δ : 8 * P.L * (lam P 0 + 3) ≤ c.Δ G
  V : c.V G P ≤ 2 ^ lam P 0 * P.κ

/-- One more regular petal. -/
theorem extend (hg : Grows G P c) {sp : Bool} {ps : List PD} (hpre : c.Pre G P ⟨sp, ps⟩)
    {z : ℕ} (hz : z ∈ c.Z G ⟨sp, ps⟩ ps.length) (hfar : 3 * c.Δ G < 4 * c.d G c.x0 z) :
    ∃ pd, c.Pre G P ⟨sp, ps ++ [pd]⟩ ∧
      (c.Z G ⟨sp, ps ++ [pd]⟩ (ps.length + 1)).card < (c.Z G ⟨sp, ps⟩ ps.length).card := by
  have hzX := Z_subset_X (c := c) (G := G) _ _ hz
  obtain ⟨hw, hh⟩ := exists_highway hg.conn hzX
  obtain ⟨pd, htj, -, hpd⟩ := exists_petal (P := P) hg.ok hg.conn (Z_subset_X _ _) hz hh 0
    (by omega) hg.κ hg.L hg.Δ hg.V
  refine ⟨pd, ⟨fun hs => ?_, fun k hk hs => ?_⟩, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hpre.1 hs
    simp only [List.length_append, List.length_singleton]
    rw [pd_append sp ps [pd] h1]
    exact ⟨by omega, h2, h3, h4⟩
  · simp only [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [pd_append sp ps [pd] hk, Z_append sp ps [pd] hk.le]
      exact hpre.2 k hk hs
    · rw [pd_last, Z_append sp ps [pd] le_rfl, htj]
      exact ⟨hfar, hpd⟩
  · show (c.Z G ⟨sp, ps ++ [pd]⟩ ps.length \ c.carve G (c.Z G ⟨sp, ps ++ [pd]⟩ ps.length)
      (Dec.pd ⟨sp, ps ++ [pd]⟩ ps.length)).card < _
    rw [pd_last, Z_append sp ps [pd] le_rfl]
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, fun h => ?_⟩
    have ht := hpd.2.2.2.1 0 (Nat.zero_le _)
    rw [hv_zero, htj] at ht
    have : z ∈ c.Z G ⟨sp, ps⟩ ps.length \ c.carve G (c.Z G ⟨sp, ps⟩ ps.length) pd := by
      rw [h]; exact hz
    exact (Finset.mem_sdiff.mp this).2 ht

/-- Petals are added until no far vertex is left. -/
theorem build (hg : Grows G P c) (sp : Bool) :
    ∀ n (ps : List PD), c.Pre G P ⟨sp, ps⟩ → (c.Z G ⟨sp, ps⟩ ps.length).card ≤ n →
      ∃ ps', c.Pre G P ⟨sp, ps'⟩ ∧ ∀ z ∈ c.stem G ⟨sp, ps'⟩, 4 * c.d G c.x0 z ≤ 3 * c.Δ G := by
  intro n
  induction n with
  | zero =>
    intro ps hpre hn
    refine ⟨ps, hpre, fun z hz => ?_⟩
    have : c.stem G ⟨sp, ps⟩ = ∅ := Finset.card_eq_zero.mp
      (show (c.Z G ⟨sp, ps⟩ ps.length).card = 0 by omega)
    rw [this] at hz
    simp at hz
  | succ n ih =>
    intro ps hpre hn
    by_cases hex : ∃ z ∈ c.Z G ⟨sp, ps⟩ ps.length, 3 * c.Δ G < 4 * c.d G c.x0 z
    · obtain ⟨z, hz, hfar⟩ := hex
      obtain ⟨pd, hpre', hlt⟩ := extend hg hpre hz hfar
      exact ih (ps ++ [pd]) hpre' (by simp only [List.length_append, List.length_singleton]; omega)
    · push Not at hex
      exact ⟨ps, hpre, fun z hz => hex z hz⟩

/-- **A correct step exists** for every cluster where petals can be grown. -/
theorem exists_dec (hg : Grows G P c) (hh : c.IsHighway G c.t c.hw) (hΔ : 0 < c.Δ G) :
    ∃ D, c.DecOk G P D := by
  classical
  have hstart : ∃ ps, c.Pre G P ⟨decide (5 * c.Δ G < 8 * c.d G c.x0 c.t), ps⟩ := by
    by_cases hs : 5 * c.Δ G < 8 * c.d G c.x0 c.t
    · have htX : c.t ∈ c.X := by
        have := hh.hv_mem (i := 0) (Nat.zero_le _); rwa [hv_zero] at this
      obtain ⟨pd, htj, hhw, hpd⟩ := exists_petal (P := P) hg.ok hg.conn subset_rfl htX hh
        (c.loS G) (by unfold loS; omega) hg.κ hg.L hg.Δ hg.V
      refine ⟨[pd], fun _ => ?_, fun k hk hsp => ?_⟩
      · have e : Dec.pd ⟨decide (5 * c.Δ G < 8 * c.d G c.x0 c.t), [pd]⟩ 0 = pd := rfl
        rw [e]
        exact ⟨by simp, htj, hhw, hpd⟩
      · simp only [List.length_singleton] at hk
        exact absurd (show k = 0 by omega) (hsp (by simp [hs]))
    · refine ⟨[], fun h => absurd (of_decide_eq_true h) hs, fun k hk => absurd hk (by simp)⟩
  obtain ⟨ps, hpre⟩ := hstart
  obtain ⟨ps', hpre', hstem⟩ := build hg _ _ ps hpre le_rfl
  exact ⟨⟨_, ps'⟩, by simp, hpre'.1, hpre'.2, hstem⟩

end Cl

end MinCostFlow.LowStretch
