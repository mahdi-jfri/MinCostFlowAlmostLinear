module

public import MinCostFlow.LowStretch.Exist3

/-!
# A run exists

With fitting constants (`Par.Fit`), every cluster that meets the invariant has a run: a step
exists (`Cl.exists_dec`), each child gets a threshold (`Cl.exists_next`), and each child is
smaller than the cluster, so the children have runs by induction on the size (`exists_run`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

/-- The constants fit the graph. -/
structure Par.Fit (G : PG) (P : Par) : Prop where
  ok : G.Ok
  B : 1 ≤ P.B
  κ : 1 ≤ P.κ
  L : 1 ≤ P.L
  BL : 8 * P.L * (Cl.lam P 0 + 3) ≤ 2 * P.B
  lam : Vmax G P ≤ 2 ^ Cl.lam P 0 * P.κ
  ω : ∀ p < G.m, 8 * P.B * G.n ≤ G.pω p
  Q : 512 * P.B * G.n ^ 2 ≤ P.Q

variable {G : PG} {P : Par}

namespace Cl

variable {c : Cl} {D : Dec}

theorem V_le_Vmax : c.V G P ≤ Vmax G P := by
  have := V_add_new_le (G := G) (P := P) (c := c) c
  simp only [Finset.sdiff_self, Finset.sum_empty, add_zero] at this
  unfold Vmax
  have : (0 : ℝ) ≤ G.n * P.κ := by positivity
  linarith

theorem grows (hP : P.Fit G) (hc : c.Inv G P) (hX : 2 ≤ c.X.card) : Grows G P c :=
  ⟨hP.ok, hc.good.conn, hP.κ, hP.L, Δ_ge_L hc hX hP.BL, V_le_Vmax.trans hP.lam⟩

/-- Each piece of a step is smaller than the cluster. -/
theorem card_raw_lt (hc : c.Conn G) (hD : c.DecOk G P D) (hΔ : 0 < c.Δ G) (hl : 0 < D.ps.length)
    {k : ℕ} (hk : k < D.nch) : (c.raw G D k).X.card < c.X.card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨raw_X_subset k, fun h => ?_⟩
  cases k with
  | zero =>
    have ht := (petalOk hD hl).2.2.2.1 0 (Nat.zero_le _)
    have htX : hv G (D.pd 0).tj (D.pd 0).hw 0 ∈ (c.raw G D 0).X := by
      rw [h]; exact W_subset_X 0 ht
    rw [raw0_X] at htX
    exact stem_disj hl htX ht
  | succ j =>
    have hx := x0_mem_stem hc hD hΔ
    have hxX : c.x0 ∈ (c.raw G D (j + 1)).X := by rw [h]; exact stem_subset_X hx
    rw [rawP_X] at hxX
    exact stem_disj (by unfold Dec.nch at hk; omega) hx hxX

end Cl

open Cl in
/-- **A run exists** for every cluster that meets the invariant. -/
theorem exists_run (hP : P.Fit G) : ∀ c : Cl, c.Inv G P → ∃ T, Run G P c T := by
  intro c
  induction h : c.X.card using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    intro hc
    by_cases hX : c.X.card ≤ 1
    · exact ⟨[], .leaf hX⟩
    push Not at hX
    have hX : 2 ≤ c.X.card := hX
    have hΔ := hc.Δ_pos hP.B hX
    obtain ⟨D, hD⟩ := exists_dec (grows hP hc hX) hc.good.high hΔ
    have hl := len_pos hP.B hc hX hD
    have hnext : ∀ k < D.nch, ∃ c', Next G P (c.raw G D k) c' := fun k hk =>
      exists_next hP.ok hP.B (raw_good hc.good hD hΔ hP.ok hk)
        (by
          have := Finset.card_le_card ((raw_X_subset (G := G) (D := D) k).trans hc.sub)
          rwa [Finset.card_range] at this) hP.ω
    classical
    let cs : ℕ → Cl := fun k => if hk : k < D.nch then (hnext k hk).choose else c
    have hcs : ∀ k < D.nch, Next G P (c.raw G D k) (cs k) := fun k hk => by
      simp only [cs, hk, ↓reduceDIte]; exact (hnext k hk).choose_spec
    have hrun : ∀ k < D.nch, ∃ T, Run G P (cs k) T := fun k hk => by
      have hlt : (cs k).X.card < n := by
        rw [(hcs k hk).X_eq, ← h]
        exact card_raw_lt hc.good.conn hD hΔ hl hk
      exact ih _ hlt (cs k) rfl (child_inv hP.ok hP.B hc hX hD hk (hcs k hk))
    let Ts : ℕ → List ℕ := fun k => if hk : k < D.nch then (hrun k hk).choose else []
    have hTs : ∀ k < D.nch, Run G P (cs k) (Ts k) := fun k hk => by
      simp only [Ts, hk, ↓reduceDIte]; exact (hrun k hk).choose_spec
    exact ⟨_, .node D cs Ts hX hD hcs hTs⟩

end MinCostFlow.LowStretch
