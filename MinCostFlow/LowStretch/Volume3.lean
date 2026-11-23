module

public import MinCostFlow.LowStretch.Volume2
public import MinCostFlow.LowStretch.Tree
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# New active pairs

A child has volume at most its part plus the weights of its new active pairs (`child_V`). A new
active pair is joined by light pairs in the cluster, but not in the child. So the new active pairs
of all children, together with the pairs that stay light-joined in the children, are different
pairs that are light-joined in the cluster (`inact_sum`). Each pair is therefore new at most once
along the run.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

variable {G : PG} {P : Par}

theorem Next.θ_le {r c' : Cl} (hn : Next G P r c') : c'.θ ≤ r.θ := by
  rcases hn with ⟨rfl, -⟩ | h
  · exact le_rfl
  · have := h.2.2.2.2.2.2.2.1; omega

namespace Cl

variable {c : Cl} {D : Dec}

variable (G P c D) in
/-- The parts of a step: the stem, then the petals. -/
noncomputable def part : ℕ → ℝ
  | 0 => c.vstem G P D
  | k + 1 => c.vol G P (c.Z G D k) (D.pd k)

open Classical in
variable (G P) in
/-- The pairs inside `X` that are joined by light pairs. -/
noncomputable def lset (c : Cl) : Finset ℕ :=
  (Finset.range G.m).filter fun p => G.pu p ∈ c.X ∧ G.pv p ∈ c.X ∧ c.LConn G (G.pu p) (G.pv p)

variable (G P) in
/-- Their weight. -/
noncomputable def inact (c : Cl) : ℝ := ∑ p ∈ lset G c, (P.cw p : ℝ)

theorem act_inside {c' : Cl} {p : ℕ} (hp : p ∈ c'.act G P) :
    p < G.m ∧ G.pu p ∈ c'.X ∧ G.pv p ∈ c'.X :=
  let h := mem_act.mp hp; ⟨h.1, h.2.1, h.2.2.1⟩

/-- A child has volume at most its part plus the weights of its new active pairs. -/
theorem child_V {k : ℕ} {c' : Cl} (hX : c'.X = (c.raw G D k).X) :
    c'.V G P ≤ c.part G P D k + ∑ p ∈ c'.act G P \ c.act G P, (P.cw p : ℝ) := by
  classical
  unfold V
  rw [← Finset.sum_inter_add_sum_sdiff (c'.act G P) (c.act G P)]
  have h1 : ∑ p ∈ c'.act G P ∩ c.act G P, (P.cw p : ℝ) ≤
      ∑ p ∈ c.act G P, if Inside G (c.raw G D k).X p then (P.cw p : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun _ _ _ => Nat.cast_nonneg _)
    obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hp
    obtain ⟨-, hu, hv⟩ := act_inside h1
    rw [hX] at hu hv
    exact Finset.mem_filter.mpr ⟨h2, hu, hv⟩
  have h2 : P.κ + ∑ p ∈ c.act G P, (if Inside G (c.raw G D k).X p then (P.cw p : ℝ) else 0) ≤
      c.part G P D k := by
    cases k with
    | zero => unfold part vstem; rw [raw0_X]
    | succ k =>
      show _ ≤ c.vol G P (c.Z G D k) (D.pd k)
      rw [vol_eq]
      refine add_le_add le_rfl (Finset.sum_le_sum fun p _ => ?_)
      rw [rawP_X]
      unfold contrib W
      split_ifs <;> first | exact le_rfl | positivity | exact Nat.cast_nonneg _
  linarith

/-- A new active pair of a child is light-joined in the cluster, but not in the child. -/
theorem new_lconn (hGo : G.Ok) (hB : 1 ≤ P.B) (hc : c.Inv G P) (hXc : 2 ≤ c.X.card)
    (hD : c.DecOk G P D) {k : ℕ} (hk : k < D.nch) {c' : Cl} (hn : Next G P (c.raw G D k) c')
    {p : ℕ} (hp : p ∈ c'.act G P \ c.act G P) :
    p < G.m ∧ G.pu p ∈ c'.X ∧ G.pv p ∈ c'.X ∧ c.LConn G (G.pu p) (G.pv p) ∧
      ¬ c'.LConn G (G.pu p) (G.pv p) := by
  obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hp
  have ha := mem_act.mp h1
  refine ⟨ha.1, ha.2.1, ha.2.2.1, ?_, ha.2.2.2.1⟩
  by_contra hl
  refine h2 (mem_act.mpr ⟨ha.1, ?_, ?_, hl, ?_⟩)
  · have := ha.2.1; rw [hn.X_eq] at this; exact raw_X_subset k this
  · have := ha.2.2.1; rw [hn.X_eq] at this; exact raw_X_subset k this
  · have hψ := psi_child hGo hB hc hXc hD hk hn
    have := ha.2.2.2.2
    have : P.Q * (c'.Δ G * c'.θ) ≤ P.Q * (c.Δ G * c.θ) := Nat.mul_le_mul_left _ (by omega)
    omega

theorem lset_child {k : ℕ} {c' : Cl} (hn : Next G P (c.raw G D k) c') :
    lset G c' ⊆ lset G c := by
  intro p hp
  simp only [lset, Finset.mem_filter, Finset.mem_range] at hp ⊢
  obtain ⟨hm, hu, hv, ps, hw⟩ := hp
  have hsub : c'.X ⊆ c.X := by rw [hn.X_eq]; exact raw_X_subset k
  have hθ : c'.θ ≤ c.θ := by have := hn.θ_le; rwa [raw_θ] at this
  refine ⟨hm, hsub hu, hsub hv, ps, hw.mono (Finset.coe_subset.mpr hsub) fun q hq => ?_⟩
  simp only [light, Set.mem_ofPred_eq] at hq ⊢
  omega

/-- The new active pairs of the children and the pairs that stay light-joined in the children
are different pairs, all light-joined in the cluster. -/
theorem inact_sum (hGo : G.Ok) (hB : 1 ≤ P.B) (hc : c.Inv G P) (hXc : 2 ≤ c.X.card)
    (hD : c.DecOk G P D) {cs : ℕ → Cl} (hn : ∀ k < D.nch, Next G P (c.raw G D k) (cs k)) :
    ∑ k ∈ Finset.range D.nch, (∑ p ∈ (cs k).act G P \ c.act G P, (P.cw p : ℝ) +
      inact G P (cs k)) ≤ inact G P c := by
  classical
  have hdisj : ∀ k < D.nch, Disjoint ((cs k).act G P \ c.act G P) (lset G (cs k)) := by
    intro k hk
    rw [Finset.disjoint_left]
    intro p hp hp'
    have := (new_lconn hGo hB hc hXc hD hk (hn k hk) hp).2.2.2.2
    simp only [lset, Finset.mem_filter] at hp'
    exact this hp'.2.2.2
  have hin : ∀ k < D.nch, ∀ p ∈ ((cs k).act G P \ c.act G P) ∪ lset G (cs k),
      G.pu p ∈ (c.raw G D k).X := by
    intro k hk p hp
    rw [← (hn k hk).X_eq]
    rcases Finset.mem_union.mp hp with h | h
    · exact (act_inside (Finset.mem_sdiff.mp h).1).2.1
    · simp only [lset, Finset.mem_filter] at h; exact h.2.1
  have e : ∀ k ∈ Finset.range D.nch, (∑ p ∈ (cs k).act G P \ c.act G P, (P.cw p : ℝ) +
      inact G P (cs k)) = ∑ p ∈ ((cs k).act G P \ c.act G P) ∪ lset G (cs k), (P.cw p : ℝ) := by
    intro k hk
    unfold inact
    rw [Finset.sum_union (hdisj k (Finset.mem_range.mp hk))]
  rw [Finset.sum_congr rfl e, ← Finset.sum_biUnion]
  · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.cast_nonneg _)
    intro p hp
    obtain ⟨k, hk, hp⟩ := Finset.mem_biUnion.mp hp
    have hk' := Finset.mem_range.mp hk
    rcases Finset.mem_union.mp hp with h | h
    · obtain ⟨hm, hu, hv, hl, -⟩ := new_lconn hGo hB hc hXc hD hk' (hn k hk') h
      rw [(hn k hk').X_eq] at hu hv
      simp only [lset, Finset.mem_filter, Finset.mem_range]
      exact ⟨hm, raw_X_subset k hu, raw_X_subset k hv, hl⟩
    · exact lset_child (hn k hk') h
  · intro j hj k hk hjk
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hpj hpk
    exact hjk (raw_eq_of_mem (Finset.mem_range.mp hj) (Finset.mem_range.mp hk)
      (hin j (Finset.mem_range.mp hj) p hpj) (hin k (Finset.mem_range.mp hk) p hpk))

end Cl

end MinCostFlow.LowStretch
