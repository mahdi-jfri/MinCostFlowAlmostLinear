module

public import MinCostFlow.LowStretch.ProgResetD
public import MinCostFlow.LowStretch.KReset

/-!
# The reset of child `k`: the new child meets `Next`

When raw child `k` is reset, the child `S.csOf k = (S.raw k).reset (S.thrK k)` meets `Next`
(`CS.next_reset`, from `next_reset` of `KReset` with `μ` the largest weight of the `θ`-nodes).
So the new threshold is at least `1` and at most a quarter of `θ` (`CS.thrK_le`). The split walk
and the record of the reset need both bounds.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace CS

variable {S : CS} {w : ℕ} {k : ℕ}

/-- **A reset child meets `Next`.** -/
theorem next_reset (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hk : k < S.nch) (hq : S.resetQ k) : Next S.G S.P (S.raw k) (S.csOf k) := by
  classical
  have hcs : S.csOf k = (S.raw k).reset (S.thrK k) := by unfold csOf; rw [if_pos hq]
  have hθ : (S.raw k).θ = S.c.θ := Cl.raw_θ k
  have hsub : (S.raw k).X ⊆ Finset.range S.G.n :=
    (Cl.raw_X_subset (G := S.G) (c := S.c) (D := S.D) k).trans hpre.ok.sub
  have hsat : S.T.Sat S.G (S.raw k).θ (S.raw k).X := by rw [hθ]; exact Cl.sat_raw hpre.ok k
  have hne : (S.raw k).X.Nonempty := Finset.card_pos.mp (by have := hq.1; omega)
  rw [hcs]
  unfold thrK Cl.resetS
  refine Cl.next_reset hpre.ok.tree hpre.ok.hG hpre.ok.hGo hpre.ok.hB (raw_good' hpre hk) hsat
    hsub (by rw [hθ]; exact hpre.ok.inv.one_le) hq.1 hpre.glob.heavy hq.2
    (fun a ha => Finset.le_sup (f := fun a => S.T.mw (S.T.top (S.raw k).θ a)) ha) (Or.inr ?_)
  obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_sup _ hne (fun a => S.T.mw (S.T.top (S.raw k).θ a))
  exact ⟨a, ha, he.symm⟩

/-- **The new threshold is between `1` and `θ / 4`.** -/
theorem thrK_le (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hk : k < S.nch) (hq : S.resetQ k) : 1 ≤ S.thrK k ∧ 4 * S.thrK k ≤ S.c.θ := by
  have hcs : S.csOf k = (S.raw k).reset (S.thrK k) := by unfold csOf; rw [if_pos hq]
  have hθ : (S.raw k).θ = S.c.θ := Cl.raw_θ k
  have hn := next_reset hpre hk hq
  rcases hn with ⟨he, h1 | h1⟩ | ⟨-, -, -, -, -, -, h4, h1, -⟩
  · have := hq.1; omega
  · have := hq.2; omega
  · rw [hcs] at h4 h1
    exact ⟨h1, by rw [← hθ]; exact h4⟩

end CS

end MinCostFlow.LowStretch
