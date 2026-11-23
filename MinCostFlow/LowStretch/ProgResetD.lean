module

public import MinCostFlow.LowStretch.ProgResetB
public import MinCostFlow.LowStretch.ProgResetC

/-!
# The reset of child `k`: the threshold is the one of the spec

The threshold that `rsP` computes for raw child `k` (`RsV.x` of `CS.rsV`) is `S.thrK k`, the new
threshold of the reset rule (`CS.rsV_x`). The two differ only in names: `rsP` takes the largest
weight over the `c.θ`-nodes and the factor `B` from the global block, while `Cl.resetS` uses the
threshold of the raw child, which is `c.θ` (`Cl.raw_θ`), and `B` of the parameters, which equals
the one of the global block (`ChildPre.glob`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace CS

variable {S : CS} {w : ℕ} {M1 : ℕ → ℕ} {k H : ℕ}

/-- The size `S` of `rsP` is the one of the reset rule. -/
theorem rsV_S (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) :
    (S.rsV M1 k H).S = Cl.resetS S.T S.G S.P (S.raw k) := by
  have hB : S.E.B = S.P.B := hpre.glob.B
  have hθ : (S.raw k).θ = S.c.θ := Cl.raw_θ k
  simp only [RsV.S, rsV, Cl.resetS, hθ, hB]

/-- **The threshold of `rsP` is `thrK k`.** -/
theorem rsV_x (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) :
    (S.rsV M1 k H).x = S.thrK k := by
  have hB : S.E.B = S.P.B := hpre.glob.B
  simp only [RsV.x, RsV.lx, thrK, thr, rsV_S hpre]
  simp only [rsV, hB]

end CS

end MinCostFlow.LowStretch
