module

public import MinCostFlow.HierPaths.BuildTopScheduleRun
public import MinCostFlow.HierPaths.BuildNumHier

/-! # Player words for the hierarchy schedule

The padded terminal count determines the core size and the path logarithms.
The root scale uses input conductance, and the remaining rows use the
expansion bound of the core.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.ExpanderDecomp

def buildTopPlayerWords (term x m d j : ℕ) : List ℕ :=
  let rank := depthOf m
  let L := x + 1
  [term, 2 ^ x, rank, 49 * L + 2, L, L,
    if j = 0 then 100 * d else 4 * PParam ParamConfig.default (2 ^ x) rank]

/-- The player row uses the parameters of the certified hierarchy construction. -/
theorem buildTopPlayerWords_eq (route : RouterFn) (core : ℕ → Cited.Graph → CoreResult)
    (G : Cited.Graph) (term d j : ℕ) :
    let B := numParams route core G
    buildTopPlayerWords term B.x G.m d j =
      [term, B.M, B.r, B.Δ, B.L, B.L', B.numBh ParamConfig.default d j] := by
  cases j <;> simp [buildTopPlayerWords, numParams, BuildParams.numBh]

/-- For a nontrivial padded root, the core logarithm is two more than the root exponent. -/
theorem buildTopCoreEll (x : ℕ) (hx : 0 < x) : ell (2 ^ x) = x + 2 := by
  unfold ell
  apply Nat.le_antisymm
  · rw [Nat.clog_le_iff_le_pow (by decide), pow_add]
    have hh : 2 ≤ 2 ^ x := (
      (Nat.pow_le_pow_right (by decide) (show 1 ≤ x by omega) : 2 ^ 1 ≤ 2 ^ x))
    omega
  · apply Nat.succ_le_of_lt
    rw [Nat.lt_clog_iff_pow_lt (by decide), pow_add]
    omega

end MinCostFlow.HierPaths

end
