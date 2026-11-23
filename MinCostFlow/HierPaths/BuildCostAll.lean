module

public import MinCostFlow.HierPaths.BuildCost
import MinCostFlow.Spanner.Subgraph
import MinCostFlow.ExpanderDecomp.Embedding
import Mathlib.Tactic.GCongr

/-!
# The operation count of the whole construction

`buildCost` adds the work of every group at depths `j < D` (`groupCost`: the game of `lemma_3` when
the children have size above one, and the sibling connectors). Each router call is counted
with the linear shortcuts of its walks (`callCost`, `BuildProgEraseCost.lean`). The bound
(`buildCost_le`), for a router with constant `C`:
```
buildCost ≤ ∑_{j < D} 2^x · F_j(2^b),
F_j(k) = T (A + 2 Q_k) + 2 Q_k + k² · 2 Q_1,
```
with `T = 49 L' + 1` rounds, `A = N² W^{10 r² + 10}` the core's cost per vertex, and
`Q_n = (C + 2) (n (d_j + 1) R_j (Δ + 2) + 1)` the cost per vertex of a call with `n` pairs at
depth `j` (router scale `b̂_j`). The `+ 2` pays for the shortcuts (`callCost_le`). This
bound has three factors: the `2^x < 4m` terminals, the `D = h + 1` depths, and the
factor `(B + 1)²` from `k ≤ B = 2^b` children. The router's cost per vertex `Q_n` comes from the
host degree `Δ`: a host on `p` terminals has at most `Δ p / 2` edges.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

namespace BuildParams

/-- The work at group `g` of depth `j`. -/
def groupCost (B : BuildParams) (routeCost : RouterCostFn) (coreCost : ℕ → Graph → ℕ)
    (H0 : Graph) (j g : ℕ) : ℕ :=
  (if 1 < groupSize B.x B.b (j + 1) then
    gameCost B.route routeCost (B.host H0 j g) (members B.x B.b j g) B.Δ B.L B.core coreCost
      B.M B.r (groupSize B.x B.b (j + 1)) (branching B.x B.b j) (B.off j g) B.T
  else 0) +
  (if 1 < groupSize B.x B.b j then
    connCost B.route routeCost (B.host H0 j g) (members B.x B.b j g) B.Δ B.L
      (fun i => members B.x B.b (j + 1) (g * branching B.x B.b j + i)) (branching B.x B.b j)
  else 0)

/-- The work at all groups of depths `j < D`. -/
def buildCost (B : BuildParams) (routeCost : RouterCostFn) (coreCost : ℕ → Graph → ℕ)
    (H0 : Graph) (D : ℕ) : ℕ :=
  ∑ j ∈ Finset.range D, ∑ g ∈ Finset.range (numGroups B.x B.b j),
    B.groupCost routeCost coreCost H0 j g

/-- The router's cost per vertex for a call with `n` pairs. -/
def routeUnit (B : BuildParams) (C bh n : ℕ) : ℕ :=
  C * (n * (routePathLen B.Δ bh B.L + 1) * routeCong B.Δ bh B.L * (B.Δ + 2) + 1)

/-- The cost per vertex of a group with `k` children. -/
def unitCost (B : BuildParams) (cfg : ParamConfig) (C bh k : ℕ) : ℕ :=
  B.T * ((NOf B.M B.r) ^ 2 * (WParam cfg B.M) ^ (10 * B.r ^ 2 + 10) + 2 * B.routeUnit C bh k) +
    2 * B.routeUnit C bh k + k * k * (2 * B.routeUnit C bh 1)

end BuildParams

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

namespace BuildParams

variable {B : BuildParams}

/-- **A router call costs at most `|X| · Q_n`.** -/
theorem routeBoundN_le {C : ℕ} {G : Graph} {X : Finset ℕ} (hH : HostPre G X B.Δ B.L)
    (hX : 1 ≤ X.card) (n bh : ℕ) :
    routeBoundN C G X n B.Δ B.L bh ≤ X.card * B.routeUnit C bh n := by
  have h2 := volIn_self_eq_two_mul_inside G X
  have h3 := volIn_le_mul_card (subset_refl X) hH.2.2.2.1
  have hA : X.card + (G.inside X).length + 1 ≤ (B.Δ + 2) * X.card := by
    have : (B.Δ + 2) * X.card = B.Δ * X.card + 2 * X.card := Nat.add_mul _ _ _
    omega
  unfold routeBoundN routeUnit
  set w := n * (routePathLen B.Δ bh B.L + 1) * routeCong B.Δ bh B.L
  calc C * (n * (X.card + (G.inside X).length + 1) * (routePathLen B.Δ bh B.L + 1) *
        routeCong B.Δ bh B.L + 1)
      = C * (w * (X.card + (G.inside X).length + 1) + 1) := by simp only [w]; ring
    _ ≤ C * (w * ((B.Δ + 2) * X.card) + X.card) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ hA) hX)
    _ = X.card * (C * (w * (B.Δ + 2) + 1)) := by ring

theorem branching_le_pow (x b j : ℕ) : branching x b j ≤ 2 ^ b := by
  by_cases h : 1 < groupSize x b j
  · rw [branching_eq h]
    exact min_le_left _ _
  · have h1 : groupSize x b j = 1 := by
      have := groupSize_pos (x := x) (b := b) (j := j)
      omega
    have : branching x b j ≤ groupSize x b j := Nat.div_le_self _ _
    have : 1 ≤ 2 ^ b := Nat.one_le_two_pow
    omega

theorem unitCost_mono {cfg : ParamConfig} {C bh k k' : ℕ} (h : k ≤ k') :
    B.unitCost cfg C bh k ≤ B.unitCost cfg C bh k' := by
  have hQ : B.routeUnit C bh k ≤ B.routeUnit C bh k' := by
    unfold routeUnit
    gcongr
  unfold unitCost
  gcongr

theorem arith_game (T k s A A' p ρ q : ℕ) (hp : p = k * s) (hρ : ρ ≤ p * q) :
    T * (k * (s * A * A') + 2 * ρ) + 2 * ρ ≤ p * (T * (A * A' + 2 * q) + 2 * q) := by
  have h1 : T * (k * (s * A * A') + 2 * ρ) ≤ T * (k * (s * A * A') + 2 * (p * q)) := by gcongr
  have h2 : p * (T * (A * A' + 2 * q) + 2 * q) =
      T * (k * (s * A * A') + 2 * (p * q)) + 2 * (p * q) := by
    rw [hp]; ring
  rw [h2]
  omega

theorem arith_conn (k p ρ q : ℕ) (hρ : ρ ≤ p * q) :
    k * k * (2 * ρ) ≤ p * (k * k * (2 * q)) := by
  have h1 : k * k * (2 * ρ) ≤ k * k * (2 * (p * q)) := by gcongr
  have h2 : p * (k * k * (2 * q)) = k * k * (2 * (p * q)) := by ring
  rw [h2]
  exact h1

/-- **The work at one group** is at most `|X| · F(k)`. -/
theorem groupCost_le {routeCost : RouterCostFn} (hrouter : IsMatchingPlayer B.route routeCost)
    {C : ℕ} (hC : RouteCostLe routeCost C)
    {cfg : ParamConfig} {coreCost : ℕ → Graph → ℕ} (hcore : IsCorePlayer cfg B.M B.r B.core coreCost)
    {H0 : Graph} {β : ℕ → ℝ} {bh : ℕ → ℕ} (hyp : B.BuildHyp cfg H0 β bh) {j g : ℕ}
    (hg : g < numGroups B.x B.b j) :
    B.groupCost routeCost coreCost H0 j g ≤
      groupSize B.x B.b j * B.unitCost cfg (C + 2) (bh j) (branching B.x B.b j) := by
  have hall := hostOK_all hrouter hcore hyp
  have hpks : groupSize B.x B.b j = branching B.x B.b j * groupSize B.x B.b (j + 1) :=
    groupSize_eq_mul_branching
  unfold groupCost
  by_cases hj : 1 < groupSize B.x B.b j
  · have hok := hall j g hj hg
    have hcard : (members B.x B.b j g).card = groupSize B.x B.b j := card_members g
    have hX : 1 ≤ (members B.x B.b j g).card := by rw [hcard]; omega
    have hconn := connCost_le_of hrouter hC hok.1 isChildren_members (hyp.β_pos _) hok.2.1 (hyp.bh_ge _)
    have hQ1 := routeBoundN_le (C := C + 2) hok.1 hX 1 (bh j)
    rw [hcard] at hQ1
    have hconn' := le_trans hconn (arith_conn _ _ _ _ hQ1)
    simp only [hj, ↓reduceIte]
    have hsplit : groupSize B.x B.b j * B.unitCost cfg (C + 2) (bh j) (branching B.x B.b j) =
        groupSize B.x B.b j * (B.T * ((NOf B.M B.r) ^ 2 * (WParam cfg B.M) ^ (10 * B.r ^ 2 + 10) +
          2 * B.routeUnit (C + 2) (bh j) (branching B.x B.b j)) + 2 * B.routeUnit (C + 2) (bh j) (branching B.x B.b j)) +
        groupSize B.x B.b j * (branching B.x B.b j * branching B.x B.b j *
          (2 * B.routeUnit (C + 2) (bh j) 1)) := by
      unfold unitCost
      rw [Nat.mul_add]
    rw [hsplit]
    by_cases hs : 1 < groupSize B.x B.b (j + 1)
    · simp only [hs, ↓reduceIte]
      have hsx : groupSize B.x B.b (j + 1) ≤ 2 ^ B.x := Nat.pow_le_pow_right (by norm_num) (by omega)
      have heven : groupSize B.x B.b (j + 1) % 2 = 0 := Nat.even_iff.mp (even_groupSize hs)
      have hsL : groupSize B.x B.b (j + 1) < 2 ^ B.L' :=
        lt_of_le_of_lt hsx (Nat.pow_lt_pow_right (by norm_num) hyp.x_lt_L')
      have hgame := gameCost_le hrouter hC hok.1 (hyp.β_pos _) hok.2.1 (hyp.bh_ge _) hcore isChildren_group
        branching_pos hs heven (hsx.trans hyp.size_le) hyp.core_deg hsL
      have hQk := routeBoundN_le (C := C + 2) hok.1 hX (branching B.x B.b j) (bh j)
      rw [hcard] at hQk
      exact Nat.add_le_add (le_trans hgame (arith_game _ _ _ _ _ _ _ _ hpks hQk)) hconn'
    · simp only [hs, ↓reduceIte, zero_add]
      exact le_trans hconn' (Nat.le_add_left _ _)
  · have hs : ¬ 1 < groupSize B.x B.b (j + 1) :=
      fun h => hj (lt_of_lt_of_le h (groupSize_succ_le _ _ _))
    simp only [hs, hj, ↓reduceIte, add_zero]
    exact Nat.zero_le _

/-- **The cost bound of the construction**: the work at all depths `j < D` is at most
`∑_{j < D} 2^x · F_j(2^b)`, where `F_j` uses the router scale `bh j` of depth `j`. -/
theorem buildCost_le {routeCost : RouterCostFn} (hrouter : IsMatchingPlayer B.route routeCost)
    {C : ℕ} (hC : RouteCostLe routeCost C)
    {cfg : ParamConfig} {coreCost : ℕ → Graph → ℕ} (hcore : IsCorePlayer cfg B.M B.r B.core coreCost)
    {H0 : Graph} {β : ℕ → ℝ} {bh : ℕ → ℕ} (hyp : B.BuildHyp cfg H0 β bh) (D : ℕ) :
    B.buildCost routeCost coreCost H0 D ≤
      ∑ j ∈ Finset.range D, 2 ^ B.x * B.unitCost cfg (C + 2) (bh j) (2 ^ B.b) := by
  unfold buildCost
  calc _ ≤ ∑ j ∈ Finset.range D, ∑ g ∈ Finset.range (numGroups B.x B.b j),
        groupSize B.x B.b j * B.unitCost cfg (C + 2) (bh j) (2 ^ B.b) := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro g hg
        refine le_trans (groupCost_le hrouter hC hcore hyp (Finset.mem_range.mp hg)) ?_
        exact Nat.mul_le_mul_left _ (unitCost_mono (branching_le_pow _ _ _))
    _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, ← Nat.mul_assoc,
          numGroups_mul_groupSize]

/-- **The cost bound** with the router's constant: there is `C` such that the work is at most
`∑_{j < D} 2^x · F_j(2^b)`. -/
theorem exists_buildCost_le {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer B.route routeCost) :
    ∃ C, ∀ {cfg : ParamConfig} {coreCost : ℕ → Graph → ℕ},
      IsCorePlayer cfg B.M B.r B.core coreCost →
      ∀ {H0 : Graph} {β : ℕ → ℝ} {bh : ℕ → ℕ}, B.BuildHyp cfg H0 β bh → ∀ D,
        B.buildCost routeCost coreCost H0 D ≤
          ∑ j ∈ Finset.range D, 2 ^ B.x * B.unitCost cfg C (bh j) (2 ^ B.b) := by
  obtain ⟨C, hC⟩ := hrouter.cost_bound
  exact ⟨C + 2, fun {cfg coreCost} hcore {H0 β bh} hyp D => buildCost_le hrouter hC hcore hyp D⟩

end BuildParams

end MinCostFlow.HierPaths
