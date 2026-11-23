module

public import MinCostFlow.ExpanderDecomp.Core
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Operation count of `OneShot` and `Core`, and its recurrence

This file defines the operation-count model for `OneShot` and `Core` (`oneShotCost`, `coreOnCost`,
`coreCost`), parameterized by the router cost `routeCost` and the fake-edge-removal cost
`removeFakeCost`, and proves that it satisfies the exact cost recurrence `coreOnCost_rec` and hence the
closed-form bound `coreTimeBound` via `Params.coreTimeBound_rec`.

Main definitions and results:
* `coreParamsOf` and `coreParamsValid_of_paramConfig`: instantiating `CoreParams` from
  `ParamConfig` whenever `4 ≤ cfg.a` and `r ≤ ell M`.
* `RouteCostBounded`, `RemoveFakeCostBounded`: explicit-constant forms of the router cost bound
  and the trimming cost bound.
* `oneShotCost`, `corePeelCost`, `coreOnCost`, `coreCost`: exact model operation counts following
  the control flow of `OneShot` and `Core`.
* `coreOnCost_rec`: the cost recurrence, bounding `coreOnCost` at level `q` by
  `c₀ · A · (N^{q+1} L^9 F^q + N L^2 F^q T_{q-1} + N^q L^4 F^{3q})`.
* `coreOnCost_le_coreTimeBound`: the closed-form bound, derived from `coreOnCost_rec` by induction on
  `q` using `coreTimeBound_rec`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-- Type of the operation-count function for `removeFake`: takes `(G, X, F_all, P_q)`. -/
abbrev RemoveFakeCostFn :=
  Graph → Finset ℕ → List (ℕ × ℕ) → ℕ → ℕ

/-- Explicit-constant form of the router cost bound. -/
def RouteCostBounded (routeCost : RouterCostFn) (C_route : ℕ) : Prop :=
  ∀ (G : Graph) (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)) (Δ L b z : ℕ),
    X ⊆ Finset.range G.n →
    (∀ e ∈ G.inside X, e.1 ≠ e.2) →
    1 ≤ Δ →
    (∀ v ∈ X, G.degIn X v ≤ Δ) →
    1 ≤ L →
    X.card < 2 ^ L →
    2 ≤ b →
    ValidTerminalPairs X pairs →
    routeCost G X pairs Δ L b z ≤
      C_route * (pairs.length * (X.card + (G.inside X).length + 1) *
        (routePathLen Δ b L + 1) * routeCong Δ b L + 1)

/-- Explicit-constant trimming cost bound (`O((|X| + e_X + |F| + 1) L^2 P_q^2)`). -/
def RemoveFakeCostBounded (removeFakeCost : RemoveFakeCostFn) (L C_trim : ℕ) : Prop :=
  ∀ (G : Graph) (X : Finset ℕ) (F : List (ℕ × ℕ)) (P_q : ℕ),
    X.card < 2 ^ L →
    removeFakeCost G X F P_q ≤
      C_trim * (X.card + (G.inside X).length + F.length + 1) * L ^ 2 * P_q ^ 2

/-- Concrete `CoreParams` obtained from `ParamConfig` at edge scale `M` and recursion depth `r`. -/
noncomputable def coreParamsOf (cfg : ParamConfig) (M r : ℕ) : CoreParams where
  N := NOf M r
  L := LParam M
  Δ := deltaParam M
  P := PParam cfg M
  D := DCore cfg M
  α := 1 / (cfg.a₀ : ℝ)

/-! ### Operation-count definitions mirroring `OneShot` and `Core` -/

/-- Operation count of one common round of Step B. -/
def stepBRoundCost (cfg : CoreParams) (routeCost : RouterCostFn) (G : Graph) (X : Finset ℕ)
    (vs : List ℕ) (b k z : ℕ) (subCore : Graph → Finset ℕ → CoreResult)
    (subCoreCost : Graph → Finset ℕ → ℕ) (st : BlockGameState) : ℕ :=
  let rpairs := activeCutPairs G vs b k subCore st
  let pairs := rpairs.map Prod.snd
  let queryCost := ∑ i ∈ (Finset.range k).filter fun i => st.active i,
    subCoreCost (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i))) (blockSet vs b i)
  let rCost := if rpairs.isEmpty then 0 else routeCost G X pairs cfg.Δ cfg.L 100 z
  queryCost + rCost + (2 * X.card + 2)

/-- Operation count of `t` rounds of Step B. -/
def stepBRunRoundsCost (cfg : CoreParams) (route : RouterFn) (routeCost : RouterCostFn)
    (G : Graph) (X : Finset ℕ) (vs : List ℕ) (b k z : ℕ)
    (subCore : Graph → Finset ℕ → CoreResult) (subCoreCost : Graph → Finset ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 =>
      stepBRunRoundsCost cfg route routeCost G X vs b k z subCore subCoreCost t +
        match stepBRunRounds cfg route G X vs b k z subCore t with
        | Sum.inl _ => 0
        | Sum.inr st => stepBRoundCost cfg routeCost G X vs b k z subCore subCoreCost st

/-- Operation count of Step B (all rounds plus the complement-injection routing call). -/
def stepBCost (cfg : CoreParams) (route : RouterFn) (routeCost : RouterCostFn)
    (G : Graph) (X : Finset ℕ) (vs : List ℕ) (b k z : ℕ)
    (subCore : Graph → Finset ℕ → CoreResult) (subCoreCost : Graph → Finset ℕ → ℕ) : ℕ :=
  stepBRunRoundsCost cfg route routeCost G X vs b k z subCore subCoreCost (49 * cfg.L + 1) +
    match stepBRunRounds cfg route G X vs b k z subCore (49 * cfg.L + 1) with
    | Sum.inl _ => 0
    | Sum.inr st =>
        let injPairs := (List.range k).map fun i => (blockSet vs b i \ st.savedS i, st.savedS i)
        routeCost G X injPairs cfg.Δ cfg.L 100 z + (X.card + 1)

/-- Operation count of one colour class in Step C. -/
def stepCMacroColorCost (cfg : CoreParams) (routeCost : RouterCostFn) (G : Graph) (X : Finset ℕ)
    (vs : List ℕ) (b z : ℕ) (Ec : List (ℕ × ℕ)) : ℕ :=
  if Ec.isEmpty then
    1
  else
    let pairs := Ec.map fun e => (blockSet vs b e.1, blockSet vs b e.2)
    routeCost G X pairs cfg.Δ cfg.L 100 z + (X.card + 1)

/-- Operation count of the first `m` colours of Step C. -/
def stepCMacroLoopCost (cfg : CoreParams) (route : RouterFn) (routeCost : RouterCostFn)
    (G : Graph) (X : Finset ℕ) (vs : List ℕ) (b z : ℕ)
    (colored : List ((ℕ × ℕ) × ℕ)) : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
      stepCMacroLoopCost cfg route routeCost G X vs b z colored m +
        match stepCMacroLoop cfg route G X vs b z colored m with
        | Sum.inl _ => 0
        | Sum.inr _ => stepCMacroColorCost cfg routeCost G X vs b z (colorClass colored m)

/-- Operation count of Step C's macro-expander construction, 17-colouring, and routing. -/
def stepCMacroCost (cfg : CoreParams) (route : RouterFn) (routeCost : RouterCostFn)
    (cloud : ℕ → Graph) (G : Graph) (X : Finset ℕ) (vs : List ℕ) (b k z : ℕ) : ℕ :=
  if 2 ≤ k then
    (200 * k + 1) + stepCMacroLoopCost cfg route routeCost G X vs b z (edgeColor17 (cloud k)) 17
  else
    1

/-- Operation count of Step C's leftover injection. -/
def stepCLeftoverCost (cfg : CoreParams) (routeCost : RouterCostFn) (G : Graph) (X : Finset ℕ)
    (vs : List ℕ) (b z : ℕ) : ℕ :=
  if (leftoverVerts vs b).Nonempty then
    routeCost G X [(leftoverVerts vs b, fullVerts vs b)] cfg.Δ cfg.L 100 z + (X.card + 1)
  else
    1

/-- Operation count of `oneShot` (Steps A–D). -/
def oneShotCost (cfg : CoreParams) (route : RouterFn) (routeCost : RouterCostFn)
    (removeFakeCost : RemoveFakeCostFn) (cloud : ℕ → Graph) (q : ℕ)
    (subCore : Graph → Finset ℕ → CoreResult) (subCoreCost : Graph → Finset ℕ → ℕ)
    (G : Graph) (X : Finset ℕ) : ℕ :=
  let vs := X.sort (· ≤ ·)
  let b := if q = 1 then 1 else cfg.N ^ (q - 1) / 2
  let k := numFullBlocks vs b
  let z := X.card / cfg.D q
  let resB : Finset ℕ ⊕ List RoutedCall :=
    if q = 1 then Sum.inr [] else stepB cfg route G X vs b k z subCore
  let costB := if q = 1 then 1 else stepBCost cfg route routeCost G X vs b k z subCore subCoreCost
  (X.card + 1) + costB +
    match resB with
    | Sum.inl _ => 0
    | Sum.inr callsB =>
        stepCMacroCost cfg route routeCost cloud G X vs b k z +
          match stepCMacro cfg route cloud G X vs b k z with
          | Sum.inl _ => 0
          | Sum.inr callsC =>
              stepCLeftoverCost cfg routeCost G X vs b z +
                match stepCLeftover cfg route G X vs b z with
                | Sum.inl _ => 0
                | Sum.inr callsZ =>
                    removeFakeCost G X (callsFakeEdges (callsB ++ callsC ++ callsZ)) (cfg.P q)

/-- Operation count of the peeling loop `corePeel`. -/
noncomputable def corePeelCost (cfg : CoreParams) (route : RouterFn) (routeCost : RouterCostFn)
    (removeFakeCost : RemoveFakeCostFn) (cloud : ℕ → Graph) (q : ℕ)
    (subCore : Graph → Finset ℕ → CoreResult) (subCoreCost : Graph → Finset ℕ → ℕ)
    (G : Graph) (X : Finset ℕ) : ℕ → Finset ℕ → ℕ
  | 0, _ => 1
  | fuel + 1, U =>
      if X.card ≤ 4 * U.card then
        1
      else
        oneShotCost cfg route routeCost removeFakeCost cloud q subCore subCoreCost G (X \ U) +
          (X.card + 1) +
          match oneShot cfg route cloud q subCore G (X \ U) with
          | .expander _ => 0
          | .cut V =>
              corePeelCost cfg route routeCost removeFakeCost cloud q subCore subCoreCost G X fuel
                (U ∪ smallerSide (X \ U) V)

/-- Operation count of `coreOn`. -/
noncomputable def coreOnCost (cfg : CoreParams) (route : RouterFn) (routeCost : RouterCostFn)
    (removeFakeCost : RemoveFakeCostFn) (cloud : ℕ → Graph) : ℕ → Graph → Finset ℕ → ℕ
  | 0, _, _ => 1
  | q + 1, G, X =>
      if X.card ≤ 1 then
        1
      else if X.card ≤ cfg.N ^ q then
        1 + coreOnCost cfg route routeCost removeFakeCost cloud q G X
      else
        corePeelCost cfg route routeCost removeFakeCost cloud (q + 1)
          (coreOn cfg route cloud q)
          (coreOnCost cfg route routeCost removeFakeCost cloud q)
          G X (2 * cfg.D (q + 1)) ∅

/-- Operation count of `core` on `G.verts`. -/
noncomputable def coreCost (cfg : CoreParams) (route : RouterFn) (routeCost : RouterCostFn)
    (removeFakeCost : RemoveFakeCostFn) (cloud : ℕ → Graph) (q : ℕ) (G : Graph) : ℕ :=
  coreOnCost cfg route routeCost removeFakeCost cloud q G G.verts

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Instantiating `CoreParamsValid` from `ParamConfig` -/

theorem routePathLen_core_eq (M : ℕ) :
    routePathLen (deltaParam M) 100 (LParam M) = dCore M := by
  unfold routePathLen dCore
  ring

theorem routeCong_core_eq (M : ℕ) :
    routeCong (deltaParam M) 100 (LParam M) = RCore M := by
  unfold routeCong routeBatchH RCore
  rw [routePathLen_core_eq]

/-- `coreParamsOf cfg M r` satisfies `CoreParamsValid` whenever `4 ≤ cfg.a` (so `60 ≤ cfg.A`)
and `r ≤ ell M`. -/
theorem coreParamsValid_of_paramConfig (cfg : ParamConfig) (M r : ℕ)
    (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) :
    CoreParamsValid (coreParamsOf cfg M r) r where
  hNpos := lt_of_lt_of_le (by decide) (four_le_NOf M r)
  hN4 := four_dvd_NOf M r
  hL := le_trans (by decide) (four_le_LParam M)
  hΔ := by
    show 49 * LParam M + 20 ≤ deltaParam M
    unfold deltaParam tParam
    have := four_le_LParam M
    omega
  hα0 := by
    show (0 : ℝ) < 1 / (cfg.a₀ : ℝ)
    have : (0 : ℝ) < cfg.a₀ := Nat.cast_pos.mpr cfg.ha₀
    positivity
  hα1 := by
    show 1 / (cfg.a₀ : ℝ) ≤ 1
    have hpos : (0 : ℝ) < cfg.a₀ := Nat.cast_pos.mpr cfg.ha₀
    rw [div_le_one hpos]
    exact_mod_cast cfg.ha₀
  hP0 := one_le_PParam cfg M 0
  hPmono q _ := by
    show PParam cfg M q ≤ PParam cfg M (q + 1)
    unfold PParam
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ (one_le_FParam cfg M)
  hP12 q hq _ := by
    show 12 ≤ PParam cfg M q
    exact Nat.le_of_dvd (one_le_PParam cfg M q) (twelve_dvd_PParam cfg M hq)
  hPstep q hq _ := by
    show 960 * (PParam cfg M (q - 1) : ℝ) * (deltaParam M : ℝ) ^ 2 *
        (routeCong (deltaParam M) 100 (LParam M) : ℝ) ≤
      (1 / (cfg.a₀ : ℝ)) * (PParam cfg M q : ℝ)
    rw [routeCong_core_eq]
    have ha0 : (0 : ℝ) < cfg.a₀ := Nat.cast_pos.mpr cfg.ha₀
    have hsplit : PParam cfg M q = PParam cfg M (q - 1) * FParam cfg M := by
      unfold PParam
      conv_lhs => rw [show q = (q - 1) + 1 by omega, pow_succ]
    rw [hsplit]
    have hmul : (1 / (cfg.a₀ : ℝ)) * ((PParam cfg M (q - 1) * FParam cfg M : ℕ) : ℝ) =
        1920 * (PParam cfg M (q - 1) : ℝ) * (deltaParam M : ℝ) ^ 2 * (RCore M : ℝ) := by
      unfold FParam
      push_cast
      have ha0ne : (cfg.a₀ : ℝ) ≠ 0 := ha0.ne'
      field_simp
    rw [hmul]
    have hnn : (0 : ℝ) ≤ (PParam cfg M (q - 1) : ℝ) * (deltaParam M : ℝ) ^ 2 * (RCore M : ℝ) := by
      positivity
    linarith
  hD q _ _ := by
    show 60 * deltaParam M * PParam cfg M q ≤ DCore cfg M q
    unfold DCore ParamConfig.A
    have h60 : 60 ≤ 16 * cfg.a := by omega
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h60)
  hNrL := by
    show (NOf M r) ^ r < 2 ^ LParam M
    rcases Nat.eq_zero_or_pos r with rfl | hr1
    · simp only [pow_zero]
      have h4 : 4 ≤ LParam M := four_le_LParam M
      have h16 : 2 ^ 4 ≤ 2 ^ LParam M := Nat.pow_le_pow_right (by decide) h4
      omega
    · have hle := NOf_pow_add_two_le_two_pow_L M hr1 hrl
      omega

/-! ### Arithmetic helpers for the cost recurrence -/

private lemma dCore_add_one_le (M : ℕ) :
    dCore M + 1 ≤ ParamConfig.d0 * (LParam M) ^ 2 := by
  unfold dCore deltaParam tParam ParamConfig.d0
  have hL : 1 ≤ (LParam M) ^ 2 := by
    have := four_le_LParam M; nlinarith
  have heq : 3200 * (1024 * LParam M) * LParam M = 3276800 * (LParam M) ^ 2 := by ring
  omega

private lemma RCore_le (M : ℕ) :
    RCore M ≤ ParamConfig.R0 * (LParam M) ^ 4 := by
  unfold RCore deltaParam tParam ParamConfig.R0
  have hd := dCore_add_one_le M
  calc 1600 * (1024 * LParam M) * (dCore M + 1) * LParam M
      ≤ 1600 * (1024 * LParam M) * (ParamConfig.d0 * (LParam M) ^ 2) * LParam M :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hd)
    _ = 1600 * 1024 * ParamConfig.d0 * (LParam M) ^ 4 := by ring

/-- When `G` has max degree `≤ Δ` on `X`, `(G.inside X).length * 2 ≤ Δ * X.card`. -/
private lemma two_mul_inside_le {G : Graph} {X : Finset ℕ} {Δ : ℕ}
    (hdeg : ∀ v ∈ X, G.degIn X v ≤ Δ) :
    2 * (G.inside X).length ≤ Δ * X.card := by
  rw [← volIn_self]
  exact volIn_le_mul_card (Finset.Subset.refl X) hdeg

/-- Single routing call bound when `pairs.length ≤ 2 * N` and `2 ≤ X.card ≤ N ^ q`. -/
private lemma single_routeCost_le {M r q C_route : ℕ}
    {routeCost : RouterCostFn} (hrc : RouteCostBounded routeCost C_route)
    {G : Graph} {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)} {z : ℕ}
    (hX : X ⊆ Finset.range G.n) (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ deltaParam M) (hXL : X.card < 2 ^ LParam M)
    (hX2 : 2 ≤ X.card) (hXle : X.card ≤ (NOf M r) ^ q)
    (hpairs : ValidTerminalPairs X pairs) (hplen : pairs.length ≤ 2 * NOf M r) :
    routeCost G X pairs (deltaParam M) (LParam M) 100 z ≤
      3 * C_route * 1024 * ParamConfig.d0 * ParamConfig.R0 *
        (NOf M r) ^ (q + 1) * (LParam M) ^ 7 := by
  have hL4 : 4 ≤ LParam M := four_le_LParam M
  have hN4 : 4 ≤ NOf M r := four_le_NOf M r
  have hΔ : 1 ≤ deltaParam M := one_le_tParam M
  have hbase := hrc G X pairs (deltaParam M) (LParam M) 100 z hX hGloop hΔ hdegG
    (by omega) hXL (by decide) hpairs
  rw [routePathLen_core_eq, routeCong_core_eq] at hbase
  have hins : X.card + (G.inside X).length + 1 ≤ 1024 * LParam M * X.card := by
    have h2 := two_mul_inside_le hdegG
    unfold deltaParam tParam at h2
    have hsplit : 1024 * LParam M * X.card = 2 * (512 * LParam M * X.card) := by ring
    have h1 : (G.inside X).length ≤ 512 * LParam M * X.card := by omega
    have h3 : X.card + 1 ≤ 512 * LParam M * X.card := by nlinarith
    omega
  have hinsN : X.card + (G.inside X).length + 1 ≤ 1024 * LParam M * (NOf M r) ^ q :=
    le_trans hins (Nat.mul_le_mul_left _ hXle)
  have hd := dCore_add_one_le M
  have hR := RCore_le M
  set B := 1024 * ParamConfig.d0 * ParamConfig.R0 * (NOf M r) ^ (q + 1) * (LParam M) ^ 7
  have hBpos : 1 ≤ B := by
    have h1 : 1 ≤ 1024 * ParamConfig.d0 * ParamConfig.R0 := by
      unfold ParamConfig.R0 ParamConfig.d0; decide
    have h2 : 1 ≤ (NOf M r) ^ (q + 1) := Nat.one_le_pow _ _ (by omega)
    have h3 : 1 ≤ (LParam M) ^ 7 := Nat.one_le_pow _ _ (by omega)
    calc 1 = 1 * 1 * 1 := by decide
      _ ≤ 1024 * ParamConfig.d0 * ParamConfig.R0 * (NOf M r) ^ (q + 1) * (LParam M) ^ 7 :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have hprod : pairs.length * (X.card + (G.inside X).length + 1) * (dCore M + 1) * RCore M ≤
      2 * B := by
    calc pairs.length * (X.card + (G.inside X).length + 1) * (dCore M + 1) * RCore M
        ≤ (2 * NOf M r) * (1024 * LParam M * (NOf M r) ^ q) *
            (ParamConfig.d0 * (LParam M) ^ 2) * (ParamConfig.R0 * (LParam M) ^ 4) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hplen hinsN) hd) hR
      _ = 2 * B := by dsimp only [B]; ring
  calc routeCost G X pairs (deltaParam M) (LParam M) 100 z
      ≤ C_route * (pairs.length * (X.card + (G.inside X).length + 1) *
          (dCore M + 1) * RCore M + 1) := hbase
    _ ≤ C_route * (2 * B + B) := Nat.mul_le_mul_left _ (Nat.add_le_add hprod hBpos)
    _ = 3 * C_route * 1024 * ParamConfig.d0 * ParamConfig.R0 *
          (NOf M r) ^ (q + 1) * (LParam M) ^ 7 := by dsimp only [B]; ring

/-- Size bound on a colour class of a graph on `k` vertices: a matching has at most `k` edges. -/
private lemma colorClass_length_le {Ec : List (ℕ × ℕ)} {k : ℕ}
    (hvalid : ∀ e ∈ Ec, e.1 < k ∧ e.2 < k)
    (hnd : (Ec.flatMap fun e => [e.1, e.2]).Nodup) : Ec.length ≤ k := by
  have hsub : (Ec.flatMap fun e => [e.1, e.2]).toFinset ⊆ Finset.range k := by
    intro v hv
    rw [List.mem_toFinset, List.mem_flatMap] at hv
    obtain ⟨e, he, hm⟩ := hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact Finset.mem_range.mpr (hvalid e he).1
    · exact Finset.mem_range.mpr (hvalid e he).2
  have hlen : (Ec.flatMap fun e => [e.1, e.2]).length = 2 * Ec.length := by
    induction Ec with
    | nil => simp
    | cons _ rest _ => simp [List.flatMap_cons]; omega
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, hlen, Finset.card_range] at hcard
  omega

/-- Whenever all three stages of `oneShot` succeed (returning `callsB`, `callsC`, `callsZ`), the
total number of fake edges passed to Step D is at most `|X|`. -/
private lemma oneShot_callsFakeEdges_length_le {cp : CoreParams} {r q : ℕ}
    (hcfg : CoreParamsValid cp r) (hq1 : 1 ≤ q) (hqr : q ≤ r)
    {route : RouterFn} {routeCost : RouterCostFn} (hroute : IsMatchingPlayer route routeCost)
    {cloud : ℕ → Graph} (hcloud : IsCloudExpander cloud cp.α)
    {subCore : Graph → Finset ℕ → CoreResult}
    (hsubCore : 2 ≤ q → ∀ W Y, Y ⊆ Finset.range W.n → W.IsValid →
      (∀ e ∈ W.inside Y, e.1 ≠ e.2) →
      Y.card ≤ cp.N ^ (q - 1) → (∀ v ∈ Y, W.degIn Y v ≤ cp.Δ) →
      CoreSpec cp (q - 1) W Y (subCore W Y))
    {G : Graph} {X : Finset ℕ}
    (hX : X ⊆ Finset.range G.n) (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ cp.Δ)
    (hsize : (q = 1 → 2 ≤ X.card ∧ X.card ≤ cp.N) ∧
      (2 ≤ q → cp.N ^ (q - 1) / 2 ≤ X.card ∧ X.card ≤ cp.N ^ q))
    {callsB callsC callsZ : List RoutedCall}
    (hB : (if q = 1 then Sum.inr []
      else stepB cp route G X (X.sort (· ≤ ·)) (if q = 1 then 1 else cp.N ^ (q - 1) / 2)
        (numFullBlocks (X.sort (· ≤ ·)) (if q = 1 then 1 else cp.N ^ (q - 1) / 2))
        (X.card / cp.D q) subCore) = Sum.inr callsB)
    (hC : stepCMacro cp route cloud G X (X.sort (· ≤ ·)) (if q = 1 then 1 else cp.N ^ (q - 1) / 2)
      (numFullBlocks (X.sort (· ≤ ·)) (if q = 1 then 1 else cp.N ^ (q - 1) / 2))
      (X.card / cp.D q) = Sum.inr callsC)
    (hZ : stepCLeftover cp route G X (X.sort (· ≤ ·)) (if q = 1 then 1 else cp.N ^ (q - 1) / 2)
      (X.card / cp.D q) = Sum.inr callsZ) :
    (callsFakeEdges (callsB ++ callsC ++ callsZ)).length ≤ X.card := by
  set vs := X.sort (· ≤ ·)
  have hnd : vs.Nodup := Finset.sort_nodup X (· ≤ ·)
  have hvs : vs.toFinset = X := by ext v; simp [vs]
  have hvslen : vs.length = X.card := Finset.length_sort (· ≤ ·)
  set b := if q = 1 then 1 else cp.N ^ (q - 1) / 2
  set k := numFullBlocks vs b
  set z := X.card / cp.D q
  have hXle : X.card ≤ cp.N ^ q := by
    by_cases hq : q = 1
    · subst hq; simpa using (hsize.1 rfl).2
    · exact (hsize.2 (by omega)).2
  have hXL : X.card < 2 ^ cp.L := lt_of_le_of_lt hXle (hcfg.hNq_lt_two_pow hqr)
  have hparams : 0 < b ∧ b ≤ vs.length ∧ 1 ≤ k := by
    by_cases hq : q = 1
    · have h1 := hsize.1 hq
      have hb1 : b = 1 := by simp [b, hq]
      have hk_eq : k = vs.length := by simp [k, hb1, numFullBlocks]
      exact ⟨by omega, by omega, by omega⟩
    · have hq2 : 2 ≤ q := by omega
      have h2 := hsize.2 hq2
      have hbe : b = cp.N ^ (q - 1) / 2 := by simp [b, hq]
      have hsp := stepA_block_params hnd hq2 hcfg.hNpos hcfg.hN4
        (by rw [hvslen]; exact h2.1) (by rw [hvslen]; exact h2.2)
      exact ⟨by rw [hbe]; exact hsp.1, by rw [hbe, hvslen]; exact h2.1,
        by show 1 ≤ numFullBlocks vs b; rw [hbe]; exact hsp.2.2.1⟩
  obtain ⟨hb_pos, hble, hk1⟩ := hparams
  have hPprev_pos : (0 : ℝ) < cp.P (q - 1) :=
    Nat.cast_pos.mpr (hcfg.hP_pos (by omega : q - 1 ≤ r))
  have hβ0 : 0 ≤ 1 / (2 * (cp.P (q - 1) : ℝ)) := by positivity
  have hβ1 : 1 / (2 * (cp.P (q - 1) : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ cp.P (q - 1) := by exact_mod_cast hcfg.hP_pos (by omega : q - 1 ≤ r)
    linarith
  have hBsp : callsB.length ≤ 49 * cp.L + 2 ∧
      (∀ c ∈ callsB, c.Valid G X (routeCong cp.Δ 100 cp.L) z) ∧
      ∀ i < k, (Graph.mk G.n (callsWitnessEdges callsB)).IsExpansionExpanderOn
        (blockSet vs b i) (1 / (2 * (cp.P (q - 1) : ℝ))) := by
    by_cases hq : q = 1
    · simp only [hq, ↓reduceIte, Sum.inr.injEq] at hB
      subst hB
      have hb1 : b = 1 := by simp [b, hq]
      refine ⟨by simp, by simp, fun i hi => ?_⟩
      exact isExpansionExpanderOn_of_card_le_one _ (by rw [card_blockSet hnd hi, hb1]) _
    · simp only [hq, ↓reduceIte] at hB
      have hq2 : 2 ≤ q := by omega
      have h2 := hsize.2 hq2
      have hbe : b = cp.N ^ (q - 1) / 2 := by simp [b, hq]
      have hsp := stepA_block_params hnd hq2 hcfg.hNpos hcfg.hN4
        (by rw [hvslen]; exact h2.1) (by rw [hvslen]; exact h2.2)
      have hb_even : Even b := hbe ▸ hsp.2.1
      have hb_le : b ≤ cp.N ^ (q - 1) := by rw [hbe]; exact Nat.div_le_self _ 2
      have hsb := stepB_spec hcfg hq2 hqr hroute hX hGloop hdegG hXL hnd hvs hb_pos
        hb_even hb_le (hsubCore hq2) (z := z)
      rw [hB] at hsb
      exact hsb
  have hCsp := stepCMacro_spec hcfg hroute hcloud (z := z) hX hGloop hdegG hXL hnd hvs hb_pos hk1
    hβ0 hβ1 hBsp.2.2
  rw [hC] at hCsp
  have hγ_eq : cp.α * (1 / (2 * (cp.P (q - 1) : ℝ))) / 10 =
      cp.α / (20 * (cp.P (q - 1) : ℝ)) := by ring
  rw [hγ_eq] at hCsp
  have hγ0 : 0 ≤ cp.α / (20 * (cp.P (q - 1) : ℝ)) := by
    have := hcfg.hα0; positivity
  have hγ1 : cp.α / (20 * (cp.P (q - 1) : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have h1 : (1 : ℝ) ≤ cp.P (q - 1) := by exact_mod_cast hcfg.hP_pos (by omega : q - 1 ≤ r)
    have h2 := hcfg.hα1
    nlinarith
  have hZsp := stepCLeftover_spec hcfg hroute (z := z) hX hGloop hdegG hXL hnd hvs hb_pos hble
    hγ0 hγ1 hCsp.2.2
  rw [hZ] at hZsp
  set callsAll := callsB ++ callsC ++ callsZ
  have hlen_all : callsAll.length ≤ cp.Δ := by
    have hΔ := hcfg.hΔ
    simp only [callsAll, List.length_append]
    omega
  have hvalid_all : ∀ c ∈ callsAll, c.Valid G X (routeCong cp.Δ 100 cp.L) z := by
    intro c hc
    simp only [callsAll, List.mem_append] at hc
    rcases hc with (h1 | h2) | h3
    · exact hBsp.2.1 c h1
    · exact hCsp.2.1 c h2
    · exact hZsp.2.1 c h3
  have h1 := (embed_calls callsAll hvalid_all).1
  have h2 : callsAll.length * z ≤ cp.Δ * z := Nat.mul_le_mul_right z hlen_all
  have hΔleD : cp.Δ ≤ cp.D q := by
    have := hcfg.hD q hq1 hqr
    have hP := hcfg.hP_pos hqr
    have hmul : cp.Δ ≤ 60 * cp.Δ * cp.P q := by
      calc cp.Δ = 1 * cp.Δ * 1 := by ring
        _ ≤ 60 * cp.Δ * cp.P q :=
          Nat.mul_le_mul (Nat.mul_le_mul (by decide) (le_refl _)) hP
    omega
  have h3 : cp.Δ * z ≤ cp.D q * z := Nat.mul_le_mul_right z hΔleD
  have h4 : cp.D q * z ≤ X.card := Nat.mul_div_le X.card (cp.D q)
  omega

/-! ### Bounding one `OneShot` call -/

private lemma oneShotCost_le {cfg : ParamConfig} {M r q C_route C_trim Tprev : ℕ}
    (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq1 : 1 ≤ q) (hqr : q ≤ r)
    {route : RouterFn} {routeCost : RouterCostFn} (hroute : IsMatchingPlayer route routeCost)
    (hrc : RouteCostBounded routeCost C_route)
    {removeFakeCost : RemoveFakeCostFn}
    (hrfc : RemoveFakeCostBounded removeFakeCost (LParam M) C_trim)
    {cloud : ℕ → Graph} (hcloud : IsCloudExpander cloud (1 / (cfg.a₀ : ℝ)))
    {subCore : Graph → Finset ℕ → CoreResult} {subCoreCost : Graph → Finset ℕ → ℕ}
    (hsubCore : 2 ≤ q → ∀ W Y, Y ⊆ Finset.range W.n → W.IsValid →
      (∀ e ∈ W.inside Y, e.1 ≠ e.2) →
      Y.card ≤ (NOf M r) ^ (q - 1) → (∀ v ∈ Y, W.degIn Y v ≤ deltaParam M) →
      CoreSpec (coreParamsOf cfg M r) (q - 1) W Y (subCore W Y))
    (hsubCost : 2 ≤ q → ∀ W Y, Y ⊆ Finset.range W.n → W.IsValid →
      (∀ e ∈ W.inside Y, e.1 ≠ e.2) →
      Y.card ≤ (NOf M r) ^ (q - 1) → (∀ v ∈ Y, W.degIn Y v ≤ deltaParam M) →
      subCoreCost W Y ≤ Tprev)
    {G : Graph} {X : Finset ℕ}
    (hX : X ⊆ Finset.range G.n) (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ deltaParam M)
    (hsize : (q = 1 → 2 ≤ X.card ∧ X.card ≤ NOf M r) ∧
      (2 ≤ q → (NOf M r) ^ (q - 1) / 2 ≤ X.card ∧ X.card ≤ (NOf M r) ^ q)) :
    oneShotCost (coreParamsOf cfg M r) route routeCost removeFakeCost cloud q subCore subCoreCost
        G X + 2 * (X.card + 1) ≤
      (207 * C_route + 1) * 1024 * ParamConfig.d0 * ParamConfig.R0 *
          (NOf M r) ^ (q + 1) * (LParam M) ^ 8 +
        100 * NOf M r * LParam M * Tprev +
        2048 * C_trim * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) := by
  have hcfg := coreParamsValid_of_paramConfig cfg M r ha hrl
  set cp := coreParamsOf cfg M r
  set vs := X.sort (· ≤ ·)
  have hnd : vs.Nodup := Finset.sort_nodup X (· ≤ ·)
  have hvs : vs.toFinset = X := by ext v; simp [vs]
  have hvslen : vs.length = X.card := Finset.length_sort (· ≤ ·)
  set b := if q = 1 then 1 else (NOf M r) ^ (q - 1) / 2
  set k := numFullBlocks vs b
  set z := X.card / DCore cfg M q
  have hL4 : 4 ≤ LParam M := four_le_LParam M
  have hN4 : 4 ≤ NOf M r := four_le_NOf M r
  have hXle : X.card ≤ (NOf M r) ^ q := by
    by_cases hq : q = 1
    · subst hq; simpa using (hsize.1 rfl).2
    · exact (hsize.2 (by omega)).2
  have hXL : X.card < 2 ^ LParam M := lt_of_le_of_lt hXle (hcfg.hNq_lt_two_pow hqr)
  have hparams : 0 < b ∧ b ≤ vs.length ∧ 1 ≤ k ∧ k ≤ 2 * NOf M r ∧ 2 ≤ X.card := by
    by_cases hq : q = 1
    · have h1 := hsize.1 hq
      have hb1 : b = 1 := by simp [b, hq]
      have hk_eq : k = vs.length := by simp [k, hb1, numFullBlocks]
      exact ⟨by omega, by omega, by omega, by omega, h1.1⟩
    · have hq2 : 2 ≤ q := by omega
      have h2 := hsize.2 hq2
      have hbe : b = (NOf M r) ^ (q - 1) / 2 := by simp [b, hq]
      have hsp := stepA_block_params hnd hq2 hcfg.hNpos hcfg.hN4
        (by rw [hvslen]; exact h2.1) (by rw [hvslen]; exact h2.2)
      have hpow4 : 4 ≤ (NOf M r) ^ (q - 1) := by
        calc 4 ≤ NOf M r := hN4
          _ = (NOf M r) ^ 1 := (pow_one _).symm
          _ ≤ (NOf M r) ^ (q - 1) := Nat.pow_le_pow_right hcfg.hNpos (by omega)
      have hb2 : 2 ≤ b := by rw [hbe]; omega
      exact ⟨by rw [hbe]; exact hsp.1, by rw [hbe, hvslen]; exact h2.1,
        by show 1 ≤ numFullBlocks vs b; rw [hbe]; exact hsp.2.2.1,
        by show numFullBlocks vs b ≤ 2 * NOf M r; rw [hbe]; exact hsp.2.2.2.1, by omega⟩
  obtain ⟨hb_pos, hble, hk1, hkle, hX2⟩ := hparams
  -- Single routing call upper bound `R1`.
  set R1 := 3 * C_route * 1024 * ParamConfig.d0 * ParamConfig.R0 *
    (NOf M r) ^ (q + 1) * (LParam M) ^ 7
  have hroute1 : ∀ pairs, ValidTerminalPairs X pairs → pairs.length ≤ 2 * NOf M r →
      routeCost G X pairs (deltaParam M) (LParam M) 100 z ≤ R1 :=
    fun pairs hp hl => single_routeCost_le hrc hX hGloop hdegG hXL hX2 hXle hp hl
  -- Step B cost bound.
  have hcostB : (if q = 1 then 1 else stepBCost cp route routeCost G X vs b k z subCore subCoreCost) ≤
      (49 * LParam M + 2) * R1 + 100 * NOf M r * LParam M * Tprev +
        (49 * LParam M + 2) * (2 * X.card + 2) := by
    by_cases hq : q = 1
    · simp only [hq, ↓reduceIte]
      have : 1 ≤ (49 * LParam M + 2) * (2 * X.card + 2) :=
        Nat.mul_le_mul (by omega : 1 ≤ 49 * LParam M + 2) (by omega : 1 ≤ 2 * X.card + 2)
      omega
    · simp only [hq, ↓reduceIte]
      have hq2 : 2 ≤ q := by omega
      have h2 := hsize.2 hq2
      have hbe : b = (NOf M r) ^ (q - 1) / 2 := by simp [b, hq]
      have hsp := stepA_block_params hnd hq2 hcfg.hNpos hcfg.hN4
        (by rw [hvslen]; exact h2.1) (by rw [hvslen]; exact h2.2)
      have hb_even : Even b := hbe ▸ hsp.2.1
      have hb_le : b ≤ (NOf M r) ^ (q - 1) := by rw [hbe]; exact Nat.div_le_self _ 2
      have hrounds : ∀ t ≤ 49 * LParam M + 1,
          stepBRunRoundsCost cp route routeCost G X vs b k z subCore subCoreCost t ≤
            t * (k * Tprev + R1 + (2 * X.card + 2)) := by
        intro t ht
        induction t with
        | zero => simp [stepBRunRoundsCost]
        | succ t ih =>
          unfold stepBRunRoundsCost
          have hprev := ih (Nat.le_of_succ_le ht)
          cases hst : stepBRunRounds cp route G X vs b k z subCore t with
          | inl _ =>
            rw [Nat.add_zero]
            exact le_trans hprev (Nat.mul_le_mul_right _ (Nat.le_succ t))
          | inr st =>
            have hsv := stepBRunRounds_state_valid hcfg hroute hX hGloop hdegG hXL hnd hvs
              hb_pos hb_even hb_le (hsubCore hq2) (Nat.le_of_succ_le ht) hst
            have hqcost : (∑ i ∈ (Finset.range k).filter fun i => st.active i,
                subCoreCost (Graph.mk G.n (witnessEdges (st.rounds i) (st.numRounds i)))
                  (blockSet vs b i)) ≤ k * Tprev := by
              calc _ ≤ ∑ _i ∈ (Finset.range k).filter fun i => st.active i, Tprev := by
                    apply Finset.sum_le_sum
                    intro i hi
                    have hik : i < k := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
                    obtain ⟨h1, h2, h3, h4, h5⟩ := hsv.1 i hik
                    exact hsubCost hq2 _ _ h1 h2 h3 h4 h5
                _ = ((Finset.range k).filter fun i => st.active i).card * Tprev := by
                    rw [Finset.sum_const, smul_eq_mul]
                _ ≤ k * Tprev := Nat.mul_le_mul_right _
                    (le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_range]))
            have hrcost : (if (activeCutPairs G vs b k subCore st).isEmpty then 0
                else routeCost G X ((activeCutPairs G vs b k subCore st).map Prod.snd)
                  cp.Δ cp.L 100 z) ≤ R1 := by
              split_ifs with hempty
              · exact Nat.zero_le _
              · obtain ⟨hvp, hlen⟩ := hsv.2.1 (by show t ≤ 49 * LParam M; omega)
                exact hroute1 _ hvp (le_trans hlen hkle)
            have hstep : stepBRoundCost cp routeCost G X vs b k z subCore subCoreCost st ≤
                k * Tprev + R1 + (2 * X.card + 2) := by
              unfold stepBRoundCost
              dsimp only
              omega
            rw [Nat.succ_mul]
            exact Nat.add_le_add hprev hstep
      unfold stepBCost
      have hr49 : stepBRunRoundsCost cp route routeCost G X vs b k z subCore subCoreCost
          (49 * cp.L + 1) ≤ (49 * LParam M + 1) * (k * Tprev + R1 + (2 * X.card + 2)) :=
        hrounds (49 * LParam M + 1) (le_refl _)
      have hinj : (match stepBRunRounds cp route G X vs b k z subCore (49 * cp.L + 1) with
          | Sum.inl _ => 0
          | Sum.inr st =>
              let injPairs := (List.range k).map fun i => (blockSet vs b i \ st.savedS i, st.savedS i)
              routeCost G X injPairs cp.Δ cp.L 100 z + (X.card + 1)) ≤ R1 + (2 * X.card + 2) := by
        cases hst : stepBRunRounds cp route G X vs b k z subCore (49 * cp.L + 1) with
        | inl _ => exact Nat.zero_le _
        | inr st =>
          dsimp only
          have hsv := stepBRunRounds_state_valid hcfg hroute hX hGloop hdegG hXL hnd hvs
            hb_pos hb_even hb_le (hsubCore hq2) (le_refl _) hst
          have hvp := hsv.2.2 rfl
          have hlen : ((List.range k).map fun i => (blockSet vs b i \ st.savedS i, st.savedS i)).length ≤
              2 * NOf M r := by simpa using hkle
          have hr1 : routeCost G X ((List.range k).map fun i =>
              (blockSet vs b i \ st.savedS i, st.savedS i)) cp.Δ cp.L 100 z ≤ R1 :=
            hroute1 _ hvp hlen
          exact Nat.add_le_add hr1 (by omega)
      have hkT : (49 * LParam M + 1) * (k * Tprev) ≤ 100 * NOf M r * LParam M * Tprev := by
        have h1 : 49 * LParam M + 1 ≤ 50 * LParam M := by omega
        calc (49 * LParam M + 1) * (k * Tprev)
            ≤ (50 * LParam M) * ((2 * NOf M r) * Tprev) :=
              Nat.mul_le_mul h1 (Nat.mul_le_mul_right Tprev hkle)
          _ = 100 * NOf M r * LParam M * Tprev := by ring
      have hexp : (49 * LParam M + 1) * (k * Tprev + R1 + (2 * X.card + 2)) =
          (49 * LParam M + 1) * (k * Tprev) + (49 * LParam M + 1) * R1 +
            (49 * LParam M + 1) * (2 * X.card + 2) := by ring
      have hexp2 : (49 * LParam M + 2) * R1 = (49 * LParam M + 1) * R1 + R1 := by ring
      have hexp3 : (49 * LParam M + 2) * (2 * X.card + 2) =
          (49 * LParam M + 1) * (2 * X.card + 2) + (2 * X.card + 2) := by ring
      have htot := Nat.add_le_add hr49 hinj
      omega
  -- Step C macro cost bound.
  have hcostC : stepCMacroCost cp route routeCost cloud G X vs b k z ≤
      17 * R1 + 17 * (X.card + 1) + (200 * k + 1) := by
    unfold stepCMacroCost
    by_cases hk2 : 2 ≤ k
    · simp only [hk2, ↓reduceIte]
      have hcn : (cloud k).n = k := hcloud.n_eq k hk2
      have hcvalid : (cloud k).IsValid := hcloud.isValid k hk2
      have hcdeg : ∀ v < (cloud k).n, (cloud k).deg v ≤ 9 :=
        fun v hv => hcloud.deg_le k hk2 v (hcn ▸ hv)
      have hcol := edgeColor17_spec hcvalid hcdeg
      have hHvalid := removeLoops_isValid hcvalid
      have hloopC : ∀ m, stepCMacroLoopCost cp route routeCost G X vs b z (edgeColor17 (cloud k)) m ≤
          m * (R1 + (X.card + 1)) := by
        intro m
        induction m with
        | zero => simp [stepCMacroLoopCost]
        | succ m ih =>
          unfold stepCMacroLoopCost
          cases stepCMacroLoop cp route G X vs b z (edgeColor17 (cloud k)) m with
          | inl _ =>
            rw [Nat.add_zero]
            exact le_trans ih (Nat.mul_le_mul_right _ (Nat.le_succ m))
          | inr _ =>
            have hcol_c : stepCMacroColorCost cp routeCost G X vs b z
                (colorClass (edgeColor17 (cloud k)) m) ≤ R1 + (X.card + 1) := by
              unfold stepCMacroColorCost
              split_ifs
              · omega
              · have hEc_v : ∀ e ∈ colorClass (edgeColor17 (cloud k)) m, e.1 < k ∧ e.2 < k := by
                  intro e he
                  unfold colorClass at he
                  obtain ⟨ec, hec, rfl⟩ := List.mem_map.mp he
                  have hin : ec.1 ∈ (removeLoops (cloud k)).edges := by
                    rw [← hcol.1]
                    exact List.mem_map.mpr ⟨ec, (List.mem_filter.mp hec).1, rfl⟩
                  have hv := hHvalid ec.1 hin
                  rwa [removeLoops_n, hcn] at hv
                have hvp := hvs ▸ validTerminalPairs_of_matching_edges hnd hb_pos hEc_v
                  (hcol.2.2.1 m)
                have hlen : ((colorClass (edgeColor17 (cloud k)) m).map fun e =>
                    (blockSet vs b e.1, blockSet vs b e.2)).length ≤ 2 * NOf M r := by
                  rw [List.length_map]
                  exact le_trans (colorClass_length_le hEc_v (hcol.2.2.1 m)) hkle
                have hr1 : routeCost G X ((colorClass (edgeColor17 (cloud k)) m).map fun e =>
                    (blockSet vs b e.1, blockSet vs b e.2)) cp.Δ cp.L 100 z ≤ R1 :=
                  hroute1 _ hvp hlen
                exact Nat.add_le_add hr1 (le_refl _)
            rw [Nat.succ_mul]
            exact Nat.add_le_add ih hcol_c
      have h17 := hloopC 17
      have hexp : 17 * (R1 + (X.card + 1)) = 17 * R1 + 17 * (X.card + 1) := by ring
      omega
    · simp only [hk2, ↓reduceIte]; omega
  -- Step C leftover cost bound.
  have hcostZ : stepCLeftoverCost cp routeCost G X vs b z ≤ R1 + (X.card + 1) := by
    unfold stepCLeftoverCost
    split_ifs
    · have hpairs : ValidTerminalPairs X [(leftoverVerts vs b, fullVerts vs b)] := by
        have hle := card_leftoverVerts_le_card_sdiff hnd hb_pos hble
        rw [sdiff_leftoverVerts_eq_fullVerts hnd] at hle
        refine ⟨?_, ?_⟩
        · intro p hp
          rw [List.mem_singleton.mp hp]
          exact ⟨hvs ▸ leftoverVerts_subset_toFinset vs b, hvs ▸ fullVerts_subset_toFinset vs b, hle⟩
        · simp [(disjoint_fullVerts_leftoverVerts hnd b).symm]
      have hr1 : routeCost G X [(leftoverVerts vs b, fullVerts vs b)] cp.Δ cp.L 100 z ≤ R1 :=
        hroute1 _ hpairs (by simp; omega)
      omega
    · omega
  -- Step D trimming cost bound (whenever all three stages returned `Sum.inr`).
  have hcostD : ∀ callsB callsC callsZ,
      (if q = 1 then Sum.inr [] else stepB cp route G X vs b k z subCore) = Sum.inr callsB →
      stepCMacro cp route cloud G X vs b k z = Sum.inr callsC →
      stepCLeftover cp route G X vs b z = Sum.inr callsZ →
      removeFakeCost G X (callsFakeEdges (callsB ++ callsC ++ callsZ)) (PParam cfg M q) ≤
        2048 * C_trim * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) := by
    intro callsB callsC callsZ hB hC hZ
    set callsAll := callsB ++ callsC ++ callsZ
    have hFlen : (callsFakeEdges callsAll).length ≤ X.card :=
      oneShot_callsFakeEdges_length_le hcfg hq1 hqr hroute hcloud hsubCore hX hGloop hdegG
        hsize hB hC hZ
    have hsum_le : X.card + (G.inside X).length + (callsFakeEdges callsAll).length + 1 ≤
        2048 * LParam M * (NOf M r) ^ q := by
      have h2 := two_mul_inside_le hdegG
      unfold deltaParam tParam at h2
      have hsp1 : 1024 * LParam M * X.card = 2 * (512 * LParam M * X.card) := by ring
      have hsp2 : 2048 * LParam M * X.card = 4 * (512 * LParam M * X.card) := by ring
      have h1 : (G.inside X).length ≤ 512 * LParam M * X.card := by omega
      have h3 : X.card + (callsFakeEdges callsAll).length + 1 ≤ 512 * LParam M * X.card := by
        nlinarith
      have h4 : X.card + (G.inside X).length + (callsFakeEdges callsAll).length + 1 ≤
          2048 * LParam M * X.card := by omega
      exact le_trans h4 (Nat.mul_le_mul_left _ hXle)
    have htrim := hrfc G X (callsFakeEdges callsAll) (PParam cfg M q) hXL
    have hPsq : (PParam cfg M q) ^ 2 = (FParam cfg M) ^ (2 * q) := by
      unfold PParam; rw [← pow_mul, Nat.mul_comm]
    calc removeFakeCost G X (callsFakeEdges callsAll) (PParam cfg M q)
        ≤ C_trim * (X.card + (G.inside X).length + (callsFakeEdges callsAll).length + 1) *
            (LParam M) ^ 2 * (PParam cfg M q) ^ 2 := htrim
      _ ≤ C_trim * (2048 * LParam M * (NOf M r) ^ q) * (LParam M) ^ 2 * (FParam cfg M) ^ (2 * q) := by
          rw [hPsq]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsum_le))
      _ = 2048 * C_trim * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) := by ring
  -- Combine all four pieces of `oneShotCost + 2 * (X.card + 1)`.
  have hoverhead : (X.card + 1) + (X.card + 1) + (49 * LParam M + 2) * (2 * X.card + 2) +
      (17 * (X.card + 1) + (200 * k + 1)) + 2 * (X.card + 1) ≤
      1024 * ParamConfig.d0 * ParamConfig.R0 * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by
    have hX1 : X.card + 1 ≤ 2 * (NOf M r) ^ q := by omega
    have h51 : (49 * LParam M + 2) * (2 * X.card + 2) ≤ 200 * (NOf M r) ^ q * LParam M := by
      have h1 : 49 * LParam M + 2 ≤ 50 * LParam M := by omega
      have h2 : 2 * X.card + 2 ≤ 4 * (NOf M r) ^ q := by omega
      calc (49 * LParam M + 2) * (2 * X.card + 2)
          ≤ (50 * LParam M) * (4 * (NOf M r) ^ q) := Nat.mul_le_mul h1 h2
        _ = 200 * (NOf M r) ^ q * LParam M := by ring
    have h200k : 200 * k + 1 ≤ 401 * NOf M r := by omega
    have hNpow : 1 ≤ (NOf M r) ^ q := Nat.one_le_pow q _ (by omega)
    have hN1 : NOf M r ≤ (NOf M r) ^ (q + 1) := by
      calc NOf M r = (NOf M r) ^ 1 := (pow_one _).symm
        _ ≤ (NOf M r) ^ (q + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hNq1 : (NOf M r) ^ q ≤ (NOf M r) ^ (q + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ q)
    have hL1 : LParam M ≤ (LParam M) ^ 8 := by
      calc LParam M = (LParam M) ^ 1 := (pow_one _).symm
        _ ≤ (LParam M) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
    set M8 := (NOf M r) ^ (q + 1) * (LParam M) ^ 8
    have hsum1 : (X.card + 1) + (X.card + 1) + (49 * LParam M + 2) * (2 * X.card + 2) +
        (17 * (X.card + 1) + (200 * k + 1)) + 2 * (X.card + 1) ≤ 1000 * M8 := by
      have h1 : 21 * (X.card + 1) ≤ 42 * M8 := by
        have hLp : 1 ≤ (LParam M) ^ 8 := Nat.one_le_pow 8 _ (by omega)
        calc 21 * (X.card + 1) ≤ 21 * (2 * (NOf M r) ^ (q + 1)) := by omega
          _ = 42 * ((NOf M r) ^ (q + 1) * 1) := by ring
          _ ≤ 42 * M8 := Nat.mul_le_mul_left 42 (Nat.mul_le_mul_left _ hLp)
      have h2 : 200 * (NOf M r) ^ q * LParam M ≤ 200 * M8 := by
        calc 200 * (NOf M r) ^ q * LParam M
            = 200 * ((NOf M r) ^ q * LParam M) := by ring
          _ ≤ 200 * M8 := Nat.mul_le_mul_left 200 (Nat.mul_le_mul hNq1 hL1)
      have h3 : 401 * NOf M r ≤ 401 * M8 := by
        have hLp : 1 ≤ (LParam M) ^ 8 := Nat.one_le_pow 8 _ (by omega)
        calc 401 * NOf M r = 401 * (NOf M r * 1) := by ring
          _ ≤ 401 * M8 := Nat.mul_le_mul_left 401 (Nat.mul_le_mul hN1 hLp)
      omega
    have hcoeff : 1000 ≤ 1024 * ParamConfig.d0 * ParamConfig.R0 := by
      unfold ParamConfig.R0 ParamConfig.d0; decide
    calc _ ≤ 1000 * M8 := hsum1
      _ ≤ (1024 * ParamConfig.d0 * ParamConfig.R0) * M8 := Nat.mul_le_mul_right M8 hcoeff
      _ = 1024 * ParamConfig.d0 * ParamConfig.R0 * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by
        dsimp only [M8]; ring
  have hroute_tot : (49 * LParam M + 2) * R1 + 17 * R1 + R1 ≤
      207 * C_route * 1024 * ParamConfig.d0 * ParamConfig.R0 *
        (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by
    have h69 : 49 * LParam M + 20 ≤ 69 * LParam M := by omega
    calc (49 * LParam M + 2) * R1 + 17 * R1 + R1
        = (49 * LParam M + 20) * R1 := by ring
      _ ≤ (69 * LParam M) * R1 := Nat.mul_le_mul_right R1 h69
      _ = 207 * C_route * 1024 * ParamConfig.d0 * ParamConfig.R0 *
            (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by dsimp only [R1]; ring
  unfold oneShotCost
  dsimp only
  change (X.card + 1) + (if q = 1 then 1 else stepBCost cp route routeCost G X vs b k z subCore subCoreCost) +
      (match (if q = 1 then Sum.inr [] else stepB cp route G X vs b k z subCore) with
        | Sum.inl _ => 0
        | Sum.inr callsB =>
            stepCMacroCost cp route routeCost cloud G X vs b k z +
              match stepCMacro cp route cloud G X vs b k z with
              | Sum.inl _ => 0
              | Sum.inr callsC =>
                  stepCLeftoverCost cp routeCost G X vs b z +
                    match stepCLeftover cp route G X vs b z with
                    | Sum.inl _ => 0
                    | Sum.inr callsZ =>
                        removeFakeCost G X (callsFakeEdges (callsB ++ callsC ++ callsZ))
                          (PParam cfg M q)) + 2 * (X.card + 1) ≤ _
  have hsum_coeff : (207 * C_route + 1) * 1024 * ParamConfig.d0 * ParamConfig.R0 *
        (NOf M r) ^ (q + 1) * (LParam M) ^ 8 =
      207 * C_route * 1024 * ParamConfig.d0 * ParamConfig.R0 *
        (NOf M r) ^ (q + 1) * (LParam M) ^ 8 +
      1024 * ParamConfig.d0 * ParamConfig.R0 * (NOf M r) ^ (q + 1) * (LParam M) ^ 8 := by ring
  have hBCR : (X.card + 1) +
      (if q = 1 then 1 else stepBCost cp route routeCost G X vs b k z subCore subCoreCost) +
      stepCMacroCost cp route routeCost cloud G X vs b k z +
      stepCLeftoverCost cp routeCost G X vs b z + 2 * (X.card + 1) ≤
      (207 * C_route + 1) * 1024 * ParamConfig.d0 * ParamConfig.R0 *
          (NOf M r) ^ (q + 1) * (LParam M) ^ 8 +
        100 * NOf M r * LParam M * Tprev := by
    have h1 := Nat.add_le_add (Nat.add_le_add hcostB hcostC) hcostZ
    linarith [h1, hroute_tot, hoverhead, hsum_coeff]
  cases hB : (if q = 1 then Sum.inr [] else stepB cp route G X vs b k z subCore) with
  | inl _ => simp only [Nat.add_zero] at *; omega
  | inr callsB =>
    dsimp only
    cases hC : stepCMacro cp route cloud G X vs b k z with
    | inl _ => simp only [Nat.add_zero] at *; omega
    | inr callsC =>
      dsimp only
      cases hZ : stepCLeftover cp route G X vs b z with
      | inl _ => simp only [Nat.add_zero, Nat.add_assoc] at hBCR ⊢; omega
      | inr callsZ =>
        dsimp only
        have hD := hcostD callsB callsC callsZ hB hC hZ
        simp only [Nat.add_assoc] at hBCR ⊢
        omega

/-! ### Cost recurrence and closed-form bound -/

/-- **Cost recurrence**: for `1 ≤ q ≤ r`, `4 ≤ cfg.a`, `r ≤ ell M`, `C_route ≤ 39 * cfg.u`,
and `C_trim ≤ 2 ^ 20 * cfg.u ^ 3` (in particular whenever `C_route ≤ cfg.u` and `C_trim ≤ cfg.u`),
if `coreOnCost` at level `q - 1` is at most `Tprev` on all valid inputs of size `≤ N ^ (q - 1)`,
then `coreOnCost` at level `q` obeys the cost recurrence
`c₀ · A · (N^{q+1} L^9 F^q + N L^2 F^q T_{q-1} + N^q L^4 F^{3q})`. -/
theorem coreOnCost_rec {cfg : ParamConfig} {M r q C_route C_trim Tprev : ℕ}
    (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq1 : 1 ≤ q) (hqr : q ≤ r)
    (hCroute : C_route ≤ 39 * cfg.u) (hCtrim : C_trim ≤ 2 ^ 20 * cfg.u ^ 3)
    {route : RouterFn} {routeCost : RouterCostFn} (hroute : IsMatchingPlayer route routeCost)
    (hrc : RouteCostBounded routeCost C_route)
    {removeFakeCost : RemoveFakeCostFn}
    (hrfc : RemoveFakeCostBounded removeFakeCost (LParam M) C_trim)
    {cloud : ℕ → Graph} (hcloud : IsCloudExpander cloud (1 / (cfg.a₀ : ℝ)))
    (hprev : ∀ W Y, Y ⊆ Finset.range W.n → W.IsValid → (∀ e ∈ W.inside Y, e.1 ≠ e.2) →
      Y.card ≤ (NOf M r) ^ (q - 1) → (∀ v ∈ Y, W.degIn Y v ≤ deltaParam M) →
      coreOnCost (coreParamsOf cfg M r) route routeCost removeFakeCost cloud (q - 1) W Y ≤ Tprev)
    {G : Graph} {X : Finset ℕ}
    (hX : X ⊆ Finset.range G.n) (hGvalid : G.IsValid) (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hXle : X.card ≤ (NOf M r) ^ q) (hdegG : ∀ v ∈ X, G.degIn X v ≤ deltaParam M) :
    coreOnCost (coreParamsOf cfg M r) route routeCost removeFakeCost cloud q G X ≤
      cfg.c0 * cfg.A *
        ((NOf M r) ^ (q + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ q +
          NOf M r * (LParam M) ^ 2 * (FParam cfg M) ^ q * Tprev +
          (NOf M r) ^ q * (LParam M) ^ 4 * (FParam cfg M) ^ (3 * q)) := by
  have hcfg := coreParamsValid_of_paramConfig cfg M r ha hrl
  obtain ⟨q', rfl⟩ := Nat.exists_eq_add_of_le' hq1
  simp only [Nat.add_sub_cancel] at hprev ⊢
  set cp := coreParamsOf cfg M r
  set RHS := cfg.c0 * cfg.A *
    ((NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ (q' + 1) +
      NOf M r * (LParam M) ^ 2 * (FParam cfg M) ^ (q' + 1) * Tprev +
      (NOf M r) ^ (q' + 1) * (LParam M) ^ 4 * (FParam cfg M) ^ (3 * (q' + 1)))
  have hN1 : 1 ≤ NOf M r := le_trans (by decide) (four_le_NOf M r)
  have hL1 : 1 ≤ LParam M := le_trans (by decide) (four_le_LParam M)
  have hF1 : 1 ≤ FParam cfg M := one_le_FParam cfg M
  have hc0 : 1 ≤ cfg.c0 := cfg.c0_pos
  have hA1 : 1 ≤ cfg.A := le_trans (by decide) cfg.A_pos
  have hRHS1 : 1 ≤ RHS := by
    have h1 : 1 ≤ cfg.c0 * cfg.A := Nat.mul_le_mul hc0 hA1
    have h2 : 1 ≤ (NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ (q' + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow _ _ hN1) (Nat.one_le_pow _ _ hL1))
        (Nat.one_le_pow _ _ hF1)
    have h3 : 1 ≤ cfg.c0 * cfg.A * ((NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 9 *
        (FParam cfg M) ^ (q' + 1)) := Nat.mul_le_mul h1 h2
    dsimp only [RHS]
    rw [Nat.mul_add, Nat.mul_add]
    omega
  unfold coreOnCost
  by_cases h1 : X.card ≤ 1
  · simp only [h1, ↓reduceIte]; exact hRHS1
  · simp only [h1, ↓reduceIte]
    by_cases hdel : X.card ≤ cp.N ^ q'
    · simp only [hdel, ↓reduceIte]
      have hpr := hprev G X hX hGvalid hGloop hdel hdegG
      have hterm2 : Tprev ≤ cfg.c0 * cfg.A *
          (NOf M r * (LParam M) ^ 2 * (FParam cfg M) ^ (q' + 1) * Tprev) := by
        have hcoeff : 1 ≤ cfg.c0 * cfg.A * (NOf M r * (LParam M) ^ 2 * (FParam cfg M) ^ (q' + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul hc0 hA1)
            (Nat.mul_le_mul (Nat.mul_le_mul hN1 (Nat.one_le_pow _ _ hL1)) (Nat.one_le_pow _ _ hF1))
        calc Tprev = 1 * Tprev := (Nat.one_mul _).symm
          _ ≤ cfg.c0 * cfg.A * (NOf M r * (LParam M) ^ 2 * (FParam cfg M) ^ (q' + 1)) * Tprev :=
            Nat.mul_le_mul_right Tprev hcoeff
          _ = cfg.c0 * cfg.A * (NOf M r * (LParam M) ^ 2 * (FParam cfg M) ^ (q' + 1) * Tprev) := by
            ring
      have hterm1 : 1 ≤ cfg.c0 * cfg.A *
          ((NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ (q' + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul hc0 hA1)
          (Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow _ _ hN1) (Nat.one_le_pow _ _ hL1))
            (Nat.one_le_pow _ _ hF1))
      dsimp only [RHS]
      rw [Nat.mul_add, Nat.mul_add]
      omega
    · simp only [hdel, ↓reduceIte]
      have hXgt : (NOf M r) ^ q' < X.card := by dsimp only [cp, coreParamsOf] at hdel; omega
      -- Bound one iteration of `corePeelCost` by `S_one`.
      set S_one :=
        (207 * C_route + 1) * 1024 * ParamConfig.d0 * ParamConfig.R0 *
            (NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 8 +
          100 * NOf M r * LParam M * Tprev +
          2048 * C_trim * (NOf M r) ^ (q' + 1) * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * (q' + 1))
      have hS_pos : 1 ≤ S_one := by
        have h1' : 1 ≤ (207 * C_route + 1) * 1024 * ParamConfig.d0 * ParamConfig.R0 := by
          unfold ParamConfig.R0 ParamConfig.d0; omega
        have h2' : 1 ≤ (NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 8 :=
          Nat.mul_le_mul (Nat.one_le_pow _ _ hN1) (Nat.one_le_pow _ _ hL1)
        have h3' : 1 ≤ (207 * C_route + 1) * 1024 * ParamConfig.d0 * ParamConfig.R0 *
            (NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 8 := by
          rw [mul_assoc _ ((NOf M r) ^ (q' + 1 + 1))]
          exact Nat.mul_le_mul h1' h2'
        dsimp only [S_one]; omega
      have hpeel : ∀ fuel U, U ⊆ X →
          corePeelCost cp route routeCost removeFakeCost cloud (q' + 1)
            (coreOn cp route cloud q')
            (coreOnCost cp route routeCost removeFakeCost cloud q') G X fuel U ≤
          fuel * S_one + 1 := by
        intro fuel
        induction fuel with
        | zero => intro U _; simp [corePeelCost]
        | succ fuel ih =>
          intro U hUX
          unfold corePeelCost
          by_cases hdone : X.card ≤ 4 * U.card
          · simp only [hdone, ↓reduceIte]; omega
          · simp only [hdone, ↓reduceIte]
            set X' := X \ U
            have hX'sub : X' ⊆ X := Finset.sdiff_subset
            have hX'card : X'.card + U.card = X.card := Finset.card_sdiff_add_card_eq_card hUX
            have h3X : 3 * X.card < 4 * X'.card := by omega
            have hX'range : X' ⊆ Finset.range G.n := hX'sub.trans hX
            have hX'loop : ∀ e ∈ G.inside X', e.1 ≠ e.2 := fun e he => by
              rw [mem_inside_iff] at he
              exact hGloop e (mem_inside_iff.mpr ⟨he.1, hX'sub he.2.1, hX'sub he.2.2⟩)
            have hX'deg : ∀ v ∈ X', G.degIn X' v ≤ deltaParam M :=
              fun v hv => le_trans (degIn_mono hX'sub v) (hdegG v (hX'sub hv))
            have hX'size : (q' + 1 = 1 → 2 ≤ X'.card ∧ X'.card ≤ NOf M r) ∧
                (2 ≤ q' + 1 → (NOf M r) ^ (q' + 1 - 1) / 2 ≤ X'.card ∧ X'.card ≤ (NOf M r) ^ (q' + 1)) := by
              refine ⟨fun hq => ?_, fun _ => ?_⟩
              · have hq0 : q' = 0 := by omega
                subst hq0
                simp only [pow_zero, zero_add, pow_one] at hXgt hXle
                exact ⟨by omega, by omega⟩
              · simp only [Nat.add_sub_cancel]
                have hdiv : 2 * ((NOf M r) ^ q' / 2) ≤ (NOf M r) ^ q' := Nat.mul_div_le _ 2
                exact ⟨by omega, by omega⟩
            have hos_c : oneShotCost cp route routeCost removeFakeCost cloud (q' + 1)
                (coreOn cp route cloud q') (coreOnCost cp route routeCost removeFakeCost cloud q')
                G X' + 2 * (X'.card + 1) ≤ S_one :=
              oneShotCost_le ha hrl (by omega : 1 ≤ q' + 1) hqr hroute hrc hrfc
                hcloud (fun _ => coreOn_spec hcfg hroute hcloud q' (Nat.le_of_succ_le hqr))
                (fun _ => hprev) hX'range hX'loop hX'deg hX'size
            have hcard_le : X.card + 1 ≤ 2 * (X'.card + 1) := by omega
            have hstep : oneShotCost cp route routeCost removeFakeCost cloud (q' + 1)
                (coreOn cp route cloud q') (coreOnCost cp route routeCost removeFakeCost cloud q')
                G X' + (X.card + 1) ≤ S_one := by omega
            cases hres : oneShot cp route cloud (q' + 1) (coreOn cp route cloud q') G X' with
            | expander _ =>
              dsimp only
              have hmul : S_one ≤ (fuel + 1) * S_one := by
                calc S_one = 1 * S_one := (Nat.one_mul _).symm
                  _ ≤ (fuel + 1) * S_one := Nat.mul_le_mul_right S_one (by omega)
              omega
            | cut V =>
              dsimp only
              have hos := oneShot_spec hcfg (by omega : 1 ≤ q' + 1) hqr hroute hcloud
                (fun _ => coreOn_spec hcfg hroute hcloud q' (Nat.le_of_succ_le hqr))
                hX'range hGvalid hX'loop hX'deg hX'size
              rw [hres] at hos
              have hYX' : smallerSide X' V ⊆ X' := by
                unfold smallerSide; split_ifs; exact hos.1; exact Finset.sdiff_subset
              have hU'X : U ∪ smallerSide X' V ⊆ X := Finset.union_subset hUX (hYX'.trans hX'sub)
              have hrec := ih (U ∪ smallerSide X' V) hU'X
              have hmul : (fuel + 1) * S_one = S_one + fuel * S_one := by ring
              omega
      have hpeel0 := hpeel (2 * cp.D (q' + 1)) ∅ (Finset.empty_subset X)
      -- Convert `2 * D_q * S_one + 1 ≤ RHS`.
      have hDq : 2 * cp.D (q' + 1) =
          2048 * cfg.A * LParam M * (FParam cfg M) ^ (q' + 1) := by
        dsimp only [cp, coreParamsOf]
        unfold DCore deltaParam tParam PParam
        ring
      rw [hDq] at hpeel0 ⊢
      have hmul_S : 2048 * cfg.A * LParam M * (FParam cfg M) ^ (q' + 1) * S_one =
          2048 * (207 * C_route + 1) * 1024 * ParamConfig.d0 * ParamConfig.R0 * cfg.A *
              (NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ (q' + 1) +
            204800 * cfg.A * NOf M r * (LParam M) ^ 2 * (FParam cfg M) ^ (q' + 1) * Tprev +
            2 ^ 22 * C_trim * cfg.A * (NOf M r) ^ (q' + 1) * (LParam M) ^ 4 *
              (FParam cfg M) ^ (3 * (q' + 1)) := by
        dsimp only [S_one]
        have hF3 : (FParam cfg M) ^ (q' + 1) * (FParam cfg M) ^ (2 * (q' + 1)) =
            (FParam cfg M) ^ (3 * (q' + 1)) := by
          rw [← pow_add]; congr 1; omega
        calc 2048 * cfg.A * LParam M * (FParam cfg M) ^ (q' + 1) *
              ((207 * C_route + 1) * 1024 * ParamConfig.d0 * ParamConfig.R0 *
                  (NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 8 +
                100 * NOf M r * LParam M * Tprev +
                2048 * C_trim * (NOf M r) ^ (q' + 1) * (LParam M) ^ 3 *
                  (FParam cfg M) ^ (2 * (q' + 1)))
            = 2048 * (207 * C_route + 1) * 1024 * ParamConfig.d0 * ParamConfig.R0 * cfg.A *
                  (NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ (q' + 1) +
                204800 * cfg.A * NOf M r * (LParam M) ^ 2 * (FParam cfg M) ^ (q' + 1) * Tprev +
                2 ^ 22 * C_trim * cfg.A * (NOf M r) ^ (q' + 1) * (LParam M) ^ 4 *
                  ((FParam cfg M) ^ (q' + 1) * (FParam cfg M) ^ (2 * (q' + 1))) := by ring
          _ = _ := by rw [hF3]
      rw [hmul_S] at hpeel0
      have hcoeff1 : 2048 * (207 * C_route + 2) * 1024 * ParamConfig.d0 * ParamConfig.R0 ≤ cfg.c0 := by
        have hu : 1 ≤ cfg.u := cfg.hu
        have h207 : 207 * C_route + 2 ≤ 8192 * cfg.u := by omega
        calc 2048 * (207 * C_route + 2) * 1024 * ParamConfig.d0 * ParamConfig.R0
            ≤ 2048 * (8192 * cfg.u) * 1024 * ParamConfig.d0 * ParamConfig.R0 := by
              exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
                (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2048 h207)))
          _ = 4096 * (4 * cfg.u * 1024 ^ 2 * ParamConfig.d0 * ParamConfig.R0) := by ring
          _ ≤ 4096 * cfg.s0 := Nat.mul_le_mul_left 4096 (by unfold ParamConfig.s0; omega)
          _ = cfg.c0 := rfl
      have hcoeff2 : 204800 ≤ cfg.c0 := by
        unfold ParamConfig.c0 ParamConfig.s0; omega
      have hcoeff3 : 2 ^ 22 * C_trim ≤ cfg.c0 := by
        calc 2 ^ 22 * C_trim
            ≤ 2 ^ 22 * (2 ^ 20 * cfg.u ^ 3) := Nat.mul_le_mul_left _ hCtrim
          _ = 4096 * (2 ^ 30 * cfg.u ^ 3) := by ring
          _ ≤ 4096 * cfg.s0 := Nat.mul_le_mul_left 4096 (by unfold ParamConfig.s0; omega)
          _ = cfg.c0 := rfl
      have hone_le : 1 ≤ 2048 * 1024 * ParamConfig.d0 * ParamConfig.R0 * cfg.A *
          (NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ (q' + 1) := by
        have h1' : 1 ≤ 2048 * 1024 * ParamConfig.d0 * ParamConfig.R0 * cfg.A := by
          unfold ParamConfig.R0 ParamConfig.d0; omega
        have h2' : 1 ≤ (NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ (q' + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow _ _ hN1) (Nat.one_le_pow _ _ hL1))
            (Nat.one_le_pow _ _ hF1)
        have h3' : 1 ≤ (2048 * 1024 * ParamConfig.d0 * ParamConfig.R0 * cfg.A) *
            ((NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ (q' + 1)) :=
          Nat.mul_le_mul h1' h2'
        have h4' : (2048 * 1024 * ParamConfig.d0 * ParamConfig.R0 * cfg.A) *
              ((NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ (q' + 1)) =
            2048 * 1024 * ParamConfig.d0 * ParamConfig.R0 * cfg.A *
              (NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ (q' + 1) := by ring
        omega
      have ht1 : 2048 * (207 * C_route + 1) * 1024 * ParamConfig.d0 * ParamConfig.R0 * cfg.A *
              (NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ (q' + 1) + 1 ≤
          cfg.c0 * cfg.A *
              ((NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ (q' + 1)) := by
        have hadd : 2048 * (207 * C_route + 1) * 1024 * ParamConfig.d0 * ParamConfig.R0 * cfg.A *
                (NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ (q' + 1) +
              2048 * 1024 * ParamConfig.d0 * ParamConfig.R0 * cfg.A *
                (NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ (q' + 1) =
            (2048 * (207 * C_route + 2) * 1024 * ParamConfig.d0 * ParamConfig.R0) *
              (cfg.A * ((NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 9 *
                (FParam cfg M) ^ (q' + 1))) := by ring
        calc _ ≤ (2048 * (207 * C_route + 2) * 1024 * ParamConfig.d0 * ParamConfig.R0) *
                  (cfg.A * ((NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 9 *
                    (FParam cfg M) ^ (q' + 1))) := by omega
          _ ≤ cfg.c0 * (cfg.A * ((NOf M r) ^ (q' + 1 + 1) * (LParam M) ^ 9 *
                (FParam cfg M) ^ (q' + 1))) := Nat.mul_le_mul_right _ hcoeff1
          _ = _ := by ring
      have ht2 : 204800 * cfg.A * NOf M r * (LParam M) ^ 2 * (FParam cfg M) ^ (q' + 1) * Tprev ≤
          cfg.c0 * cfg.A * (NOf M r * (LParam M) ^ 2 * (FParam cfg M) ^ (q' + 1) * Tprev) := by
        calc 204800 * cfg.A * NOf M r * (LParam M) ^ 2 * (FParam cfg M) ^ (q' + 1) * Tprev
            = 204800 * (cfg.A * (NOf M r * (LParam M) ^ 2 * (FParam cfg M) ^ (q' + 1) * Tprev)) := by
              ring
          _ ≤ cfg.c0 * (cfg.A * (NOf M r * (LParam M) ^ 2 * (FParam cfg M) ^ (q' + 1) * Tprev)) :=
              Nat.mul_le_mul_right _ hcoeff2
          _ = _ := by ring
      have ht3 : 2 ^ 22 * C_trim * cfg.A * (NOf M r) ^ (q' + 1) * (LParam M) ^ 4 *
              (FParam cfg M) ^ (3 * (q' + 1)) ≤
          cfg.c0 * cfg.A * ((NOf M r) ^ (q' + 1) * (LParam M) ^ 4 *
              (FParam cfg M) ^ (3 * (q' + 1))) := by
        calc 2 ^ 22 * C_trim * cfg.A * (NOf M r) ^ (q' + 1) * (LParam M) ^ 4 *
                (FParam cfg M) ^ (3 * (q' + 1))
            = (2 ^ 22 * C_trim) * (cfg.A * ((NOf M r) ^ (q' + 1) * (LParam M) ^ 4 *
                (FParam cfg M) ^ (3 * (q' + 1)))) := by ring
          _ ≤ cfg.c0 * (cfg.A * ((NOf M r) ^ (q' + 1) * (LParam M) ^ 4 *
                (FParam cfg M) ^ (3 * (q' + 1)))) := Nat.mul_le_mul_right _ hcoeff3
          _ = _ := by ring
      dsimp only [RHS]
      rw [Nat.mul_add, Nat.mul_add]
      omega

/-- **Closed-form cost bound** (induced-set form): for every `q ≤ r`, the operation count of
`coreOn` on any valid loopless induced subproblem of size `≤ N^q` and maximum degree `≤ Δ` is at
most `coreTimeBound cfg M r q = N^{q+1} W^{10 q^2 + 10}`. -/
theorem coreOnCost_le_coreTimeBound {cfg : ParamConfig} {M r C_route C_trim : ℕ}
    (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M)
    (hCroute : C_route ≤ 39 * cfg.u) (hCtrim : C_trim ≤ 2 ^ 20 * cfg.u ^ 3)
    {route : RouterFn} {routeCost : RouterCostFn} (hroute : IsMatchingPlayer route routeCost)
    (hrc : RouteCostBounded routeCost C_route)
    {removeFakeCost : RemoveFakeCostFn}
    (hrfc : RemoveFakeCostBounded removeFakeCost (LParam M) C_trim)
    {cloud : ℕ → Graph} (hcloud : IsCloudExpander cloud (1 / (cfg.a₀ : ℝ))) :
    ∀ q, q ≤ r → ∀ (G : Graph) (X : Finset ℕ),
      X ⊆ Finset.range G.n → G.IsValid → (∀ e ∈ G.inside X, e.1 ≠ e.2) →
      X.card ≤ (NOf M r) ^ q → (∀ v ∈ X, G.degIn X v ≤ deltaParam M) →
      coreOnCost (coreParamsOf cfg M r) route routeCost removeFakeCost cloud q G X ≤
        coreTimeBound cfg M r q := by
  intro q
  induction q with
  | zero =>
    intro _ G X _ _ _ _ _
    simp only [coreOnCost, coreTimeBound]
    have hN1 : 1 ≤ NOf M r := le_trans (by decide) (four_le_NOf M r)
    have hW1 : 1 ≤ WParam cfg M := by unfold WParam; omega
    exact Nat.mul_le_mul (Nat.one_le_pow _ _ hN1) (Nat.one_le_pow _ _ hW1)
  | succ q ih =>
    intro hqr G X hX hGvalid hGloop hXle hdegG
    have hprev := ih (Nat.le_of_succ_le hqr)
    have hrec := coreOnCost_rec ha hrl (by omega : 1 ≤ q + 1) hqr hCroute hCtrim
      hroute hrc hrfc hcloud (by simpa using hprev) hX hGvalid hGloop hXle hdegG
    exact le_trans hrec (coreTimeBound_rec cfg M r (by omega : 1 ≤ q + 1) (by simp))

/-- **Closed-form cost bound** (full-graph form): for every `q ≤ r`, the operation count of
`core` on any valid loopless graph `G` with `G.n ≤ N^q` and maximum degree `≤ Δ` is at most
`coreTimeBound cfg M r q = N^{q+1} W^{10 q^2 + 10}`. -/
theorem coreCost_le_coreTimeBound {cfg : ParamConfig} {M r q C_route C_trim : ℕ}
    (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hqr : q ≤ r)
    (hCroute : C_route ≤ 39 * cfg.u) (hCtrim : C_trim ≤ 2 ^ 20 * cfg.u ^ 3)
    {route : RouterFn} {routeCost : RouterCostFn} (hroute : IsMatchingPlayer route routeCost)
    (hrc : RouteCostBounded routeCost C_route)
    {removeFakeCost : RemoveFakeCostFn}
    (hrfc : RemoveFakeCostBounded removeFakeCost (LParam M) C_trim)
    {cloud : ℕ → Graph} (hcloud : IsCloudExpander cloud (1 / (cfg.a₀ : ℝ)))
    {G : Graph} (hGvalid : G.IsValid) (hGloop : G.IsLoopless)
    (hGn : G.n ≤ (NOf M r) ^ q) (hdegG : ∀ v < G.n, G.deg v ≤ deltaParam M) :
    coreCost (coreParamsOf cfg M r) route routeCost removeFakeCost cloud q G ≤
      coreTimeBound cfg M r q := by
  unfold coreCost
  refine coreOnCost_le_coreTimeBound ha hrl hCroute hCtrim hroute hrc hrfc hcloud q hqr
    G G.verts (Finset.Subset.refl _) hGvalid ?_ ?_ ?_
  · intro e he
    rw [mem_inside_iff] at he
    exact hGloop e he.1
  · simpa [Graph.verts] using hGn
  · intro v hv
    exact hdegG v (Finset.mem_range.mp hv)

end MinCostFlow.ExpanderDecomp
