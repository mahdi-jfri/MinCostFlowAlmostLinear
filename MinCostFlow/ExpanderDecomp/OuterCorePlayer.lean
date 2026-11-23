module

public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.ExpanderDecomp.Params
public import Mathlib.Data.Nat.Log
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Core cut-player interface for the outer expander decomposition

This file defines the interface `IsCorePlayer` between the recursive core cut player `Core` and
the outer decomposition algorithm.

Main definitions and results:
* `CoreResult`: the two outcomes of `Core(q, G)`, either a balanced sparse cut `U` or a
  large induced expander `S`.
* `CoreOutcomeSpec`: exact formalization of these two outcomes for `Core(q, G)`.
* `IsCorePlayer`: states the core theorem for all `q ≤ r` and the size-sensitive cost bound when
  `q` is the least level with `G.n ≤ N^q`.
* `coreLevel`: the least level `q = ⌈log_N p⌉` with `p ≤ N^q`, together with its bounds.
* `IsCorePlayer.of_coreTimeBound`: constructs `IsCorePlayer` from the closed-form bound
  (`coreTimeBound`) via `coreTimeBound_size_sensitive`.
* `IsCorePlayer.spec_coreLevel`, `IsCorePlayer.cost_coreLevel`, and `IsCorePlayer.weakened_expansion`:
  convenience wrappers for the outer algorithm's calls to `Core`.
* `exists_isCorePlayer_zero`: shows `IsCorePlayer` is non-vacuous.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-- Output of the recursive core cut player: either a balanced sparse cut `(U, Ū)`
or an induced vertex set `S` of size at least `n / 2` with expansion at least `1 / P_q`
(see `CoreOutcomeSpec`). -/
inductive CoreResult where
  /-- Balanced sparse cut `(U, G.verts \ U)`. -/
  | cut (U : Finset ℕ)
  /-- Induced expander `S ⊆ G.verts`. -/
  | expander (S : Finset ℕ)

/-- The specification of `Core(q, G)` given by the core theorem:
* on `.cut U`: `U ⊆ G.verts`, `|U| ≥ n / 4`, `|G.verts \ U| ≥ n / 4`, and `|∂_G U| ≤ n / 100`;
* on `.expander S`: `S ⊆ G.verts`, `|S| ≥ n / 2`, and `Ψ(G[S]) ≥ 1 / P_q`. -/
def CoreOutcomeSpec (cfg : ParamConfig) (M q : ℕ) (G : Graph) (res : CoreResult) : Prop :=
  match res with
  | .cut U =>
      U ⊆ G.verts ∧
        G.n ≤ 4 * U.card ∧
        G.n ≤ 4 * (G.verts \ U).card ∧
        100 * G.cut U ≤ G.n
  | .expander S =>
      S ⊆ G.verts ∧
        G.n ≤ 2 * S.card ∧
        G.IsExpansionExpanderOn S (1 / (PParam cfg M q : ℝ))

/-- The least core recursion level `q` such that `p ≤ N^q`, where `N = NOf M r`. -/
def coreLevel (M r p : ℕ) : ℕ :=
  Nat.clog (NOf M r) p

/-- Interface for the recursive core cut player (core theorem and size-sensitive cost bound):
* `spec`: for every `q ≤ r` and every valid loopless graph `G` with `G.n ≤ N^q` and maximum
  degree at most `Δ`, `core q G` returns either a balanced sparse cut or an induced half-size
  expander with expansion at least `1 / P_q`;
* `cost_le`: whenever `1 ≤ q ≤ r` is the least level with `G.n ≤ N^q` (so `N^{q-1} < G.n`),
  `coreCost q G ≤ G.n · N^2 · W^{10 r^2 + 10}`. -/
structure IsCorePlayer (cfg : ParamConfig) (M r : ℕ)
    (core : ℕ → Graph → CoreResult) (coreCost : ℕ → Graph → ℕ) : Prop where
  /-- **Core theorem**: a balanced sparse cut or a half-size induced expander. -/
  spec : ∀ q (G : Graph), q ≤ r → G.IsValid → G.IsLoopless →
    G.n ≤ (NOf M r) ^ q → (∀ v < G.n, G.deg v ≤ deltaParam M) →
    CoreOutcomeSpec cfg M q G (core q G)
  /-- Size-sensitive cost bound at the least valid level `q`. -/
  cost_le : ∀ q (G : Graph), 1 ≤ q → q ≤ r → G.IsValid → G.IsLoopless →
    (NOf M r) ^ (q - 1) < G.n → G.n ≤ (NOf M r) ^ q →
    (∀ v < G.n, G.deg v ≤ deltaParam M) →
    coreCost q G ≤ G.n * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Properties of `coreLevel` -/

/-- `p ≤ N ^ (coreLevel M r p)` for all `p`. -/
theorem le_pow_coreLevel (M r p : ℕ) :
    p ≤ (NOf M r) ^ coreLevel M r p := by
  unfold coreLevel
  exact Nat.le_pow_clog (lt_of_lt_of_le (by decide) (four_le_NOf M r)) p

/-- For `p ≥ 2`, `coreLevel M r p ≥ 1`. -/
theorem one_le_coreLevel {M r p : ℕ} (hp : 2 ≤ p) :
    1 ≤ coreLevel M r p := by
  unfold coreLevel
  exact Nat.clog_pos (lt_of_lt_of_le (by decide) (four_le_NOf M r)) (by omega)

/-- If `p ≤ N^r`, then `coreLevel M r p ≤ r`. -/
theorem coreLevel_le {M r p : ℕ} (hp : p ≤ (NOf M r) ^ r) :
    coreLevel M r p ≤ r := by
  unfold coreLevel
  exact Nat.clog_le_of_le_pow hp

/-- For `p ≥ 2`, `coreLevel M r p` is minimal: `N ^ (coreLevel M r p - 1) < p`. -/
theorem pow_pred_coreLevel_lt {M r p : ℕ} (hp : 2 ≤ p) :
    (NOf M r) ^ (coreLevel M r p - 1) < p := by
  unfold coreLevel
  have hN : 1 < NOf M r := lt_of_lt_of_le (by decide) (four_le_NOf M r)
  by_contra hge
  push Not at hge
  have hle : Nat.clog (NOf M r) p ≤ Nat.clog (NOf M r) p - 1 :=
    Nat.clog_le_of_le_pow hge
  have hpos : 1 ≤ Nat.clog (NOf M r) p := Nat.clog_pos hN (by omega)
  omega

/-! ### Constructors and wrappers for `IsCorePlayer` -/

/-- Construct `IsCorePlayer` from the core theorem and the closed-form core time bound
(`coreTimeBound`), deriving the size-sensitive bound via `coreTimeBound_size_sensitive`. -/
theorem IsCorePlayer.of_coreTimeBound {cfg : ParamConfig} {M r : ℕ}
    {core : ℕ → Graph → CoreResult} {coreCost : ℕ → Graph → ℕ}
    (hspec : ∀ q (G : Graph), q ≤ r → G.IsValid → G.IsLoopless →
      G.n ≤ (NOf M r) ^ q → (∀ v < G.n, G.deg v ≤ deltaParam M) →
      CoreOutcomeSpec cfg M q G (core q G))
    (hcost : ∀ q (G : Graph), q ≤ r → G.IsValid → G.IsLoopless →
      G.n ≤ (NOf M r) ^ q → (∀ v < G.n, G.deg v ≤ deltaParam M) →
      coreCost q G ≤ coreTimeBound cfg M r q) :
    IsCorePlayer cfg M r core coreCost where
  spec := hspec
  cost_le q G hq1 hqr hv hl hlt hle hdeg :=
    le_trans (hcost q G hqr hv hl hle hdeg)
      (coreTimeBound_size_sensitive cfg M r hq1 hqr hlt)

/-- Weakening an expansion certificate from level `q ≤ r` to the uniform outer level `r`:
`1 / P_r ≤ 1 / P_q`. -/
theorem inv_PParam_le_of_le (cfg : ParamConfig) (M : ℕ) {q r : ℕ} (hqr : q ≤ r) :
    (1 : ℝ) / (PParam cfg M r : ℝ) ≤ 1 / (PParam cfg M q : ℝ) := by
  have hPq_pos : (0 : ℝ) < (PParam cfg M q : ℝ) := by
    exact_mod_cast (one_le_PParam cfg M q)
  have hle : PParam cfg M q ≤ PParam cfg M r :=
    Nat.pow_le_pow_right (one_le_FParam cfg M) hqr
  exact one_div_le_one_div_of_le hPq_pos (by exact_mod_cast hle)

/-- Weakening an expansion expander from expansion `β₂` to `β₁ ≤ β₂`. -/
theorem isExpansionExpanderOn_mono {G : Graph} {X : Finset ℕ} {β₁ β₂ : ℝ}
    (hβ : β₁ ≤ β₂) (h : G.IsExpansionExpanderOn X β₂) :
    G.IsExpansionExpanderOn X β₁ := by
  intro S hSX hSne hSXne
  have h2 := h S hSX hSne hSXne
  have hmin : 0 ≤ min (S.card : ℝ) ((X \ S).card : ℝ) :=
    le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  exact le_trans (mul_le_mul_of_nonneg_right hβ hmin) h2

/-- Calling `core` at `q = coreLevel M r G.n` yields a balanced sparse cut or an induced
half-size expander conservatively weakened to expansion `1 / P_r`. -/
theorem IsCorePlayer.spec_coreLevel {cfg : ParamConfig} {M r : ℕ}
    {core : ℕ → Graph → CoreResult} {coreCost : ℕ → Graph → ℕ}
    (hcore : IsCorePlayer cfg M r core coreCost) {G : Graph}
    (hv : G.IsValid) (hl : G.IsLoopless) (hn : G.n ≤ (NOf M r) ^ r)
    (hdeg : ∀ v < G.n, G.deg v ≤ deltaParam M) :
    CoreOutcomeSpec cfg M r G (core (coreLevel M r G.n) G) := by
  have hqr : coreLevel M r G.n ≤ r := coreLevel_le hn
  have hspec := hcore.spec (coreLevel M r G.n) G hqr hv hl (le_pow_coreLevel M r G.n) hdeg
  cases hres : core (coreLevel M r G.n) G with
  | cut U =>
    rw [hres] at hspec
    exact hspec
  | expander S =>
    rw [hres] at hspec
    exact ⟨hspec.1, hspec.2.1,
      isExpansionExpanderOn_mono (inv_PParam_le_of_le cfg M hqr) hspec.2.2⟩

/-- Calling `core` at `q = coreLevel M r G.n` for `2 ≤ G.n ≤ N^r` obeys the size-sensitive cost
bound. -/
theorem IsCorePlayer.cost_coreLevel {cfg : ParamConfig} {M r : ℕ}
    {core : ℕ → Graph → CoreResult} {coreCost : ℕ → Graph → ℕ}
    (hcore : IsCorePlayer cfg M r core coreCost) {G : Graph}
    (hv : G.IsValid) (hl : G.IsLoopless) (hn2 : 2 ≤ G.n) (hn : G.n ≤ (NOf M r) ^ r)
    (hdeg : ∀ v < G.n, G.deg v ≤ deltaParam M) :
    coreCost (coreLevel M r G.n) G ≤
      G.n * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) :=
  hcore.cost_le (coreLevel M r G.n) G (one_le_coreLevel hn2) (coreLevel_le hn) hv hl
    (pow_pred_coreLevel_lt hn2) (le_pow_coreLevel M r G.n) hdeg

/-! ### Non-vacuity witness -/

/-- `IsCorePlayer` is non-vacuous: at `r = 0`, every admissible graph has `G.n ≤ 1`, so returning
`G.verts` at zero cost satisfies `IsCorePlayer`. -/
theorem exists_isCorePlayer_zero (cfg : ParamConfig) (M : ℕ) :
    ∃ core coreCost, IsCorePlayer cfg M 0 core coreCost := by
  refine ⟨fun _ G => .expander G.verts, fun _ _ => 0, ?_, ?_⟩
  · intro q G hq _ _ hn _
    have hq0 : q = 0 := by omega
    subst hq0
    simp only [Nat.pow_zero] at hn
    refine ⟨Finset.Subset.refl _, ?_, ?_⟩
    · simp only [Graph.verts, Finset.card_range]
      omega
    · intro S hS hSne hSneV
      exfalso
      have hcard : S.card ≤ G.verts.card := Finset.card_le_card hS
      have hVcard : G.verts.card = G.n := Finset.card_range G.n
      have hSpos : 1 ≤ S.card := Finset.card_pos.mpr hSne
      exact hSneV (Finset.eq_of_subset_of_card_le hS (by omega))
  · intro q _ hq1 hqr
    omega

end MinCostFlow.ExpanderDecomp
