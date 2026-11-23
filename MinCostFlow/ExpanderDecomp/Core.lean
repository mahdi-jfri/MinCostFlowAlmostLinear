module

public import MinCostFlow.ExpanderDecomp.OneShot
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The recursive core cut player `Core`

This file defines the recursive core cut player `coreOn` (on an induced vertex subset `X` of a
read-only graph `G`) and `core` (on `G.verts`), using a peeling loop over
`oneShot`.

Main results:
* `cutIn_union_le`: for disjoint `U ⊆ X` and `Y ⊆ X \ U`,
  `G.cutIn X (U ∪ Y) ≤ G.cutIn X U + G.cutIn (X \ U) Y`.
* `corePeel_spec`: the peeling loop terminates within `2 * D_q` calls to `oneShot` and returns
  either a balanced sparse cut `(U, X \ U)` or a half-size induced `1 / P_q`-expander.
* `coreOn_spec`: the core theorem on any vertex subset `X ⊆ Finset.range G.n`, proved by induction
  on `q`.
* `core_spec`: the core theorem specialized to `X = G.verts`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-- Peeling loop: repeatedly runs `oneShot` on `X \ U`, peeling off the smaller
side of each returned sparse cut until either an expander is found, `|U| ≥ |X| / 4`, or `fuel`
reaches `0`. -/
noncomputable def corePeel (cfg : CoreParams) (route : RouterFn) (cloud : ℕ → Graph)
    (q : ℕ) (subCore : Graph → Finset ℕ → CoreResult) (G : Graph) (X : Finset ℕ) :
    ℕ → Finset ℕ → CoreResult
  | 0, U => .cut U
  | fuel + 1, U =>
      if X.card ≤ 4 * U.card then
        .cut U
      else
        match oneShot cfg route cloud q subCore G (X \ U) with
        | .expander R => .expander R
        | .cut V =>
            let Y := smallerSide (X \ U) V
            corePeel cfg route cloud q subCore G X fuel (U ∪ Y)

/-- The recursive core `Core(q, G[X])` on an induced subset `X ⊆ Finset.range G.n`,
treating `G` as read-only. -/
noncomputable def coreOn (cfg : CoreParams) (route : RouterFn) (cloud : ℕ → Graph) :
    ℕ → Graph → Finset ℕ → CoreResult
  | 0, _, X => .expander X
  | q + 1, G, X =>
      if X.card ≤ 1 then
        .expander X
      else if X.card ≤ cfg.N ^ q then
        coreOn cfg route cloud q G X
      else
        corePeel cfg route cloud (q + 1) (coreOn cfg route cloud q) G X (2 * cfg.D (q + 1)) ∅

/-- The recursive core `Core(q, G)` on the full vertex set `G.verts`. -/
noncomputable def core (cfg : CoreParams) (route : RouterFn) (cloud : ℕ → Graph)
    (q : ℕ) (G : Graph) : CoreResult :=
  coreOn cfg route cloud q G G.verts

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Peeling cut-additivity lemma -/

/-- Every edge of `G[X]` crossing `U ∪ Y` (for `U ⊆ X` and `Y ⊆ X \ U`) either already crosses
`U` in `G[X]`, or lies wholly inside `X \ U` and crosses `Y`. -/
theorem cutIn_union_le (G : Graph) {X U Y : Finset ℕ} (_hUX : U ⊆ X) (hY : Y ⊆ X \ U) :
    G.cutIn X (U ∪ Y) ≤ G.cutIn X U + G.cutIn (X \ U) Y := by
  rw [cutIn_eq_sum_edges, cutIn_eq_sum_edges, cutIn_eq_sum_edges, ← sum_map_add]
  apply sum_map_le_sum_map
  intro e _
  have hdisj : Disjoint U Y := Finset.disjoint_of_subset_right hY disjoint_sdiff_self_right
  have hnot1 : e.1 ∈ U → e.1 ∉ Y := fun h1 h2 => Finset.disjoint_left.mp hdisj h1 h2
  have hnot2 : e.2 ∈ U → e.2 ∉ Y := fun h1 h2 => Finset.disjoint_left.mp hdisj h1 h2
  unfold cutTerm insideB crossesB
  by_cases hx1 : e.1 ∈ X <;> by_cases hx2 : e.2 ∈ X <;>
    by_cases hu1 : e.1 ∈ U <;> by_cases hu2 : e.2 ∈ U <;>
    by_cases hy1 : e.1 ∈ Y <;> by_cases hy2 : e.2 ∈ Y <;>
    simp_all [Finset.mem_union, Finset.mem_sdiff]

/-! ### Peeling loop specification -/

private lemma corePeel_spec {cfg : CoreParams} {r q : ℕ} (hcfg : CoreParamsValid cfg r)
    (hq1 : 1 ≤ q) (hqr : q ≤ r)
    {route : RouterFn} {routeCost : RouterCostFn} (hroute : IsMatchingPlayer route routeCost)
    {cloud : ℕ → Graph} (hcloud : IsCloudExpander cloud cfg.α)
    {subCore : Graph → Finset ℕ → CoreResult}
    (hsubCore : 2 ≤ q → ∀ W Y, Y ⊆ Finset.range W.n → W.IsValid →
      (∀ e ∈ W.inside Y, e.1 ≠ e.2) →
      Y.card ≤ cfg.N ^ (q - 1) → (∀ v ∈ Y, W.degIn Y v ≤ cfg.Δ) →
      CoreSpec cfg (q - 1) W Y (subCore W Y))
    {G : Graph} {X : Finset ℕ}
    (hX : X ⊆ Finset.range G.n) (hGvalid : G.IsValid) (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ cfg.Δ)
    (hXgt : cfg.N ^ (q - 1) < X.card) (hXle : X.card ≤ cfg.N ^ q)
    (fuel : ℕ) (U : Finset ℕ)
    (hUX : U ⊆ X) (hcut : 100 * G.cutIn X U ≤ U.card)
    (hbal : X.card ≤ 4 * (X \ U).card)
    (hfuel : 2 * cfg.D q * X.card ≤ 8 * cfg.D q * U.card + 3 * fuel * X.card) :
    CoreSpec cfg q G X (corePeel cfg route cloud q subCore G X fuel U) := by
  have hDq_pos : 1 ≤ cfg.D q := hcfg.hD_pos hq1 hqr
  have hXpos : 1 ≤ X.card := by
    have hpow : 1 ≤ cfg.N ^ (q - 1) := Nat.one_le_pow _ _ hcfg.hNpos
    omega
  induction fuel generalizing U with
  | zero =>
    unfold corePeel
    have h4U : X.card ≤ 4 * U.card := by
      simp only [mul_zero, zero_mul, add_zero] at hfuel
      have hmul : 2 * cfg.D q * X.card ≤ 2 * cfg.D q * (4 * U.card) := by
        calc 2 * cfg.D q * X.card ≤ 8 * cfg.D q * U.card := hfuel
          _ = 2 * cfg.D q * (4 * U.card) := by ring
      exact Nat.le_of_mul_le_mul_left hmul (by omega)
    have hUleX : U.card ≤ X.card := Finset.card_le_card hUX
    exact ⟨hUX, h4U, hbal, le_trans hcut hUleX⟩
  | succ fuel ih =>
    unfold corePeel
    by_cases hdone : X.card ≤ 4 * U.card
    · simp only [hdone, ↓reduceIte]
      have hUleX : U.card ≤ X.card := Finset.card_le_card hUX
      exact ⟨hUX, hdone, hbal, le_trans hcut hUleX⟩
    · simp only [hdone, ↓reduceIte]
      set X' := X \ U
      have hX'sub : X' ⊆ X := Finset.sdiff_subset
      have hX'card : X'.card + U.card = X.card := Finset.card_sdiff_add_card_eq_card hUX
      have h3X : 3 * X.card < 4 * X'.card := by omega
      have hX'range : X' ⊆ Finset.range G.n := hX'sub.trans hX
      have hX'loop : ∀ e ∈ G.inside X', e.1 ≠ e.2 := by
        intro e he
        rw [mem_inside_iff] at he
        exact hGloop e (mem_inside_iff.mpr ⟨he.1, hX'sub he.2.1, hX'sub he.2.2⟩)
      have hX'deg : ∀ v ∈ X', G.degIn X' v ≤ cfg.Δ :=
        fun v hv => le_trans (degIn_mono hX'sub v) (hdegG v (hX'sub hv))
      have hX'size : (q = 1 → 2 ≤ X'.card ∧ X'.card ≤ cfg.N) ∧
          (2 ≤ q → cfg.N ^ (q - 1) / 2 ≤ X'.card ∧ X'.card ≤ cfg.N ^ q) := by
        refine ⟨fun hq => ?_, fun hq2 => ?_⟩
        · subst hq
          simp only [Nat.sub_self, pow_zero, pow_one] at hXgt hXle
          exact ⟨by omega, by omega⟩
        · have hX'le : X'.card ≤ cfg.N ^ q := by omega
          have hdiv : 2 * (cfg.N ^ (q - 1) / 2) ≤ cfg.N ^ (q - 1) := Nat.mul_div_le _ 2
          exact ⟨by omega, hX'le⟩
      have hos := oneShot_spec hcfg hq1 hqr hroute hcloud hsubCore hX'range hGvalid hX'loop
        hX'deg hX'size
      cases hres : oneShot cfg route cloud q subCore G X' with
      | expander R =>
        rw [hres] at hos
        obtain ⟨hRX', h11, hRexp⟩ := hos
        refine ⟨hRX'.trans hX'sub, ?_, hRexp⟩
        -- `(11 / 12) * (3 / 4) = 33 / 48 > 1 / 2`.
        omega
      | cut V =>
        rw [hres] at hos
        obtain ⟨hVX', hcutV, hV1, hV2⟩ := hos
        set Y := smallerSide X' V
        have hYX' : Y ⊆ X' := by
          unfold Y smallerSide
          split_ifs
          · exact hVX'
          · exact Finset.sdiff_subset
        have hY2 : 2 * Y.card ≤ X'.card := by
          have hadd : (X' \ V).card + V.card = X'.card := Finset.card_sdiff_add_card_eq_card hVX'
          unfold Y smallerSide
          split_ifs <;> omega
        have hYcut : 100 * G.cutIn X' Y ≤ Y.card := by
          unfold Y smallerSide at *
          split_ifs with hle
          · rw [min_eq_left hle] at hcutV
            exact hcutV
          · rw [cutIn_sdiff G X' V hVX']
            rw [min_eq_right (le_of_not_ge hle)] at hcutV
            exact hcutV
        have hYlb : X'.card / cfg.D q + 1 ≤ 2 * Y.card := by
          unfold Y smallerSide
          split_ifs
          · exact hV1
          · exact hV2
        -- Lower bound `3 * X.card < 8 * D_q * Y.card`.
        have hY_big : 3 * X.card < 8 * cfg.D q * Y.card := by
          have hdiv_lt : X'.card < cfg.D q * (X'.card / cfg.D q + 1) := by
            have hmod : X'.card % cfg.D q < cfg.D q := Nat.mod_lt _ (by omega)
            have hdm := Nat.div_add_mod X'.card (cfg.D q)
            rw [Nat.mul_add, Nat.mul_one]
            omega
          have h1 : X'.card < cfg.D q * (2 * Y.card) :=
            lt_of_lt_of_le hdiv_lt (Nat.mul_le_mul_left _ hYlb)
          have h2 : 4 * X'.card < 4 * (cfg.D q * (2 * Y.card)) := by omega
          have h3 : 4 * (cfg.D q * (2 * Y.card)) = 8 * cfg.D q * Y.card := by ring
          omega
        -- Verify the invariant for `U' := U ∪ Y`.
        have hdisjUY : Disjoint U Y :=
          Finset.disjoint_of_subset_right hYX' disjoint_sdiff_self_right
        have hU'X : U ∪ Y ⊆ X := Finset.union_subset hUX (hYX'.trans hX'sub)
        have hU'card : (U ∪ Y).card = U.card + Y.card := Finset.card_union_of_disjoint hdisjUY
        have hU'cut : 100 * G.cutIn X (U ∪ Y) ≤ (U ∪ Y).card := by
          have hadd := cutIn_union_le G hUX hYX'
          dsimp only [X'] at hYcut
          rw [hU'card]
          omega
        have hU'bal : X.card ≤ 4 * (X \ (U ∪ Y)).card := by
          have hsd : (X \ (U ∪ Y)).card + (U ∪ Y).card = X.card :=
            Finset.card_sdiff_add_card_eq_card hU'X
          omega
        have hU'fuel : 2 * cfg.D q * X.card ≤
            8 * cfg.D q * (U ∪ Y).card + 3 * fuel * X.card := by
          rw [hU'card, Nat.mul_add]
          have hstep : 3 * (fuel + 1) * X.card = 3 * fuel * X.card + 3 * X.card := by ring
          rw [hstep] at hfuel
          omega
        exact ih (U ∪ Y) hU'X hU'cut hU'bal hU'fuel

/-! ### The core theorem (`coreOn_spec` and `core_spec`) -/

/-- **Core theorem** (induced-subset form): for every `q ≤ r`, on any valid graph `G` and vertex
subset `X ⊆ Finset.range G.n` (loopless inside `X`, `|X| ≤ N ^ q`, max degree `≤ Δ`),
`coreOn cfg route cloud q G X` returns either a balanced sparse cut or a half-size induced
`1 / P_q`-expander. -/
theorem coreOn_spec {cfg : CoreParams} {r : ℕ} (hcfg : CoreParamsValid cfg r)
    {route : RouterFn} {routeCost : RouterCostFn} (hroute : IsMatchingPlayer route routeCost)
    {cloud : ℕ → Graph} (hcloud : IsCloudExpander cloud cfg.α) :
    ∀ q ≤ r, ∀ (G : Graph) (X : Finset ℕ),
      X ⊆ Finset.range G.n →
      G.IsValid →
      (∀ e ∈ G.inside X, e.1 ≠ e.2) →
      X.card ≤ cfg.N ^ q →
      (∀ v ∈ X, G.degIn X v ≤ cfg.Δ) →
      CoreSpec cfg q G X (coreOn cfg route cloud q G X) := by
  intro q
  induction q with
  | zero =>
    intro _ G X _ _ _ hXle _
    unfold coreOn
    simp only [pow_zero] at hXle
    exact ⟨Finset.Subset.refl X, by omega, isExpansionExpanderOn_of_card_le_one G hXle _⟩
  | succ q ih =>
    intro hqr G X hX hGvalid hGloop hXle hdegG
    unfold coreOn
    by_cases h1 : X.card ≤ 1
    · simp only [h1, ↓reduceIte]
      exact ⟨Finset.Subset.refl X, by omega, isExpansionExpanderOn_of_card_le_one G h1 _⟩
    · simp only [h1, ↓reduceIte]
      by_cases hdel : X.card ≤ cfg.N ^ q
      · simp only [hdel, ↓reduceIte]
        have hprev := ih (Nat.le_of_succ_le hqr) G X hX hGvalid hGloop hdel hdegG
        cases hres : coreOn cfg route cloud q G X with
        | cut U =>
          rw [hres] at hprev
          exact hprev
        | expander S =>
          rw [hres] at hprev
          obtain ⟨hSX, h2S, hSexp⟩ := hprev
          have hPpos : (0 : ℝ) < cfg.P q := Nat.cast_pos.mpr (hcfg.hP_pos (Nat.le_of_succ_le hqr))
          have hPmono : (cfg.P q : ℝ) ≤ cfg.P (q + 1) := by
            exact_mod_cast hcfg.hPmono q hqr
          have hinv : 1 / (cfg.P (q + 1) : ℝ) ≤ 1 / (cfg.P q : ℝ) :=
            one_div_le_one_div_of_le hPpos hPmono
          exact ⟨hSX, h2S, IsExpansionExpanderOn.mono hinv hSexp⟩
      · simp only [hdel, ↓reduceIte]
        have hXgt : cfg.N ^ q < X.card := by omega
        have hsubCore : 2 ≤ q + 1 → ∀ W Y, Y ⊆ Finset.range W.n → W.IsValid →
            (∀ e ∈ W.inside Y, e.1 ≠ e.2) →
            Y.card ≤ cfg.N ^ q → (∀ v ∈ Y, W.degIn Y v ≤ cfg.Δ) →
            CoreSpec cfg q W Y (coreOn cfg route cloud q W Y) :=
          fun _ => ih (Nat.le_of_succ_le hqr)
        have hfuel0 : 2 * cfg.D (q + 1) * X.card ≤
            8 * cfg.D (q + 1) * (∅ : Finset ℕ).card + 3 * (2 * cfg.D (q + 1)) * X.card := by
          simp only [Finset.card_empty, mul_zero, zero_add]
          have h6 : 3 * (2 * cfg.D (q + 1)) * X.card = 6 * cfg.D (q + 1) * X.card := by ring
          rw [h6]
          exact Nat.mul_le_mul_right X.card (Nat.mul_le_mul_right (cfg.D (q + 1)) (by decide))
        exact corePeel_spec hcfg (by omega) hqr hroute hcloud hsubCore hX hGvalid hGloop hdegG
          hXgt hXle (2 * cfg.D (q + 1)) ∅ (Finset.empty_subset X)
          (by simp [Graph.cutIn, Graph.inside])
          (by simp; omega) hfuel0

/-- **Core theorem** (whole-graph form): for every `q ≤ r`, on any valid loopless graph `G` with
`G.n ≤ N ^ q` and maximum degree at most `Δ`, `core cfg route cloud q G` returns either a balanced
sparse cut or a half-size induced `1 / P_q`-expander. -/
theorem core_spec {cfg : CoreParams} {r : ℕ} (hcfg : CoreParamsValid cfg r)
    {route : RouterFn} {routeCost : RouterCostFn} (hroute : IsMatchingPlayer route routeCost)
    {cloud : ℕ → Graph} (hcloud : IsCloudExpander cloud cfg.α)
    {q : ℕ} (hqr : q ≤ r) {G : Graph}
    (hGvalid : G.IsValid) (hGloop : G.IsLoopless)
    (hn : G.n ≤ cfg.N ^ q) (hdeg : ∀ v < G.n, G.deg v ≤ cfg.Δ) :
    CoreSpec cfg q G G.verts (core cfg route cloud q G) := by
  refine coreOn_spec hcfg hroute hcloud q hqr G G.verts (Finset.Subset.refl _) hGvalid
    (fun e he => hGloop e (mem_inside_iff.mp he).1)
    (by simp [Graph.verts, hn])
    (fun v hv => hdeg v (Finset.mem_range.mp hv))

end MinCostFlow.ExpanderDecomp
