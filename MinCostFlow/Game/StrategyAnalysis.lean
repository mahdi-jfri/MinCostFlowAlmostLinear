module

public import MinCostFlow.Game.Lemma75

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Shift-and-Rebuild Game: Analysis of Algorithm 3 and Lemma 7.3

This file completes the formalization of Section 7.2 (pages 35–38) of the paper
(*A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow*, arXiv:2309.16629v1),
building on `MinCostFlow.Game.Lemma75` and culminating in **Lemma 7.3** (`lemma_7_3`, page 35).

Following the paper's proof step by step:
1. **Claims 7.8 and 7.9** (`claim_7_8`, `claim_7_9`, page 37), **Events 1–3** (`event_1`,
   `event_2`, `event_3`), and **Cases A–C** (`case_A`, `case_B`, `case_C`, pages 37–38)
   establishing `GameIH` (`gameIH_holds`) and `passes_0 < 2Ψ` (`passes_zero_lt`) at every step `s`.
2. The counting argument at the start of the proof of Lemma 7.3, yielding `lemma_7_3`.

Departures from the paper, each fixing an error in it:
- **Lemma 7.3 (page 35)**: adds the initial-budget term `(10Ψk)^{i+1}` (equivalently
  replacing `r_0` by `r_0 + 1`), because at the start of the game the initial stretches can
  force shifts even when `r_0 = ... = r_i = 0`.
- **Event 1 (page 37)**: resets levels `i' ≥ i` (matching Definition 7.2 and Algorithm 3)
  rather than `i' ≤ i`.
- **Claim 7.9 (page 37)**: uses `repT^{(s+1)}_{i'} = t` for `i' > i`.
- **Case C (pages 37–38)**: branches on `bran^{(s+1)}_i = 0` rather than `repT^{(s+1)}_i =
  repT^{(s)}_i`; searches the full `k`-branch cycle ending at `s` (rather than only `(s_1, s]`,
  where `str_i` may exceed `σ`); and derives the `i^* > i` contradiction directly at step `x`
  from `GameIH` at step `x` (avoiding the intermediate step `y`, which need not preserve
  levels `< i^*` when `rebuild` or lower `shift` steps intervene).
-/

namespace MinCostFlow.Game

@[expose] public section

/-- **Claim 7.8** (page 37):
at step `s`, if the player chooses `shift-step(i)` under Algorithm 3 and `GameIH` holds at `s`,
then `M^{(s)} ∩ P^{(s)} ∩ {i + 1, ..., d} = ∅`. -/
theorem claim_7_8 (params : GameParams) {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    (hv : ValidPlayPrefix params W initStr moves)
    (hf : FollowsStrategyPrefix params W initStr moves)
    {s : ℕ} (hs : s < moves.length)
    (hih : GameIH params W (stateAt W params.hk initStr moves s)
      (passesAt W params.hk initStr moves s))
    {i : Fin (params.d + 1)} {adv : RoundChoice} {newStr : Fin (params.d + 1) → Fin params.k → ℝ}
    (hm : moves[s] = .roundStep adv (.shift i) newStr) :
    ∀ i' : Fin (params.d + 1), i < i' →
      ¬ (i' ∈ PrefixMaxSet W (stateAt W params.hk initStr moves s) ∧
         i' ∈ PrefixGoodStretchSet params.σ (stateAt W params.hk initStr moves s)) := by
  intro i' hi' ⟨hM, hP⟩
  have hmne : moves ≠ [] := List.ne_nil_of_length_pos (Nat.zero_lt_of_lt hs)
  have hP_ge := (shift_step_strategy_props params hv hf hs hm).2.2 i' hi'
  have h2Psi : 2 * params.Ψ ≤ (passesAt W params.hk initStr moves s i' : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hP_ge)
  have hlog := hih i' hM hP
  have hwv := weightValid_repT hv hmne (le_of_lt hs) i'
  linarith [hwv.2.1]

/-- **Claim 7.9** (page 37):
at the start of step `s + 1` after `shift-step(i)` at step `s`, `GameIH` holds for all
levels `i' ≠ i`. -/
theorem claim_7_9 (params : GameParams) {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    (hv : ValidPlayPrefix params W initStr moves)
    {s : ℕ} (hs : s < moves.length)
    (hih : GameIH params W (stateAt W params.hk initStr moves s)
      (passesAt W params.hk initStr moves s))
    {i : Fin (params.d + 1)} {adv : RoundChoice} {newStr : Fin (params.d + 1) → Fin params.k → ℝ}
    (hm : moves[s] = .roundStep adv (.shift i) newStr) :
    ∀ i' : Fin (params.d + 1), i' ≠ i →
      i' ∈ PrefixMaxSet W (stateAt W params.hk initStr moves (s + 1)) →
      i' ∈ PrefixGoodStretchSet params.σ (stateAt W params.hk initStr moves (s + 1)) →
      Real.logb 2 (W ((stateAt W params.hk initStr moves (s + 1)).repT i')) <
        params.Ψ - (passesAt W params.hk initStr moves (s + 1) i' : ℝ) := by
  intro i' hne hM hP
  have htr := state_passes_shift W params.hk (stateAt W params.hk initStr moves s)
    (passesAt W params.hk initStr moves s) adv i newStr
  rw [stateAt_succ W params.hk initStr moves hs, passesAt_succ W params.hk initStr moves hs, hm]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hM_s : i' ∈ PrefixMaxSet W (stateAt W params.hk initStr moves s) := by
      intro a ha
      have ha_lt : a < i := lt_trans ha hlt
      have h1 := (htr.2.2.2.2 a ha_lt).2.1
      have h2 := (htr.2.2.2.2 i' hlt).2.1
      have hMa := hM a ha
      rw [stateAt_succ W params.hk initStr moves hs, hm, h1, h2] at hMa
      exact hMa
    have hP_s : i' ∈ PrefixGoodStretchSet params.σ (stateAt W params.hk initStr moves s) := by
      intro a ha
      have ha_lt : a < i := lt_trans ha hlt
      have hb := (htr.2.2.2.2 a ha_lt).1
      have hs' := (htr.2.2.2.2 a ha_lt).2.2.1
      have hPa := hP a ha
      rw [stateAt_succ W params.hk initStr moves hs, hm, hb, hs'] at hPa
      exact hPa
    have hself := htr.2.2.2.2 i' hlt
    rw [hself.2.1, hself.2.2.2]
    exact hih i' hM_s hP_s
  · have h1 := (htr.1 i' hgt).2.1
    have h2 := (htr.1 i' hgt).2.2.2
    rw [h1, h2]
    have hwr := weightValid_round_of_lt hv hs
    simp [hwr.2.2]

/-- **Event 1** (page 37): if `GameIH` holds at step `s` and the adversary chooses
`rebuild-step(i)`, then `GameIH` holds at step `s + 1`. -/
theorem event_1 (params : GameParams) {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    (hv : ValidPlayPrefix params W initStr moves)
    {s : ℕ} (hs : s < moves.length)
    (hih : GameIH params W (stateAt W params.hk initStr moves s)
      (passesAt W params.hk initStr moves s))
    {i : Fin (params.d + 1)} {newStr : Fin (params.d + 1) → Fin params.k → ℝ}
    (hm : moves[s] = .advRebuild i newStr) :
    GameIH params W (stateAt W params.hk initStr moves (s + 1))
      (passesAt W params.hk initStr moves (s + 1)) := by
  intro i' hM hP
  have htr := state_passes_advRebuild W params.hk (stateAt W params.hk initStr moves s)
    (passesAt W params.hk initStr moves s) i newStr
  rw [stateAt_succ W params.hk initStr moves hs, passesAt_succ W params.hk initStr moves hs, hm]
  by_cases hle : i ≤ i'
  · have hi' := htr.1 i' hle
    rw [hi'.2.1, hi'.2.2.2]
    have hwr := weightValid_round_of_lt hv hs
    simp [hwr.2.2]
  · have hlt : i' < i := not_le.mp hle
    have hM_s : i' ∈ PrefixMaxSet W (stateAt W params.hk initStr moves s) := by
      intro a ha
      have ha_lt : a < i := lt_trans ha hlt
      have h1 := (htr.2 a ha_lt).2.1
      have h2 := (htr.2 i' hlt).2.1
      have hMa := hM a ha
      rw [stateAt_succ W params.hk initStr moves hs, hm, h1, h2] at hMa
      exact hMa
    have hP_s : i' ∈ PrefixGoodStretchSet params.σ (stateAt W params.hk initStr moves s) := by
      intro a ha
      have ha_lt : a < i := lt_trans ha hlt
      have hb := (htr.2 a ha_lt).1
      have hs' := (htr.2 a ha_lt).2.2.1
      have hPa := hP a ha
      rw [stateAt_succ W params.hk initStr moves hs, hm, hb, hs'] at hPa
      exact hPa
    have hself := htr.2 i' hlt
    rw [hself.2.1, hself.2.2.2]
    exact hih i' hM_s hP_s

/-- **Event 2** (page 37): if `GameIH` holds at step `s` and the adversary or player chooses
`do-nothing-step`, then `GameIH` holds at step `s + 1`. -/
theorem event_2 (params : GameParams) {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    {s : ℕ} (hs : s < moves.length)
    (hih : GameIH params W (stateAt W params.hk initStr moves s)
      (passesAt W params.hk initStr moves s))
    (hm : moves[s] = .advDoNothing ∨
      ∃ adv newStr, moves[s] = .roundStep adv .doNothing newStr) :
    GameIH params W (stateAt W params.hk initStr moves (s + 1))
      (passesAt W params.hk initStr moves (s + 1)) := by
  intro i' hM hP
  rw [stateAt_succ W params.hk initStr moves hs, passesAt_succ W params.hk initStr moves hs]
  rcases hm with hm_adv | ⟨adv, newStr, hm_pl⟩
  · rw [hm_adv]
    have htr := state_passes_advDoNothing W params.hk (stateAt W params.hk initStr moves s)
      (passesAt W params.hk initStr moves s)
    have hM_s : i' ∈ PrefixMaxSet W (stateAt W params.hk initStr moves s) := by
      intro a ha
      have hMa := hM a ha
      rw [stateAt_succ W params.hk initStr moves hs, hm_adv, htr.2.1] at hMa
      exact hMa
    have hP_s : i' ∈ PrefixGoodStretchSet params.σ (stateAt W params.hk initStr moves s) := by
      intro a ha
      have hPa := hP a ha
      rw [stateAt_succ W params.hk initStr moves hs, hm_adv, htr.1, htr.2.2.1] at hPa
      exact hPa
    rw [htr.2.1, htr.2.2.2]
    exact hih i' hM_s hP_s
  · rw [hm_pl]
    have htr := state_passes_roundDoNothing W params.hk (stateAt W params.hk initStr moves s)
      (passesAt W params.hk initStr moves s) adv newStr
    have hM_s : i' ∈ PrefixMaxSet W (stateAt W params.hk initStr moves s) := by
      intro a ha
      have hMa := hM a ha
      rw [stateAt_succ W params.hk initStr moves hs, hm_pl, htr.2.1] at hMa
      exact hMa
    have hP_s : i' ∈ PrefixGoodStretchSet params.σ (stateAt W params.hk initStr moves s) := by
      intro a ha
      have hPa := hP a ha
      rw [stateAt_succ W params.hk initStr moves hs, hm_pl, htr.1, htr.2.2.1] at hPa
      exact hPa
    rw [htr.2.1, htr.2.2.2]
    exact hih i' hM_s hP_s

/-- **Case A** (page 37) inside Event 3:
when `i ∉ M^{(s)}`, we also have `i ∉ M^{(s+1)}`, so `GameIH` holds at level `i` at step `s + 1`. -/
theorem case_A (params : GameParams) {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    {s : ℕ} (hs : s < moves.length)
    {i : Fin (params.d + 1)} {adv : RoundChoice} {newStr : Fin (params.d + 1) → Fin params.k → ℝ}
    (hm : moves[s] = .roundStep adv (.shift i) newStr)
    (hnotM : i ∉ PrefixMaxSet W (stateAt W params.hk initStr moves s)) :
    i ∈ PrefixMaxSet W (stateAt W params.hk initStr moves (s + 1)) →
    i ∈ PrefixGoodStretchSet params.σ (stateAt W params.hk initStr moves (s + 1)) →
    Real.logb 2 (W ((stateAt W params.hk initStr moves (s + 1)).repT i)) <
      params.Ψ - (passesAt W params.hk initStr moves (s + 1) i : ℝ) := by
  intro hM_succ _
  exfalso
  simp only [PrefixMaxSet, Set.mem_ofPred_eq, not_forall, not_lt] at hnotM
  rcases hnotM with ⟨a, ha, hge⟩
  have htr := state_passes_shift W params.hk (stateAt W params.hk initStr moves s)
    (passesAt W params.hk initStr moves s) adv i newStr
  have ha_eq : (stateAt W params.hk initStr moves (s + 1)).repT a =
      (stateAt W params.hk initStr moves s).repT a := by
    rw [stateAt_succ W params.hk initStr moves hs, hm]
    exact (htr.2.2.2.2 a ha).2.1
  have hi_le : W ((stateAt W params.hk initStr moves (s + 1)).repT i) ≤
      W ((stateAt W params.hk initStr moves s).repT i) := by
    rw [stateAt_succ W params.hk initStr moves hs, hm]
    exact shift_repT_weight_le W params.hk _ adv i newStr
      (repT_bounds W params.hk initStr moves s i).2
  have hlt := hM_succ a ha
  rw [ha_eq] at hlt
  linarith

/-- **Case B** (page 37) inside Event 3:
when `i ∈ M^{(s)}` and `i ∉ P^{(s)}`, we also have `i ∉ P^{(s+1)}`, so `GameIH` holds at
level `i` at step `s + 1`. -/
theorem case_B (params : GameParams) {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    {s : ℕ} (hs : s < moves.length)
    {i : Fin (params.d + 1)} {adv : RoundChoice} {newStr : Fin (params.d + 1) → Fin params.k → ℝ}
    (hm : moves[s] = .roundStep adv (.shift i) newStr)
    (hnotP : i ∉ PrefixGoodStretchSet params.σ (stateAt W params.hk initStr moves s)) :
    i ∈ PrefixMaxSet W (stateAt W params.hk initStr moves (s + 1)) →
    i ∈ PrefixGoodStretchSet params.σ (stateAt W params.hk initStr moves (s + 1)) →
    Real.logb 2 (W ((stateAt W params.hk initStr moves (s + 1)).repT i)) <
      params.Ψ - (passesAt W params.hk initStr moves (s + 1) i : ℝ) := by
  intro _ hP_succ
  exfalso
  simp only [PrefixGoodStretchSet, Set.mem_ofPred_eq, not_forall, not_le] at hnotP
  rcases hnotP with ⟨a, ha, hgt⟩
  have htr := state_passes_shift W params.hk (stateAt W params.hk initStr moves s)
    (passesAt W params.hk initStr moves s) adv i newStr
  have ha_bran : (stateAt W params.hk initStr moves (s + 1)).bran a =
      (stateAt W params.hk initStr moves s).bran a := by
    rw [stateAt_succ W params.hk initStr moves hs, hm]
    exact (htr.2.2.2.2 a ha).1
  have ha_str : (stateAt W params.hk initStr moves (s + 1)).str a =
      (stateAt W params.hk initStr moves s).str a := by
    rw [stateAt_succ W params.hk initStr moves hs, hm]
    exact (htr.2.2.2.2 a ha).2.2.1
  have hle := hP_succ a ha
  rw [ha_bran, ha_str] at hle
  linarith

/-- **Case C** (pages 37–38) inside Event 3:
when `i ∈ M^{(s)} ∩ P^{(s)}` and `GameIH` holds for all steps `≤ s`, `GameIH` holds at level `i`
at step `s + 1`. -/
theorem case_C (params : GameParams) {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    (hv : ValidPlayPrefix params W initStr moves)
    (hf : FollowsStrategyPrefix params W initStr moves)
    {s : ℕ} (hs : s < moves.length)
    (hih_all : ∀ t ≤ s, GameIH params W (stateAt W params.hk initStr moves t)
      (passesAt W params.hk initStr moves t))
    {i : Fin (params.d + 1)} {adv : RoundChoice} {newStr : Fin (params.d + 1) → Fin params.k → ℝ}
    (hm : moves[s] = .roundStep adv (.shift i) newStr)
    (hM : i ∈ PrefixMaxSet W (stateAt W params.hk initStr moves s))
    (hP : i ∈ PrefixGoodStretchSet params.σ (stateAt W params.hk initStr moves s)) :
    i ∈ PrefixMaxSet W (stateAt W params.hk initStr moves (s + 1)) →
    i ∈ PrefixGoodStretchSet params.σ (stateAt W params.hk initStr moves (s + 1)) →
    Real.logb 2 (W ((stateAt W params.hk initStr moves (s + 1)).repT i)) <
      params.Ψ - (passesAt W params.hk initStr moves (s + 1) i : ℝ) := by
  intro _ _
  have htr := state_passes_shift W params.hk (stateAt W params.hk initStr moves s)
    (passesAt W params.hk initStr moves s) adv i newStr
  by_cases hwrap : (nextBranch params.hk ((stateAt W params.hk initStr moves s).bran i)).val = 0
  · -- Wrapping branch: `repT_i` updates via (15) and `passes_i` increments by 1.
    have hup := htr.2.2.1 hwrap
    have hrep_succ : (stateAt W params.hk initStr moves (s + 1)).repT i =
        argminRound W ((stateAt W params.hk initStr moves s).repT i)
          (stateAt W params.hk initStr moves s).round := by
      rw [stateAt_succ W params.hk initStr moves hs, hm]; exact hup.1
    have hps_succ : passesAt W params.hk initStr moves (s + 1) i =
        passesAt W params.hk initStr moves s i + 1 := by
      rw [passesAt_succ W params.hk initStr moves hs, hm]; exact hup.2.2
    have hbk : ((stateAt W params.hk initStr moves s).bran i).val + 1 = params.k :=
      (nextBranch_val_eq_zero_iff params.hk _).mp hwrap
    let p₀ := passesAt W params.hk initStr moves s i
    let P := Nat.ceil (2 * params.Ψ)
    have hP2 : 2 ≤ P := by
      have h1 : (2 : ℝ) ≤ (P : ℝ) := le_trans (by linarith [params.hΨ]) (Nat.le_ceil _)
      exact_mod_cast h1
    have hphi_s : levelPhi W params.hk initStr moves i s = p₀ * params.k + (params.k - 1) := by
      have hkpos := params.hk
      dsimp only [p₀]
      unfold levelPhi; omega
    have hphi_s1 : levelPhi W params.hk initStr moves i (s + 1) = (p₀ + 1) * params.k := by
      rw [levelPhi_shift_self W params.hk initStr moves i hs hm, hphi_s]
      have hk1 : 1 ≤ params.k := params.hk
      calc
        p₀ * params.k + (params.k - 1) + 1 = p₀ * params.k + params.k := by omega
        _ = (p₀ + 1) * params.k := by ring
    -- Last reset step `a₀ ≤ s` at or below level `i`.
    classical
    let S₀ := (Finset.range (s + 1)).filter
      (fun t => t = 0 ∨ ∃ m, moves[t - 1]? = some m ∧ ¬ PreservesBelow i m)
    have hS₀ : S₀.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Or.inl rfl⟩⟩
    let a₀ := S₀.max' hS₀
    have ha₀_mem := Finset.mem_filter.mp (Finset.max'_mem S₀ hS₀)
    have ha₀_le : a₀ ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha₀_mem.1)
    have hpb_a₀ : ∀ t (ht1 : a₀ ≤ t) (ht2 : t < s + 1),
        PreservesBelow i (moves[t]'(lt_of_le_of_lt (Nat.lt_succ_iff.mp ht2) hs)) := by
      intro t ht1 ht2
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ht2) with hts | rfl
      · by_contra hnpb
        have hget : moves[t + 1 - 1]? = some moves[t] := by
          rw [Nat.add_sub_cancel]
          exact List.getElem?_eq_getElem (lt_trans hts hs)
        have hmem : t + 1 ∈ S₀ := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), Or.inr ⟨moves[t], hget, hnpb⟩⟩
        have hle := Finset.le_max' S₀ (t + 1) hmem
        omega
      · refine ⟨?_, ?_⟩
        · intro i₀ newStr₀ h; rw [hm] at h; cases h
        · intro i₀ adv₀ newStr₀ h; rw [hm] at h; cases h; exact le_rfl
    have ha₀_cases : a₀ = 0 ∨
        (0 < a₀ ∧ ¬ PreservesBelow i (moves[a₀ - 1]'(by omega))) := by
      rcases ha₀_mem.2 with ha₀_0 | ⟨m, hm?, hnpb⟩
      · exact Or.inl ha₀_0
      · have ha₀_pos : 0 < a₀ := by
          by_contra h0
          have h0' : a₀ = 0 := by omega
          change moves[a₀ - 1]? = some m at hm?
          rw [h0', Nat.zero_sub] at hm?
          have hlt0 : 0 < moves.length := by omega
          rw [List.getElem?_eq_getElem hlt0] at hm?
          injection hm? with hmEq
          subst hmEq
          have h0pb := hpb_a₀ 0 (by rw [h0']) (by omega)
          exact hnpb h0pb
        have hlt_len : a₀ - 1 < moves.length := by omega
        rw [List.getElem?_eq_getElem hlt_len] at hm?
        injection hm? with hmEq
        subst hmEq
        exact Or.inr ⟨ha₀_pos, hnpb⟩
    have hphi_a₀ : levelPhi W params.hk initStr moves i a₀ = 0 := by
      rcases ha₀_cases with ha₀_0 | ⟨ha₀_pos, hnpb⟩
      · rw [ha₀_0, levelPhi_zero]
      · have hlt_len : a₀ - 1 < moves.length := by omega
        have hcases := levelPhi_step_cases W params.hk initStr moves i hlt_len
        have hsub : (a₀ - 1) + 1 = a₀ := Nat.sub_add_cancel ha₀_pos
        rw [← hsub]
        simp only [PreservesBelow, not_and_or, not_forall, not_lt, not_le] at hnpb
        rcases hnpb with ⟨i₀, newStr₀, hm₀, hle⟩ | ⟨i₀, adv₀, newStr₀, hm₀, hlt⟩
        · exact hcases.1 i₀ newStr₀ hm₀ hle
        · exact hcases.2.1 i₀ adv₀ newStr₀ hm₀ hlt
    have ha₀_passes_gt : ∀ i' : Fin (params.d + 1), i < i' →
        passesAt W params.hk initStr moves a₀ i' = 0 := by
      intro i' hi'
      rcases ha₀_cases with ha₀_0 | ⟨ha₀_pos, hnpb⟩
      · rw [ha₀_0, passesAt_zero]
      · have hlt_len : a₀ - 1 < moves.length := by omega
        have hsub : (a₀ - 1) + 1 = a₀ := Nat.sub_add_cancel ha₀_pos
        rw [← hsub, passesAt_succ W params.hk initStr moves hlt_len]
        simp only [PreservesBelow, not_and_or, not_forall, not_lt, not_le] at hnpb
        rcases hnpb with ⟨i₀, newStr₀, hm₀, hle⟩ | ⟨i₀, adv₀, newStr₀, hm₀, hlt⟩
        · rw [hm₀]
          exact ((state_passes_advRebuild W params.hk
            (stateAt W params.hk initStr moves (a₀ - 1))
            (passesAt W params.hk initStr moves (a₀ - 1)) i₀ newStr₀).1 i'
            (le_trans hle (le_of_lt hi'))).2.2.2
        · rw [hm₀]
          exact ((state_passes_shift W params.hk
            (stateAt W params.hk initStr moves (a₀ - 1))
            (passesAt W params.hk initStr moves (a₀ - 1)) adv₀ i₀ newStr₀).1 i'
            (lt_trans hlt hi')).2.2.2
    obtain ⟨jStar, hjStar⟩ := (str_nonneg_and_valid hv s (le_of_lt hs) i).2
    let target := p₀ * params.k + jStar.val
    have htarget_lo : levelPhi W params.hk initStr moves i a₀ ≤ target := by
      rw [hphi_a₀]; exact Nat.zero_le _
    have htarget_hi : target < levelPhi W params.hk initStr moves i (s + 1) := by
      rw [hphi_s1]
      have hjlt := jStar.isLt
      have : (p₀ + 1) * params.k = p₀ * params.k + params.k := by ring
      omega
    have hstep_phi : ∀ t, a₀ ≤ t → t < s + 1 →
        levelPhi W params.hk initStr moves i (t + 1) ≤ levelPhi W params.hk initStr moves i t + 1 :=
      fun t ht1 ht2 => (levelPhi_mono_of_preservesBelow W params.hk initStr moves i
        (by omega) (hpb_a₀ t ht1 ht2)).2
    obtain ⟨u_end, hu_end1, hu_end2, hu_end_eq, hu_end_succ, _⟩ := unitStep_last_eq
      (levelPhi W params.hk initStr moves i) (by omega) htarget_lo htarget_hi hstep_phi
    have hu_end_len : u_end < moves.length := lt_of_le_of_lt (Nat.le_of_lt_succ hu_end2) hs
    have hu_end_le : u_end ≤ s := Nat.le_of_lt_succ hu_end2
    have hu_end_shift : ∃ newStr_e, moves[u_end] = .roundStep .roundContinuing (.shift i) newStr_e := by
      obtain ⟨adv_e, newStr_e, hm_e⟩ := shift_self_of_levelPhi_lt W params.hk initStr moves
        hu_end_len (hpb_a₀ u_end hu_end1 hu_end2) (by omega)
      have hadv := (shift_step_strategy_props params hv hf hu_end_len hm_e).1
      subst hadv
      exact ⟨newStr_e, hm_e⟩
    obtain ⟨a', ha'1, ha'2, ha'_eq, ha'_prev, ha'_lt⟩ := unitStep_first_eq
      (levelPhi W params.hk initStr moves i) hu_end1 htarget_lo (le_of_eq hu_end_eq.symm)
      (fun t ht1 ht2 => hstep_phi t ht1 (lt_trans ht2 hu_end2))
    have hphi_const : ∀ t, a' ≤ t → t ≤ u_end →
        levelPhi W params.hk initStr moves i t = target := by
      intro t ht1 ht2
      have h1 := levelPhi_mono_le W params.hk initStr moves i (by omega)
        (fun x hx1 hx2 => hpb_a₀ x hx1 (by omega)) ha'1 ht1 ht2
      have h2 := levelPhi_mono_le W params.hk initStr moves i (by omega)
        (fun x hx1 hx2 => hpb_a₀ x hx1 (by omega)) (by omega) ht2 le_rfl
      omega
    have hband : ∀ t, a' ≤ t → t ≤ s →
        p₀ * params.k ≤ levelPhi W params.hk initStr moves i t ∧
        levelPhi W params.hk initStr moves i t < (p₀ + 1) * params.k := by
      intro t ht1 ht2
      have h1 := levelPhi_mono_le W params.hk initStr moves i (by omega)
        (fun x hx1 hx2 => hpb_a₀ x hx1 (by omega)) ha'1 ht1 ht2
      have h2 := levelPhi_mono_le W params.hk initStr moves i (by omega)
        (fun x hx1 hx2 => hpb_a₀ x hx1 (by omega)) (by omega) ht2 le_rfl
      have hmul : (p₀ + 1) * params.k = p₀ * params.k + params.k := by ring
      have hkpos := params.hk
      omega
    have hconst_s := interval_str_repT_of_phi_band W params.hk initStr moves i
      (le_of_lt hs) (fun t ht1 ht2 => hpb_a₀ t (by omega) (by omega)) hband
    have hstr_a' : (stateAt W params.hk initStr moves a').str i =
        (stateAt W params.hk initStr moves s).str i :=
      (hconst_s s (by omega) le_rfl).1.symm
    have hrepT_const : ∀ t, a' ≤ t → t ≤ u_end →
        (stateAt W params.hk initStr moves t).repT i = (stateAt W params.hk initStr moves s).repT i ∧
        (∀ i' < i,
          (stateAt W params.hk initStr moves t).repT i' = (stateAt W params.hk initStr moves s).repT i' ∧
          (stateAt W params.hk initStr moves t).str i' ((stateAt W params.hk initStr moves t).bran i') =
            (stateAt W params.hk initStr moves s).str i' ((stateAt W params.hk initStr moves s).bran i')) := by
      intro t ht1 ht2
      have ht_props := hconst_s t ht1 (le_trans ht2 hu_end_le)
      have hs_props := hconst_s s (by omega) le_rfl
      refine ⟨ht_props.2.1.trans hs_props.2.1.symm, fun i' hi' => ?_⟩
      have ht' := ht_props.2.2 i' hi'
      have hs' := hs_props.2.2 i' hi'
      refine ⟨ht'.2.1.trans hs'.2.1.symm, ?_⟩
      rw [ht'.1, ht'.2.2.1, ← hs'.1, ← hs'.2.2.1]
    have ha'_passes_gt : ∀ i' : Fin (params.d + 1), i < i' →
        passesAt W params.hk initStr moves a' i' = 0 := by
      intro i' hi'
      by_cases htar0 : target = 0
      · have ha'_eq_a₀ : a' = a₀ := by
          by_contra hne
          have hlt := lt_of_le_of_ne ha'1 (Ne.symm hne)
          have hbad := ha'_lt a₀ le_rfl hlt
          rw [hphi_a₀, htar0] at hbad
          exact lt_irrefl 0 hbad
        rw [ha'_eq_a₀]
        exact ha₀_passes_gt i' hi'
      · have hlt_tar : levelPhi W params.hk initStr moves i a₀ < target := by
          rw [hphi_a₀]; omega
        obtain ⟨ha'_gt, hprev_eq⟩ := ha'_prev hlt_tar
        have hpred_len : a' - 1 < moves.length := by omega
        have hpred_lt : levelPhi W params.hk initStr moves i (a' - 1) <
            levelPhi W params.hk initStr moves i ((a' - 1) + 1) := by
          rw [Nat.sub_add_cancel (by omega), ha'_eq]; omega
        obtain ⟨adv_p, newStr_p, hm_p⟩ := shift_self_of_levelPhi_lt W params.hk initStr moves
          hpred_len (hpb_a₀ (a' - 1) (by omega) (by omega)) hpred_lt
        rw [show a' = (a' - 1) + 1 by omega, passesAt_succ W params.hk initStr moves hpred_len, hm_p]
        exact ((state_passes_shift W params.hk _ _ adv_p i newStr_p).1 i' hi').2.2.2
    -- Obtain the good step `x ∈ [a', u_end]` with all stretches `≤ σ` and `passes_{i'} = P - 1` for `i' > i`.
    have hex : ∃ x, a' ≤ x ∧ x ≤ u_end ∧
        (∃ i₀ newStr_x, moves[x]? = some (.roundStep .roundContinuing (.shift i₀) newStr_x)) ∧
        (∀ i' : Fin (params.d + 1), (stateAt W params.hk initStr moves x).str i'
          ((stateAt W params.hk initStr moves x).bran i') ≤ params.σ) ∧
        (∀ i' : Fin (params.d + 1), i < i' →
          passesAt W params.hk initStr moves x i' = P - 1) := by
      by_cases htop : i.val < params.d
      · have hpres_i : ∀ t, a' ≤ t → (ht2 : t < u_end) →
            PreservesUpTo i (moves[t]'(lt_of_lt_of_le ht2 (le_of_lt hu_end_len))) := by
          intro t ht1 ht2
          have hp := hpb_a₀ t (by omega) (by omega)
          refine ⟨hp.1, fun i₀ adv₀ newStr₀ hm₀ => ?_⟩
          have hge := hp.2 i₀ adv₀ newStr₀ hm₀
          rcases eq_or_lt_of_le hge with rfl | hgt
          · exfalso
            have hlen_t : t < moves.length := lt_of_lt_of_le ht2 (le_of_lt hu_end_len)
            have hinc := levelPhi_shift_self W params.hk initStr moves i hlen_t hm₀
            have hc1 := hphi_const t ht1 (le_of_lt ht2)
            have hc2 := hphi_const (t + 1) (by omega) ht2
            omega
          · exact hgt
        have hu_end_passes_gt : ∀ i' : Fin (params.d + 1), i < i' →
            P ≤ passesAt W params.hk initStr moves u_end i' := by
          rcases hu_end_shift with ⟨newStr_e, hm_e⟩
          exact (shift_step_strategy_props params hv hf hu_end_len hm_e).2.2
        obtain ⟨x, hx1, hx2, hx_shift, hx_props⟩ := lemma_7_5_interval params hv hf
          (params.d - i.val) i htop rfl a' u_end ha'2 (le_of_lt hu_end_len)
          hpres_i ha'_passes_gt hu_end_passes_gt
        refine ⟨x, hx1, le_of_lt hx2, hx_shift, fun i' => ?_, fun i' hi' => (hx_props i' hi').2⟩
        rcases lt_trichotomy i' i with hlt | rfl | hgt
        · have hx_lt := (hrepT_const x hx1 (le_of_lt hx2)).2 i' hlt
          rw [hx_lt.2]
          exact hP i' hlt
        · have hphi_x := hphi_const x hx1 (le_of_lt hx2)
          have hbran_x : (stateAt W params.hk initStr moves x).bran i' = jStar := by
            ext
            rw [bran_val_eq_levelPhi_mod, hphi_x]
            dsimp only [target]
            rw [Nat.mul_comm _ params.k, Nat.mul_add_mod, Nat.mod_eq_of_lt jStar.isLt]
          have hstr_x := (hconst_s x hx1 (by omega)).1
          rw [hbran_x, hstr_x, hstr_a']
          exact hjStar
        · exact (hx_props i' hgt).1
      · have hi_eq_d : i.val = params.d := by omega
        rcases hu_end_shift with ⟨newStr_e, hm_e⟩
        refine ⟨u_end, ha'2, le_rfl,
          ⟨i, newStr_e, by rw [List.getElem?_eq_getElem hu_end_len, hm_e]⟩,
          fun i' => ?_, fun i' hi' => ?_⟩
        · have hi'_le : i' ≤ i := Fin.le_iff_val_le_val.mpr (by
            have := i'.isLt; omega)
          rcases lt_or_eq_of_le hi'_le with hlt | rfl
          · have hx_lt := (hrepT_const u_end ha'2 le_rfl).2 i' hlt
            rw [hx_lt.2]
            exact hP i' hlt
          · have hphi_x := hphi_const u_end ha'2 le_rfl
            have hbran_x : (stateAt W params.hk initStr moves u_end).bran i' = jStar := by
              ext
              rw [bran_val_eq_levelPhi_mod, hphi_x]
              dsimp only [target]
              rw [Nat.mul_comm _ params.k, Nat.mul_add_mod, Nat.mod_eq_of_lt jStar.isLt]
            have hstr_x := (hconst_s u_end ha'2 (by omega)).1
            rw [hbran_x, hstr_x, hstr_a']
            exact hjStar
        · exfalso
          have := Fin.lt_def.mp hi'
          have := i'.isLt
          omega
    rcases hex with ⟨x, hxa', hxu, ⟨i₀, newStr_x, hm_x?⟩, hx_str, hx_passes⟩
    have hx_le_s : x ≤ s := le_trans hxu hu_end_le
    have hx_len : x < moves.length := lt_of_le_of_lt hx_le_s hs
    have hm_x : moves[x] = .roundStep .roundContinuing (.shift i₀) newStr_x := by
      rw [List.getElem?_eq_getElem hx_len] at hm_x?
      exact Option.some.inj hm_x?
    have hloss : LossSumCond W (stateAt W params.hk initStr moves x) := by
      have hstep_x := hv.2 x hx_len
      dsimp only [ValidStep] at hstep_x
      have hph_x : (stateAt W params.hk initStr moves x).phase = .stage34 := by
        cases h : (stateAt W params.hk initStr moves x).phase
        · rw [h, hm_x] at hstep_x
          exact False.elim hstep_x.2
        · rfl
      rw [hph_x, hm_x] at hstep_x
      rcases hstep_x.1 rfl with hloss | hbad
      · exact hloss
      · exfalso
        rcases hbad with ⟨i', hgt⟩
        exact absurd hgt (not_lt.mpr (hx_str i'))
    -- Pick the smallest level `iStar` maximizing `W ((stateAt x).repT _)`.
    let stx := stateAt W params.hk initStr moves x
    let vals : Finset ℝ := Finset.univ.image (fun a : Fin (params.d + 1) => W (stx.repT a))
    have hvals_ne : vals.Nonempty := ⟨W (stx.repT 0), Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
    let Mval := vals.max' hvals_ne
    have hex_max : ∃ a : Fin (params.d + 1), W (stx.repT a) = Mval := by
      have hm := Finset.max'_mem vals hvals_ne
      rcases Finset.mem_image.mp hm with ⟨a, _, ha⟩
      exact ⟨a, ha⟩
    have hle_Mval : ∀ a : Fin (params.d + 1), W (stx.repT a) ≤ Mval := fun a =>
      Finset.le_max' vals _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
    let goodIdx := Finset.univ.filter (fun a : Fin (params.d + 1) => W (stx.repT a) = Mval)
    have hgood_ne : goodIdx.Nonempty := by
      rcases hex_max with ⟨a, ha⟩
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
    let iStar := goodIdx.min' hgood_ne
    have hiStar_mem := Finset.mem_filter.mp (Finset.min'_mem goodIdx hgood_ne)
    have hiStar_eq : W (stx.repT iStar) = Mval := hiStar_mem.2
    have hiStar_in_M : iStar ∈ PrefixMaxSet W stx := by
      intro a ha
      have hle := hle_Mval a
      have hne : W (stx.repT a) ≠ Mval := by
        intro heq
        have ha_mem : a ∈ goodIdx := Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
        have := Finset.min'_le goodIdx a ha_mem
        exact absurd ha (not_lt.mpr this)
      rw [hiStar_eq]
      exact lt_of_le_of_ne hle hne
    have hiStar_in_P : iStar ∈ PrefixGoodStretchSet params.σ stx := fun a _ => hx_str a
    have hsum_le : ∑ a : Fin (params.d + 1), W (stx.repT a) ≤
        ((params.d : ℝ) + 1) * W (stx.repT iStar) := by
      calc
        ∑ a : Fin (params.d + 1), W (stx.repT a)
          ≤ ∑ _a : Fin (params.d + 1), W (stx.repT iStar) := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [hiStar_eq]; exact hle_Mval a
        _ = ((params.d : ℝ) + 1) * W (stx.repT iStar) := by
            simp [Finset.sum_const, nsmul_eq_mul]
    have hW_gt : 2 * W stx.round < W (stx.repT iStar) := by
      dsimp [LossSumCond] at hloss
      have hdpos : (0 : ℝ) < (params.d : ℝ) + 1 := by positivity
      have hmul : ((params.d : ℝ) + 1) * (2 * W stx.round) <
          ((params.d : ℝ) + 1) * W (stx.repT iStar) := by
        calc
          ((params.d : ℝ) + 1) * (2 * W stx.round)
            = 2 * ((params.d : ℝ) + 1) * W stx.round := by ring
          _ < ∑ a : Fin (params.d + 1), W (stx.repT a) := hloss
          _ ≤ ((params.d : ℝ) + 1) * W (stx.repT iStar) := hsum_le
      exact (mul_lt_mul_iff_right₀ hdpos).mp hmul
    have hiStar_not_lt : ¬ iStar < i := by
      intro hlt
      have hMa := hM iStar hlt
      have h1 := (hrepT_const x hxa' hxu).2 iStar hlt
      have h2 := (hrepT_const x hxa' hxu).1
      have hle := hle_Mval i
      rw [← hiStar_eq] at hle
      dsimp [stx] at hle
      rw [h1.1, h2] at hle
      linarith only [hMa, hle]
    have hiStar_not_gt : ¬ i < iStar := by
      intro hgt
      have hih_x := hih_all x hx_le_s iStar hiStar_in_M hiStar_in_P
      have hpx := hx_passes iStar hgt
      have hmne : moves ≠ [] := List.ne_nil_of_length_pos (Nat.zero_lt_of_lt hs)
      have hwr := weightValid_round_of_lt hv hx_len
      have h2Psi : 2 * params.Ψ - 1 ≤ (passesAt W params.hk initStr moves x iStar : ℝ) := by
        have hceil : 2 * params.Ψ ≤ (P : ℝ) := Nat.le_ceil _
        have hP1 : (1 : ℝ) ≤ (P : ℝ) := by linarith only [params.hΨ, hceil]
        have hP_pos : 1 ≤ P := by exact_mod_cast hP1
        have hcast : ((P - 1 : ℕ) : ℝ) = (P : ℝ) - 1 := by
          rw [Nat.cast_sub hP_pos, Nat.cast_one]
        rw [hpx, hcast]
        linarith only [hceil]
      have hlog_mul : Real.logb 2 (2 * W stx.round) = 1 + Real.logb 2 (W stx.round) := by
        rw [Real.logb_mul (by norm_num) (ne_of_gt hwr.1), Real.logb_self_eq_one (by norm_num)]
      have hlog_lt := Real.logb_lt_logb (b := 2) (by norm_num) (by linarith only [hwr.1]) hW_gt
      rw [hlog_mul] at hlog_lt
      dsimp [stx] at hlog_lt hih_x
      linarith only [hlog_lt, hih_x, h2Psi, hwr.2.1]
    have hiStar_eq_i : iStar = i := le_antisymm (not_lt.mp hiStar_not_gt) (not_lt.mp hiStar_not_lt)
    subst hiStar_eq_i
    have hrep_xs : stx.repT iStar = (stateAt W params.hk initStr moves s).repT iStar :=
      (hrepT_const x hxa' hxu).1
    have hW_i_gt : 2 * W stx.round < W ((stateAt W params.hk initStr moves s).repT iStar) := by
      rw [← hrep_xs]; exact hW_gt
    have hrep_le_round : (stateAt W params.hk initStr moves s).repT iStar ≤ stx.round := by
      rw [← hrep_xs]; exact (repT_bounds W params.hk initStr moves x iStar).2
    have hround_le : stx.round ≤ (stateAt W params.hk initStr moves s).round :=
      round_mono W params.hk initStr moves hx_le_s
    have hmin_le : W ((stateAt W params.hk initStr moves (s + 1)).repT iStar) ≤ W stx.round := by
      rw [hrep_succ]
      exact argminRound_le W hrep_le_round hround_le
    have hmne : moves ≠ [] := List.ne_nil_of_length_pos (Nat.zero_lt_of_lt hs)
    have hwr_s1 := weightValid_repT hv hmne (Nat.succ_le_of_lt hs) iStar
    have hwr_x := weightValid_round_of_lt hv hx_len
    have hW_half : W ((stateAt W params.hk initStr moves (s + 1)).repT iStar) <
        (1 / 2 : ℝ) * W ((stateAt W params.hk initStr moves s).repT iStar) := by
      linarith only [hmin_le, hW_i_gt]
    have hlog_step : Real.logb 2 (W ((stateAt W params.hk initStr moves (s + 1)).repT iStar)) <
        Real.logb 2 (W ((stateAt W params.hk initStr moves s).repT iStar)) - 1 := by
      have hlt' := Real.logb_lt_logb (b := 2) (by norm_num) hwr_s1.1 hW_half
      have hdiv : Real.logb 2 ((1 / 2 : ℝ) * W ((stateAt W params.hk initStr moves s).repT iStar)) =
          Real.logb 2 (W ((stateAt W params.hk initStr moves s).repT iStar)) - 1 := by
        rw [show (1 / 2 : ℝ) * W ((stateAt W params.hk initStr moves s).repT iStar) =
          W ((stateAt W params.hk initStr moves s).repT iStar) / 2 by ring]
        rw [Real.logb_div (by linarith only [hwr_x.1, hW_i_gt]) (by norm_num),
          Real.logb_self_eq_one (by norm_num)]
      linarith only [hlt', hdiv]
    have hih_s := hih_all s le_rfl iStar hM hP
    rw [hps_succ, Nat.cast_add, Nat.cast_one]
    linarith only [hlog_step, hih_s]
  · -- Non-wrapping branch: `repT_i` and `passes_i` stay unchanged.
    have hnw := htr.2.2.2.1 hwrap
    rw [stateAt_succ W params.hk initStr moves hs, passesAt_succ W params.hk initStr moves hs, hm]
    rw [hnw.1, hnw.2.2]
    exact hih_all s le_rfl i hM hP

/-- **Event 3** (pages 37–38): if `GameIH` holds for all steps `≤ s` and the player chooses
`shift-step(i)` at step `s` under Algorithm 3, then `GameIH` holds at step `s + 1`. -/
theorem event_3 (params : GameParams) {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    (hv : ValidPlayPrefix params W initStr moves)
    (hf : FollowsStrategyPrefix params W initStr moves)
    {s : ℕ} (hs : s < moves.length)
    (hih_all : ∀ t ≤ s, GameIH params W (stateAt W params.hk initStr moves t)
      (passesAt W params.hk initStr moves t))
    {i : Fin (params.d + 1)} {adv : RoundChoice} {newStr : Fin (params.d + 1) → Fin params.k → ℝ}
    (hm : moves[s] = .roundStep adv (.shift i) newStr) :
    GameIH params W (stateAt W params.hk initStr moves (s + 1))
      (passesAt W params.hk initStr moves (s + 1)) := by
  intro i' hM hP
  by_cases heq : i' = i
  · subst heq
    by_cases hM_s : i' ∈ PrefixMaxSet W (stateAt W params.hk initStr moves s)
    · by_cases hP_s : i' ∈ PrefixGoodStretchSet params.σ (stateAt W params.hk initStr moves s)
      · exact case_C params hv hf hs hih_all hm hM_s hP_s hM hP
      · exact case_B params hs hm hP_s hM hP
    · exact case_A params hs hm hM_s hM hP
  · exact claim_7_9 params hv hs (hih_all s le_rfl) hm i' heq hM hP

/-- The induction hypothesis (16) (`GameIH`, page 37) holds at every step `s ≤ moves.length`
when the player follows Algorithm 3 (`FollowsStrategyPrefix`) on a nonempty valid prefix. -/
theorem gameIH_holds (params : GameParams) {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    (hv : ValidPlayPrefix params W initStr moves)
    (hf : FollowsStrategyPrefix params W initStr moves)
    (hmne : moves ≠ []) :
    ∀ s ≤ moves.length, GameIH params W (stateAt W params.hk initStr moves s)
      (passesAt W params.hk initStr moves s) := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro hs_len
    cases s with
    | zero =>
      intro i _ _
      have hwv := weightValid_repT hv hmne (Nat.zero_le _) i
      rw [passesAt_zero, Nat.cast_zero, sub_zero]
      exact hwv.2.2
    | succ s =>
      have hs : s < moves.length := Nat.lt_of_succ_le hs_len
      have hih_all : ∀ t ≤ s, GameIH params W (stateAt W params.hk initStr moves t)
          (passesAt W params.hk initStr moves t) :=
        fun t ht => ih t (Nat.lt_succ_of_le ht) (le_trans ht (le_of_lt hs))
      cases hm : moves[s] with
      | advDoNothing =>
        exact event_2 params hs (hih_all s le_rfl) (Or.inl hm)
      | advRebuild i newStr =>
        exact event_1 params hv hs (hih_all s le_rfl) hm
      | roundStep adv player newStr =>
        cases player with
        | doNothing =>
          exact event_2 params hs (hih_all s le_rfl) (Or.inr ⟨adv, newStr, hm⟩)
        | shift i =>
          exact event_3 params hv hf hs hih_all hm

/-- Corollary of `gameIH_holds` (page 37): at every step `s ≤ moves.length`, level `0` has
`passes_0 < 2Ψ`. -/
theorem passes_zero_lt (params : GameParams) {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    (hv : ValidPlayPrefix params W initStr moves)
    (hf : FollowsStrategyPrefix params W initStr moves)
    (hmne : moves ≠ []) {s : ℕ} (hs : s ≤ moves.length) :
    (passesAt W params.hk initStr moves s 0 : ℝ) < 2 * params.Ψ := by
  have hih := gameIH_holds params hv hf hmne s hs 0
    (zero_mem_prefixMaxSet W _) (zero_mem_prefixGoodStretchSet params.σ _)
  have hwv := weightValid_repT hv hmne hs 0
  linarith only [hwv.2.1, hih]

/-- Well-definedness of **Algorithm 3** (page 34): at every step `s ≤ moves.length` of a
nonempty valid play following Algorithm 3, there exists a largest eligible level `i` with
`passes_i < 2Ψ`. -/
theorem strategy_next_level_exists (params : GameParams) {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    (hv : ValidPlayPrefix params W initStr moves)
    (hf : FollowsStrategyPrefix params W initStr moves)
    (hmne : moves ≠ []) {s : ℕ} (hs : s ≤ moves.length) :
    ∃ i : Fin (params.d + 1),
      (passesAt W params.hk initStr moves s i : ℝ) < 2 * params.Ψ ∧
      ∀ j : Fin (params.d + 1), (passesAt W params.hk initStr moves s j : ℝ) < 2 * params.Ψ →
        j ≤ i := by
  classical
  let elig : Finset (Fin (params.d + 1)) :=
    Finset.univ.filter fun j => (passesAt W params.hk initStr moves s j : ℝ) < 2 * params.Ψ
  have h0_mem : (0 : Fin (params.d + 1)) ∈ elig :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, passes_zero_lt params hv hf hmne hs⟩
  have hne : elig.Nonempty := ⟨0, h0_mem⟩
  refine ⟨elig.max' hne, (Finset.mem_filter.mp (elig.max'_mem hne)).2, fun j hj => ?_⟩
  exact Finset.le_max' elig j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)

private lemma list_take_succ_eq {α : Type*} (xs : List α) {s : ℕ} (hs : s < xs.length) :
    xs.take (s + 1) = xs.take s ++ [xs[s]] := by
  induction xs generalizing s with
  | nil => simp at hs
  | cons x xs ih =>
    cases s with
    | zero => simp
    | succ s =>
      simp only [List.take_succ_cons, List.getElem_cons_succ, List.cons_append]
      exact congrArg (x :: ·) (ih (by simp at hs; omega))

private lemma levelPhi_le_ceil_mul_k (params : GameParams) {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    (hv : ValidPlayPrefix params W initStr moves)
    (hf : FollowsStrategyPrefix params W initStr moves) :
    ∀ s ≤ moves.length, ∀ i : Fin (params.d + 1),
      levelPhi W params.hk initStr moves i s ≤ Nat.ceil (2 * params.Ψ) * params.k := by
  intro s
  induction s with
  | zero =>
    intro _ i
    rw [levelPhi_zero]
    exact Nat.zero_le _
  | succ s ih =>
    intro hs_len i
    have hs : s < moves.length := Nat.lt_of_succ_le hs_len
    have hih := ih (le_of_lt hs) i
    have hcases := levelPhi_step_cases W params.hk initStr moves i hs
    cases hm : moves[s] with
    | advDoNothing =>
      have hp : PreservesUpTo i moves[s] := by rw [hm]; exact preservesUpTo_advDoNothing i
      rw [hcases.2.2.2 hp]
      exact hih
    | advRebuild i₀ newStr =>
      by_cases hle : i₀ ≤ i
      · rw [hcases.1 i₀ newStr hm hle]
        exact Nat.zero_le _
      · have hp : PreservesUpTo i moves[s] := by
          rw [hm]; exact preservesUpTo_advRebuild_gt (not_le.mp hle) newStr
        rw [hcases.2.2.2 hp]
        exact hih
    | roundStep adv player newStr =>
      cases player with
      | doNothing =>
        have hp : PreservesUpTo i moves[s] := by
          rw [hm]; exact preservesUpTo_roundDoNothing i adv newStr
        rw [hcases.2.2.2 hp]
        exact hih
      | shift i₀ =>
        rcases lt_trichotomy i₀ i with hlt | rfl | hgt
        · rw [hcases.2.1 i₀ adv newStr hm hlt]
          exact Nat.zero_le _
        · rw [hcases.2.2.1 adv newStr hm]
          have hpass := (shift_step_strategy_props params hv hf hs hm).2.1
          have hbran : ((stateAt W params.hk initStr moves s).bran i₀).val < params.k :=
            ((stateAt W params.hk initStr moves s).bran i₀).isLt
          have hphi_lt : levelPhi W params.hk initStr moves i₀ s + 1 ≤
              (passesAt W params.hk initStr moves s i₀ + 1) * params.k := by
            unfold levelPhi
            rw [Nat.add_mul, Nat.one_mul]
            omega
          exact le_trans hphi_lt (Nat.mul_le_mul_right params.k hpass)
        · have hp : PreservesUpTo i moves[s] := by
            rw [hm]; exact preservesUpTo_shift_gt hgt adv newStr
          rw [hcases.2.2.2 hp]
          exact hih

private lemma shiftCount_take_bound (params : GameParams) {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    (hv : ValidPlayPrefix params W initStr moves)
    (hf : FollowsStrategyPrefix params W initStr moves) :
    ∀ s ≤ moves.length, ∀ i : Fin (params.d + 1),
      shiftCount (moves.take s) i ≤
        levelPhi W params.hk initStr moves i s +
          Nat.ceil (2 * params.Ψ) * params.k *
            (∑ i' ∈ Finset.Iic i, rebuildCount (moves.take s) i' +
              ∑ i' ∈ Finset.Iio i, shiftCount (moves.take s) i') := by
  intro s
  induction s with
  | zero =>
    intro _ i
    simp [shiftCount_nil]
  | succ s ih =>
    intro hs_len i
    have hs : s < moves.length := Nat.lt_of_succ_le hs_len
    have hih := ih (le_of_lt hs) i
    have hphi_le := levelPhi_le_ceil_mul_k params hv hf s (le_of_lt hs) i
    have htake : moves.take (s + 1) = moves.take s ++ [moves[s]] :=
      list_take_succ_eq moves hs
    have hsc_eq : ∀ j, shiftCount (moves.take (s + 1)) j =
        shiftCount (moves.take s) j + shiftCount [moves[s]] j := fun j => by
      rw [htake, shiftCount_append]
    have hrc_eq : ∀ j, rebuildCount (moves.take (s + 1)) j =
        rebuildCount (moves.take s) j + rebuildCount [moves[s]] j := fun j => by
      rw [htake, rebuildCount_append]
    have hR_mono :
        ∑ i' ∈ Finset.Iic i, rebuildCount (moves.take s) i' +
          ∑ i' ∈ Finset.Iio i, shiftCount (moves.take s) i' ≤
        ∑ i' ∈ Finset.Iic i, rebuildCount (moves.take (s + 1)) i' +
          ∑ i' ∈ Finset.Iio i, shiftCount (moves.take (s + 1)) i' := by
      refine Nat.add_le_add ?_ ?_ <;> refine Finset.sum_le_sum fun j _ => ?_
      · rw [hrc_eq]; exact Nat.le_add_right _ _
      · rw [hsc_eq]; exact Nat.le_add_right _ _
    have hcases := levelPhi_step_cases W params.hk initStr moves i hs
    cases hm : moves[s] with
    | advDoNothing =>
      have hsc_i : shiftCount (moves.take (s + 1)) i = shiftCount (moves.take s) i := by
        simp [hsc_eq, hm, shiftCount_cons, shiftCount_nil]
      have hp : PreservesUpTo i moves[s] := by rw [hm]; exact preservesUpTo_advDoNothing i
      rw [hsc_i, hcases.2.2.2 hp]
      exact le_trans hih (Nat.add_le_add_left (Nat.mul_le_mul_left _ hR_mono) _)
    | advRebuild i₀ newStr =>
      have hsc_i : shiftCount (moves.take (s + 1)) i = shiftCount (moves.take s) i := by
        simp [hsc_eq, hm, shiftCount_cons, shiftCount_nil]
      rw [hsc_i]
      by_cases hle : i₀ ≤ i
      · have hrc_sum :
            ∑ i' ∈ Finset.Iic i, rebuildCount (moves.take (s + 1)) i' =
              ∑ i' ∈ Finset.Iic i, rebuildCount (moves.take s) i' + 1 := by
          have hadd :
              ∑ i' ∈ Finset.Iic i, rebuildCount (moves.take (s + 1)) i' =
                ∑ i' ∈ Finset.Iic i, rebuildCount (moves.take s) i' +
                  ∑ i' ∈ Finset.Iic i, rebuildCount [moves[s]] i' := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun j _ => hrc_eq j
          have hsingle : ∑ i' ∈ Finset.Iic i, rebuildCount [moves[s]] i' = 1 := by
            rw [Finset.sum_eq_single i₀]
            · simp [hm, rebuildCount_cons, rebuildCount_nil]
            · intro j _ hne
              simp [hm, rebuildCount_cons, rebuildCount_nil, hne.symm]
            · intro hmem
              exact absurd (Finset.mem_Iic.mpr hle) hmem
          rw [hadd, hsingle]
        have hsc_sum :
            ∑ i' ∈ Finset.Iio i, shiftCount (moves.take (s + 1)) i' =
              ∑ i' ∈ Finset.Iio i, shiftCount (moves.take s) i' := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp [hsc_eq, hm, shiftCount_cons, shiftCount_nil]
        rw [hcases.1 i₀ newStr hm hle, Nat.zero_add, hrc_sum, hsc_sum]
        have hbound : levelPhi W params.hk initStr moves i s +
            Nat.ceil (2 * params.Ψ) * params.k *
              (∑ i' ∈ Finset.Iic i, rebuildCount (moves.take s) i' +
                ∑ i' ∈ Finset.Iio i, shiftCount (moves.take s) i') ≤
            Nat.ceil (2 * params.Ψ) * params.k *
              (∑ i' ∈ Finset.Iic i, rebuildCount (moves.take s) i' + 1 +
                ∑ i' ∈ Finset.Iio i, shiftCount (moves.take s) i') := by
          calc
            levelPhi W params.hk initStr moves i s +
                Nat.ceil (2 * params.Ψ) * params.k *
                  (∑ i' ∈ Finset.Iic i, rebuildCount (moves.take s) i' +
                    ∑ i' ∈ Finset.Iio i, shiftCount (moves.take s) i')
              ≤ Nat.ceil (2 * params.Ψ) * params.k +
                  Nat.ceil (2 * params.Ψ) * params.k *
                    (∑ i' ∈ Finset.Iic i, rebuildCount (moves.take s) i' +
                      ∑ i' ∈ Finset.Iio i, shiftCount (moves.take s) i') :=
                Nat.add_le_add_right hphi_le _
            _ = Nat.ceil (2 * params.Ψ) * params.k *
                  (∑ i' ∈ Finset.Iic i, rebuildCount (moves.take s) i' + 1 +
                    ∑ i' ∈ Finset.Iio i, shiftCount (moves.take s) i') := by
                ring
        exact le_trans hih hbound
      · have hp : PreservesUpTo i moves[s] := by
          rw [hm]; exact preservesUpTo_advRebuild_gt (not_le.mp hle) newStr
        rw [hcases.2.2.2 hp]
        exact le_trans hih (Nat.add_le_add_left (Nat.mul_le_mul_left _ hR_mono) _)
    | roundStep adv player newStr =>
      cases player with
      | doNothing =>
        have hsc_i : shiftCount (moves.take (s + 1)) i = shiftCount (moves.take s) i := by
          simp [hsc_eq, hm, shiftCount_cons, shiftCount_nil]
        have hp : PreservesUpTo i moves[s] := by
          rw [hm]; exact preservesUpTo_roundDoNothing i adv newStr
        rw [hsc_i, hcases.2.2.2 hp]
        exact le_trans hih (Nat.add_le_add_left (Nat.mul_le_mul_left _ hR_mono) _)
      | shift i₀ =>
        rcases lt_trichotomy i₀ i with hlt | rfl | hgt
        · have hsc_i : shiftCount (moves.take (s + 1)) i = shiftCount (moves.take s) i := by
            simp [hsc_eq, hm, shiftCount_cons, shiftCount_nil, ne_of_lt hlt]
          have hrc_sum :
              ∑ i' ∈ Finset.Iic i, rebuildCount (moves.take (s + 1)) i' =
                ∑ i' ∈ Finset.Iic i, rebuildCount (moves.take s) i' := by
            refine Finset.sum_congr rfl fun j _ => ?_
            simp [hrc_eq, hm, rebuildCount_cons, rebuildCount_nil]
          have hsc_sum :
              ∑ i' ∈ Finset.Iio i, shiftCount (moves.take (s + 1)) i' =
                ∑ i' ∈ Finset.Iio i, shiftCount (moves.take s) i' + 1 := by
            have hadd :
                ∑ i' ∈ Finset.Iio i, shiftCount (moves.take (s + 1)) i' =
                  ∑ i' ∈ Finset.Iio i, shiftCount (moves.take s) i' +
                    ∑ i' ∈ Finset.Iio i, shiftCount [moves[s]] i' := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun j _ => hsc_eq j
            have hsingle : ∑ i' ∈ Finset.Iio i, shiftCount [moves[s]] i' = 1 := by
              rw [Finset.sum_eq_single i₀]
              · simp [hm, shiftCount_cons, shiftCount_nil]
              · intro j _ hne
                simp [hm, shiftCount_cons, shiftCount_nil, hne.symm]
              · intro hmem
                exact absurd (Finset.mem_Iio.mpr hlt) hmem
            rw [hadd, hsingle]
          rw [hsc_i, hcases.2.1 i₀ adv newStr hm hlt, Nat.zero_add, hrc_sum, hsc_sum]
          have hbound : levelPhi W params.hk initStr moves i s +
              Nat.ceil (2 * params.Ψ) * params.k *
                (∑ i' ∈ Finset.Iic i, rebuildCount (moves.take s) i' +
                  ∑ i' ∈ Finset.Iio i, shiftCount (moves.take s) i') ≤
              Nat.ceil (2 * params.Ψ) * params.k *
                (∑ i' ∈ Finset.Iic i, rebuildCount (moves.take s) i' +
                  (∑ i' ∈ Finset.Iio i, shiftCount (moves.take s) i' + 1)) := by
            calc
              levelPhi W params.hk initStr moves i s +
                  Nat.ceil (2 * params.Ψ) * params.k *
                    (∑ i' ∈ Finset.Iic i, rebuildCount (moves.take s) i' +
                      ∑ i' ∈ Finset.Iio i, shiftCount (moves.take s) i')
                ≤ Nat.ceil (2 * params.Ψ) * params.k +
                    Nat.ceil (2 * params.Ψ) * params.k *
                      (∑ i' ∈ Finset.Iic i, rebuildCount (moves.take s) i' +
                        ∑ i' ∈ Finset.Iio i, shiftCount (moves.take s) i') :=
                  Nat.add_le_add_right hphi_le _
              _ = Nat.ceil (2 * params.Ψ) * params.k *
                    (∑ i' ∈ Finset.Iic i, rebuildCount (moves.take s) i' +
                      (∑ i' ∈ Finset.Iio i, shiftCount (moves.take s) i' + 1)) := by
                  ring
          exact le_trans hih hbound
        · have hsc_i : shiftCount (moves.take (s + 1)) i₀ = shiftCount (moves.take s) i₀ + 1 := by
            simp [hsc_eq, hm, shiftCount_cons, shiftCount_nil]
          rw [hsc_i, hcases.2.2.1 adv newStr hm]
          have hih' := Nat.add_le_add_right hih 1
          have hrhs :
              levelPhi W params.hk initStr moves i₀ s +
                  Nat.ceil (2 * params.Ψ) * params.k *
                    (∑ i' ∈ Finset.Iic i₀, rebuildCount (moves.take s) i' +
                      ∑ i' ∈ Finset.Iio i₀, shiftCount (moves.take s) i') + 1 ≤
              levelPhi W params.hk initStr moves i₀ s + 1 +
                  Nat.ceil (2 * params.Ψ) * params.k *
                    (∑ i' ∈ Finset.Iic i₀, rebuildCount (moves.take (s + 1)) i' +
                      ∑ i' ∈ Finset.Iio i₀, shiftCount (moves.take (s + 1)) i') := by
            calc
              levelPhi W params.hk initStr moves i₀ s +
                  Nat.ceil (2 * params.Ψ) * params.k *
                    (∑ i' ∈ Finset.Iic i₀, rebuildCount (moves.take s) i' +
                      ∑ i' ∈ Finset.Iio i₀, shiftCount (moves.take s) i') + 1
                = levelPhi W params.hk initStr moves i₀ s + 1 +
                    Nat.ceil (2 * params.Ψ) * params.k *
                      (∑ i' ∈ Finset.Iic i₀, rebuildCount (moves.take s) i' +
                        ∑ i' ∈ Finset.Iio i₀, shiftCount (moves.take s) i') := by ring
              _ ≤ levelPhi W params.hk initStr moves i₀ s + 1 +
                    Nat.ceil (2 * params.Ψ) * params.k *
                      (∑ i' ∈ Finset.Iic i₀, rebuildCount (moves.take (s + 1)) i' +
                        ∑ i' ∈ Finset.Iio i₀, shiftCount (moves.take (s + 1)) i') :=
                Nat.add_le_add_left (Nat.mul_le_mul_left _ hR_mono) _
          exact le_trans hih' hrhs
        · have hsc_i : shiftCount (moves.take (s + 1)) i = shiftCount (moves.take s) i := by
            simp [hsc_eq, hm, shiftCount_cons, shiftCount_nil, ne_of_gt hgt]
          have hp : PreservesUpTo i moves[s] := by
            rw [hm]; exact preservesUpTo_shift_gt hgt adv newStr
          rw [hsc_i, hcases.2.2.2 hp]
          exact le_trans hih (Nat.add_le_add_left (Nat.mul_le_mul_left _ hR_mono) _)

private lemma geom_sum_le_two_mul_pow (M : ℝ) (hM : 2 ≤ M) :
    ∀ n : ℕ, ∑ t ∈ Finset.range (n + 1), M ^ t ≤ 2 * M ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := geom_sum_le_two_mul_pow M hM n
    have hM0 : 0 ≤ M := by linarith only [hM]
    have hMn : 0 ≤ M ^ n := pow_nonneg hM0 n
    have hmul : 2 * M ^ n ≤ M * M ^ n := mul_le_mul_of_nonneg_right hM hMn
    rw [Finset.sum_range_succ]
    calc
      ∑ t ∈ Finset.range (n + 1), M ^ t + M ^ (n + 1)
        ≤ 2 * M ^ n + M ^ (n + 1) := by linarith only [ih]
      _ ≤ M * M ^ n + M ^ (n + 1) := by linarith only [hmul]
      _ = 2 * M ^ (n + 1) := by rw [← pow_succ']; ring

private lemma lemma_7_3_level_bound (d : ℕ) (M C : ℝ) (hM : 2 ≤ M) (hC0 : 0 ≤ C)
    (h2CM : 2 * C ≤ M) (s r : Fin (d + 1) → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hstep : ∀ i : Fin (d + 1),
      s i ≤ C * (1 + ∑ j ∈ Finset.Iic i, r j + ∑ i' ∈ Finset.Iio i, s i')) :
    ∀ n ≤ d, ∀ i : Fin (d + 1), i.val = n →
      s i ≤ M ^ (i.val + 1) + ∑ j ∈ Finset.Iic i, r j * M ^ (i.val + 1 - j.val) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn i hin
    have hM0 : 0 ≤ M := by linarith only [hM]
    have hsi := hstep i
    have hs_prev : ∑ i' ∈ Finset.Iio i, s i' ≤
        ∑ i' ∈ Finset.Iio i, (M ^ (i'.val + 1) +
          ∑ j ∈ Finset.Iic i', r j * M ^ (i'.val + 1 - j.val)) := by
      refine Finset.sum_le_sum fun i' hi' => ?_
      have hlt : i'.val < i.val := Fin.lt_def.mp (Finset.mem_Iio.mp hi')
      exact ih i'.val (by omega) (by omega) i' rfl
    have hinit_sum : 1 + ∑ i' ∈ Finset.Iio i, M ^ (i'.val + 1) ≤ 2 * M ^ i.val := by
      have hrange : ∑ i' ∈ Finset.Iio i, M ^ (i'.val + 1) =
          ∑ t ∈ Finset.range i.val, M ^ (t + 1) := by
        refine Finset.sum_bij (fun i' _ => i'.val) ?_ ?_ ?_ ?_
        · intro a ha
          exact Finset.mem_range.mpr (Fin.lt_def.mp (Finset.mem_Iio.mp ha))
        · intro a _ b _ hab
          ext; exact hab
        · intro b hb
          have hlt := Finset.mem_range.mp hb
          exact ⟨⟨b, lt_trans hlt i.isLt⟩, Finset.mem_Iio.mpr hlt, rfl⟩
        · intro _ _; rfl
      rw [hrange]
      have hsplit : 1 + ∑ t ∈ Finset.range i.val, M ^ (t + 1) =
          ∑ t ∈ Finset.range (i.val + 1), M ^ t := by
        rw [Finset.sum_range_succ', pow_zero, add_comm]
      rw [hsplit]
      exact geom_sum_le_two_mul_pow M hM i.val
    have hswap :
        ∑ i' ∈ Finset.Iio i, ∑ j ∈ Finset.Iic i', r j * M ^ (i'.val + 1 - j.val) =
          ∑ j ∈ Finset.Iic i, r j * ∑ i' ∈ Finset.Ico j i, M ^ (i'.val + 1 - j.val) := by
      have hL : (∑ i' ∈ Finset.Iio i, ∑ j ∈ Finset.Iic i', r j * M ^ (i'.val + 1 - j.val)) =
          ∑ i' : Fin (d + 1), ∑ j : Fin (d + 1),
            if i' < i ∧ j ≤ i' then r j * M ^ (i'.val + 1 - j.val) else 0 := by
        have hiio : Finset.Iio i = Finset.univ.filter (· < i) := by ext; simp
        have hiic : ∀ i' : Fin (d + 1), Finset.Iic i' = Finset.univ.filter (· ≤ i') := fun i' => by
          ext; simp
        rw [hiio, Finset.sum_filter]
        refine Finset.sum_congr rfl fun i' _ => ?_
        by_cases h1 : i' < i
        · simp [h1, hiic i', Finset.sum_filter]
        · simp only [h1, ite_false]
          symm
          refine Finset.sum_eq_zero fun j _ => by simp only [false_and, ite_false]
      have hR : (∑ j ∈ Finset.Iic i, r j * ∑ i' ∈ Finset.Ico j i, M ^ (i'.val + 1 - j.val)) =
          ∑ j : Fin (d + 1), ∑ i' : Fin (d + 1),
            if j ≤ i' ∧ i' < i then r j * M ^ (i'.val + 1 - j.val) else 0 := by
        have hiic : Finset.Iic i = Finset.univ.filter (· ≤ i) := by ext; simp
        have hico : ∀ j : Fin (d + 1),
            Finset.Ico j i = Finset.univ.filter (fun i' => j ≤ i' ∧ i' < i) := fun j => by
          ext; simp
        rw [hiic, Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h1 : j ≤ i
        · simp only [h1, ite_true]
          rw [Finset.mul_sum, hico j, Finset.sum_filter]
        · simp only [h1, ite_false]
          symm
          refine Finset.sum_eq_zero fun i' _ => by
            have hnot : ¬ (j ≤ i' ∧ i' < i) := fun ⟨hle, hlt⟩ =>
              h1 (le_trans hle (le_of_lt hlt))
            simp only [hnot, ite_false]
      rw [hL, hR, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i' _ => ?_
      simp only [and_comm]
    have hr_bound :
        ∑ j ∈ Finset.Iic i, r j +
            ∑ i' ∈ Finset.Iio i, ∑ j ∈ Finset.Iic i', r j * M ^ (i'.val + 1 - j.val) ≤
          ∑ j ∈ Finset.Iic i, r j * (2 * M ^ (i.val - j.val)) := by
      rw [hswap, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun j hj => ?_
      have hj_le : j ≤ i := Finset.mem_Iic.mp hj
      have hcoeff : 1 + ∑ i' ∈ Finset.Ico j i, M ^ (i'.val + 1 - j.val) ≤
          2 * M ^ (i.val - j.val) := by
        have hico : ∑ i' ∈ Finset.Ico j i, M ^ (i'.val + 1 - j.val) =
            ∑ t ∈ Finset.range (i.val - j.val), M ^ (t + 1) := by
          refine Finset.sum_bij (fun i' _ => i'.val - j.val) ?_ ?_ ?_ ?_
          · intro a ha
            rcases Finset.mem_Ico.mp ha with ⟨h1, h2⟩
            have h1v : j.val ≤ a.val := Fin.le_def.mp h1
            have h2v : a.val < i.val := Fin.lt_def.mp h2
            exact Finset.mem_range.mpr (by omega)
          · intro a ha b hb hab
            rcases Finset.mem_Ico.mp ha with ⟨ha1, _⟩
            rcases Finset.mem_Ico.mp hb with ⟨hb1, _⟩
            have ha1v : j.val ≤ a.val := Fin.le_def.mp ha1
            have hb1v : j.val ≤ b.val := Fin.le_def.mp hb1
            ext; omega
          · intro b hb
            have hbv := Finset.mem_range.mp hb
            have hi_lt : i.val < d + 1 := i.isLt
            have hjlt : j.val + b < d + 1 := by omega
            refine ⟨⟨j.val + b, hjlt⟩, Finset.mem_Ico.mpr ⟨Fin.le_def.mpr ?_,
              Fin.lt_def.mpr ?_⟩, ?_⟩
            · change j.val ≤ j.val + b; omega
            · change j.val + b < i.val; omega
            · change j.val + b - j.val = b; omega
          · intro a ha
            have ha1v : j.val ≤ a.val := Fin.le_def.mp (Finset.mem_Ico.mp ha).1
            exact congrArg (M ^ ·) (by omega)
        have hsum1 : 1 + ∑ t ∈ Finset.range (i.val - j.val), M ^ (t + 1) =
            ∑ t ∈ Finset.range (i.val - j.val + 1), M ^ t := by
          rw [Finset.sum_range_succ', pow_zero, add_comm]
        rw [hico, hsum1]
        exact geom_sum_le_two_mul_pow M hM (i.val - j.val)
      calc
        r j + r j * ∑ i' ∈ Finset.Ico j i, M ^ (i'.val + 1 - j.val)
          = r j * (1 + ∑ i' ∈ Finset.Ico j i, M ^ (i'.val + 1 - j.val)) := by ring
        _ ≤ r j * (2 * M ^ (i.val - j.val)) :=
          mul_le_mul_of_nonneg_left hcoeff (hr j)
    have hr_mul : C * (∑ j ∈ Finset.Iic i, r j * (2 * M ^ (i.val - j.val))) ≤
        ∑ j ∈ Finset.Iic i, r j * M ^ (i.val + 1 - j.val) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      have hj_le : j.val ≤ i.val := Fin.le_def.mp (Finset.mem_Iic.mp hj)
      have hpow_nonneg : 0 ≤ M ^ (i.val - j.val) := pow_nonneg hM0 _
      have hCM : 2 * C * M ^ (i.val - j.val) ≤ M * M ^ (i.val - j.val) :=
        mul_le_mul_of_nonneg_right h2CM hpow_nonneg
      have hpow_eq : M * M ^ (i.val - j.val) = M ^ (i.val + 1 - j.val) := by
        rw [← pow_succ']
        exact congrArg (M ^ ·) (by omega)
      have hterm : C * (r j * (2 * M ^ (i.val - j.val))) = r j * (2 * C * M ^ (i.val - j.val)) :=
        by ring
      rw [hterm, ← hpow_eq]
      exact mul_le_mul_of_nonneg_left hCM (hr j)
    have hinit_mul : C * (2 * M ^ i.val) ≤ M ^ (i.val + 1) := by
      have hMi : 0 ≤ M ^ i.val := pow_nonneg hM0 _
      have h1 : 2 * C * M ^ i.val ≤ M * M ^ i.val := mul_le_mul_of_nonneg_right h2CM hMi
      calc
        C * (2 * M ^ i.val) = 2 * C * M ^ i.val := by ring
        _ ≤ M * M ^ i.val := h1
        _ = M ^ (i.val + 1) := (pow_succ' M i.val).symm
    calc
      s i ≤ C * (1 + ∑ j ∈ Finset.Iic i, r j + ∑ i' ∈ Finset.Iio i, s i') := hsi
      _ ≤ C * (1 + ∑ j ∈ Finset.Iic i, r j +
            ∑ i' ∈ Finset.Iio i, (M ^ (i'.val + 1) +
              ∑ j ∈ Finset.Iic i', r j * M ^ (i'.val + 1 - j.val))) :=
          mul_le_mul_of_nonneg_left (by linarith only [hs_prev]) hC0
      _ = C * (1 + ∑ i' ∈ Finset.Iio i, M ^ (i'.val + 1)) +
            C * (∑ j ∈ Finset.Iic i, r j +
              ∑ i' ∈ Finset.Iio i, ∑ j ∈ Finset.Iic i', r j * M ^ (i'.val + 1 - j.val)) := by
          rw [Finset.sum_add_distrib]; ring
      _ ≤ C * (2 * M ^ i.val) +
            C * (∑ j ∈ Finset.Iic i, r j * (2 * M ^ (i.val - j.val))) :=
          add_le_add (mul_le_mul_of_nonneg_left hinit_sum hC0)
            (mul_le_mul_of_nonneg_left hr_bound hC0)
      _ ≤ M ^ (i.val + 1) + ∑ j ∈ Finset.Iic i, r j * M ^ (i.val + 1 - j.val) :=
          add_le_add hinit_mul hr_mul

/-- **Lemma 7.3** (page 35, prefix form, corrected for initial stretches):
for any valid prefix following Algorithm 3, the number of shift-steps at level `i` is bounded by
`(10Ψk)^{i+1} + ∑_{i' ≤ i} r_{i'} (10Ψk)^{i+1-i'}`. -/
theorem lemma_7_3_prefix (params : GameParams) {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    (hv : ValidPlayPrefix params W initStr moves)
    (hf : FollowsStrategyPrefix params W initStr moves)
    (i : Fin (params.d + 1)) :
    (shiftCount moves i : ℝ) ≤ (10 * params.Ψ * params.k) ^ (i.val + 1) +
      ∑ i' ∈ Finset.Iic i,
        (rebuildCount moves i' : ℝ) * (10 * params.Ψ * params.k) ^ (i.val + 1 - i'.val) := by
  let M : ℝ := 10 * params.Ψ * params.k
  let C : ℝ := (Nat.ceil (2 * params.Ψ) : ℝ) * params.k
  have hk1 : (1 : ℝ) ≤ params.k := Nat.one_le_cast.mpr params.hk
  have hΨk1 : 1 ≤ params.Ψ * params.k := one_le_mul_of_one_le_of_one_le params.hΨ hk1
  have hΨk0 : 0 ≤ params.Ψ * params.k := by linarith only [hΨk1]
  have hM2 : 2 ≤ M := by
    dsimp only [M]
    linarith only [hΨk1]
  have hceil : (Nat.ceil (2 * params.Ψ) : ℝ) < 2 * params.Ψ + 1 :=
    Nat.ceil_lt_add_one (by linarith only [params.hΨ])
  have hP_le : (Nat.ceil (2 * params.Ψ) : ℝ) ≤ 3 * params.Ψ := by linarith only [hceil, params.hΨ]
  have hC0 : 0 ≤ C := by positivity
  have h2CM : 2 * C ≤ M := by
    have hk0 : (0 : ℝ) ≤ params.k := Nat.cast_nonneg _
    have hC_le : C ≤ 3 * params.Ψ * params.k := by
      dsimp only [C]
      calc
        (Nat.ceil (2 * params.Ψ) : ℝ) * params.k
          ≤ (3 * params.Ψ) * params.k := mul_le_mul_of_nonneg_right hP_le hk0
        _ = 3 * params.Ψ * params.k := by ring
    dsimp only [M]
    linarith only [hC_le, hΨk0]
  have hstep : ∀ i₀ : Fin (params.d + 1),
      (shiftCount moves i₀ : ℝ) ≤ C * (1 + ∑ j ∈ Finset.Iic i₀, (rebuildCount moves j : ℝ) +
        ∑ i' ∈ Finset.Iio i₀, (shiftCount moves i' : ℝ)) := by
    intro i₀
    have hnat := shiftCount_take_bound params hv hf moves.length le_rfl i₀
    have hphi := levelPhi_le_ceil_mul_k params hv hf moves.length le_rfl i₀
    rw [List.take_length] at hnat
    have hnat' : shiftCount moves i₀ ≤ Nat.ceil (2 * params.Ψ) * params.k *
        (1 + ∑ j ∈ Finset.Iic i₀, rebuildCount moves j +
          ∑ i' ∈ Finset.Iio i₀, shiftCount moves i') := by
      calc
        shiftCount moves i₀
          ≤ levelPhi W params.hk initStr moves i₀ moves.length +
              Nat.ceil (2 * params.Ψ) * params.k *
                (∑ j ∈ Finset.Iic i₀, rebuildCount moves j +
                  ∑ i' ∈ Finset.Iio i₀, shiftCount moves i') := hnat
        _ ≤ Nat.ceil (2 * params.Ψ) * params.k +
              Nat.ceil (2 * params.Ψ) * params.k *
                (∑ j ∈ Finset.Iic i₀, rebuildCount moves j +
                  ∑ i' ∈ Finset.Iio i₀, shiftCount moves i') := Nat.add_le_add_right hphi _
        _ = Nat.ceil (2 * params.Ψ) * params.k *
              (1 + ∑ j ∈ Finset.Iic i₀, rebuildCount moves j +
                ∑ i' ∈ Finset.Iio i₀, shiftCount moves i') := by ring
    have hreal : (shiftCount moves i₀ : ℝ) ≤
        ((Nat.ceil (2 * params.Ψ) * params.k *
          (1 + ∑ j ∈ Finset.Iic i₀, rebuildCount moves j +
            ∑ i' ∈ Finset.Iio i₀, shiftCount moves i') : ℕ) : ℝ) := by
      exact_mod_cast hnat'
    push_cast at hreal
    exact hreal
  exact lemma_7_3_level_bound params.d M C hM2 hC0 h2CM
    (fun j => (shiftCount moves j : ℝ)) (fun j => (rebuildCount moves j : ℝ))
    (fun _ => Nat.cast_nonneg _) hstep i.val (Nat.lt_succ_iff.mp i.isLt) i rfl

/-- **Lemma 7.3** (page 35, corrected for initial stretches):
in any play `p` following Algorithm 3 (`FollowsStrategy`), for every level `i ∈ [[d]]`,
the number `s_i` of shift-steps at level `i` is bounded by
`(10Ψk)^{i+1} + ∑_{i' ≤ i} r_{i'} (10Ψk)^{i+1-i'}`.

Departure from the paper: the paper omits the initial-budget term
`(10Ψk)^{i+1}` (equivalently replacing `r_0` by `r_0 + 1`), which is needed when `r_0 = ... = r_i = 0`
and initial stretches at step 0 force shifts. -/
theorem lemma_7_3 (params : GameParams) (p : Play params)
    (hf : FollowsStrategy params p) (i : Fin (params.d + 1)) :
    (shiftCount p.moves i : ℝ) ≤ (10 * params.Ψ * params.k) ^ (i.val + 1) +
      ∑ i' ∈ Finset.Iic i,
        (rebuildCount p.moves i' : ℝ) * (10 * params.Ψ * params.k) ^ (i.val + 1 - i'.val) :=
  lemma_7_3_prefix params p.toValidPlayPrefix hf i

end

end MinCostFlow.Game
