module

public import MinCostFlow.Game.Defs
public import Mathlib.Order.Interval.Finset.Fin

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Shift-and-Rebuild Game: Prefix Sets, Potential, and Lemma 7.5

This file sets up the technical machinery of Section 7.2 (pages 36–37) of the paper
(*A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow*, arXiv:2309.16629v1):

- **Definition 7.6** (`PrefixMaxSet`, page 37): levels whose `repT` weight strictly exceeds
  all lower levels.
- **Definition 7.7** (`PrefixGoodStretchSet`, page 37): levels whose strictly preceding levels
  all have current stretch `≤ σ`.
- **Induction Hypothesis (16)** (`GameIH`, page 37): `log₂ W^{(repT_i)} < Ψ - passes_i` on
  `M^{(s)} ∩ P^{(s)}`.
- The branch-and-pass potential `levelPhi` and unit-step search lemmas (`unitStep_last_eq`,
  `unitStep_first_eq`).
- **Lemma 7.5** (`lemma_7_5_interval` and `lemma_7_5`, page 36): between consecutive shifts at
  level `i < d` (without intermediate resets at `≤ i`), some step has all suffix stretches
  `≤ σ` and `passes = ⌈2Ψ⌉ - 1`.

Departure from the paper in Lemma 7.5:
- The paper treats `i = d - 1` as a base case citing `G_d` having constant size and takes
  `s = s₂` (where `passes_d = 2Ψ`, contradicting `passes_d = 2Ψ - 1`). Here `lemma_7_5`
  proves `i = d - 1` by the exact same branch-cycling argument as `i < d - 1` using only
  `ValidStretch`, yielding `s < s₂` with `passes_{i'} = ⌈2Ψ⌉ - 1` (equal to `2Ψ - 1` when
  `2Ψ ∈ ℕ`).
-/

namespace MinCostFlow.Game

@[expose] public section

/-- **Definition 7.6** (*Prefix Max Set*, page 37):
`M^{(s)} = { i ∈ [[d]] | W^{(repT^{(s)}_{i'})} < W^{(repT^{(s)}_i)} for all i' < i }`. -/
def PrefixMaxSet {d k : ℕ} (W : ℕ → ℝ) (st : GameState d k) : Set (Fin (d + 1)) :=
  { i | ∀ i' : Fin (d + 1), i' < i → W (st.repT i') < W (st.repT i) }

/-- **Definition 7.7** (*Prefix Good Stretch Set*, page 37):
`P^{(s)} = { i ∈ [[d]] | str^{(s)}_{i'} ≤ σ for all i' < i }`. -/
def PrefixGoodStretchSet {d k : ℕ} (σ : ℝ) (st : GameState d k) : Set (Fin (d + 1)) :=
  { i | ∀ i' : Fin (d + 1), i' < i → st.str i' (st.bran i') ≤ σ }

/-- **Induction Hypothesis (16)** (page 37):
at the start of step `s`, `log₂ W^{(repT^{(s)}_i)} < Ψ - passes^{(s)}_i` for all
`i ∈ M^{(s)} ∩ P^{(s)}`. -/
def GameIH (params : GameParams) (W : ℕ → ℝ)
    (st : GameState params.d params.k) (ps : Fin (params.d + 1) → ℕ) : Prop :=
  ∀ i : Fin (params.d + 1),
    i ∈ PrefixMaxSet W st →
    i ∈ PrefixGoodStretchSet params.σ st →
    Real.logb 2 (W (st.repT i)) < params.Ψ - (ps i : ℝ)

/-- A move does not rebuild any level `≤ i` and does not shift any level `< i`. -/
def PreservesBelow {d k : ℕ} (i : Fin (d + 1)) (m : Move d k) : Prop :=
  (∀ i₀ newStr, m = .advRebuild i₀ newStr → i < i₀) ∧
  (∀ i₀ adv newStr, m = .roundStep adv (.shift i₀) newStr → i ≤ i₀)

/-- A move does not rebuild any level `≤ i` and does not shift any level `≤ i`. -/
def PreservesUpTo {d k : ℕ} (i : Fin (d + 1)) (m : Move d k) : Prop :=
  (∀ i₀ newStr, m = .advRebuild i₀ newStr → i < i₀) ∧
  (∀ i₀ adv newStr, m = .roundStep adv (.shift i₀) newStr → i < i₀)

/-- Combined branch/pass potential `Φ_i(s) = passes_i(s) * k + bran_i(s)`. -/
noncomputable def levelPhi {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k))
    (i : Fin (d + 1)) (s : ℕ) : ℕ :=
  passesAt W hk initStr moves s i * k + ((stateAt W hk initStr moves s).bran i).val

end

public section

lemma zero_mem_prefixMaxSet {d k : ℕ} (W : ℕ → ℝ) (st : GameState d k) :
    (0 : Fin (d + 1)) ∈ PrefixMaxSet W st := by
  intro i' hi'
  exact absurd hi' (Fin.not_lt_zero i')

lemma zero_mem_prefixGoodStretchSet {d k : ℕ} (σ : ℝ) (st : GameState d k) :
    (0 : Fin (d + 1)) ∈ PrefixGoodStretchSet σ st := by
  intro i' hi'
  exact absurd hi' (Fin.not_lt_zero i')

lemma step_preservesUpTo {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (st : GameState d k) (ps : Fin (d + 1) → ℕ) (m : Move d k)
    {i : Fin (d + 1)} (hm : PreservesUpTo i m) :
    ∀ i' ≤ i,
      (stepState W hk st m).bran i' = st.bran i' ∧
      (stepState W hk st m).repT i' = st.repT i' ∧
      (stepState W hk st m).str i' = st.str i' ∧
      stepPasses hk st ps m i' = ps i' := by
  intro i' hi'
  cases m with
  | advDoNothing => exact ⟨rfl, rfl, rfl, rfl⟩
  | advRebuild i₀ newStr =>
    have hlt : i < i₀ := hm.1 i₀ newStr rfl
    exact (state_passes_advRebuild W hk st ps i₀ newStr).2 i' (lt_of_le_of_lt hi' hlt)
  | roundStep adv player newStr =>
    cases player with
    | doNothing => exact ⟨rfl, rfl, rfl, rfl⟩
    | shift i₀ =>
      have hlt : i < i₀ := hm.2 i₀ adv newStr rfl
      exact (state_passes_shift W hk st ps adv i₀ newStr).2.2.2.2 i' (lt_of_le_of_lt hi' hlt)

lemma step_str_repT_of_preservesBelow {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k))
    {i : Fin (d + 1)} {t : ℕ} (ht : t < moves.length)
    (hpb : PreservesBelow i moves[t])
    (hp_eq : passesAt W hk initStr moves (t + 1) i = passesAt W hk initStr moves t i) :
    (stateAt W hk initStr moves (t + 1)).str i = (stateAt W hk initStr moves t).str i ∧
    (stateAt W hk initStr moves (t + 1)).repT i = (stateAt W hk initStr moves t).repT i ∧
    (∀ i' < i,
      (stateAt W hk initStr moves (t + 1)).bran i' = (stateAt W hk initStr moves t).bran i' ∧
      (stateAt W hk initStr moves (t + 1)).repT i' = (stateAt W hk initStr moves t).repT i' ∧
      (stateAt W hk initStr moves (t + 1)).str i' = (stateAt W hk initStr moves t).str i' ∧
      passesAt W hk initStr moves (t + 1) i' = passesAt W hk initStr moves t i') := by
  rw [stateAt_succ W hk initStr moves ht]
  rw [passesAt_succ W hk initStr moves ht] at hp_eq
  cases hm : moves[t] with
  | advDoNothing =>
    refine ⟨rfl, rfl, fun i' _ => ?_⟩
    rw [passesAt_succ W hk initStr moves ht, hm]
    exact ⟨rfl, rfl, rfl, rfl⟩
  | advRebuild i₀ newStr =>
    have hgt : i < i₀ := hpb.1 i₀ newStr hm
    have h1 := (state_passes_advRebuild W hk (stateAt W hk initStr moves t)
      (passesAt W hk initStr moves t) i₀ newStr).2 i hgt
    refine ⟨h1.2.2.1, h1.2.1, fun i' hi' => ?_⟩
    rw [passesAt_succ W hk initStr moves ht, hm]
    exact (state_passes_advRebuild W hk _ _ i₀ newStr).2 i' (lt_trans hi' hgt)
  | roundStep adv player newStr =>
    cases player with
    | doNothing =>
      refine ⟨rfl, rfl, fun i' _ => ?_⟩
      rw [passesAt_succ W hk initStr moves ht, hm]
      exact ⟨rfl, rfl, rfl, rfl⟩
    | shift i₀ =>
      have hge : i ≤ i₀ := hpb.2 i₀ adv newStr hm
      rcases lt_or_eq_of_le hge with hgt | rfl
      · have h1 := (state_passes_shift W hk (stateAt W hk initStr moves t)
          (passesAt W hk initStr moves t) adv i₀ newStr).2.2.2.2 i hgt
        refine ⟨h1.2.2.1, h1.2.1, fun i' hi' => ?_⟩
        rw [passesAt_succ W hk initStr moves ht, hm]
        exact (state_passes_shift W hk _ _ adv i₀ newStr).2.2.2.2 i' (lt_trans hi' hgt)
      · rw [hm] at hp_eq
        have htr := state_passes_shift W hk (stateAt W hk initStr moves t)
          (passesAt W hk initStr moves t) adv i newStr
        have hnowrap : (nextBranch hk ((stateAt W hk initStr moves t).bran i)).val ≠ 0 := by
          intro hwrap
          have hinc := (htr.2.2.1 hwrap).2.2
          rw [hinc] at hp_eq
          omega
        have hnw := htr.2.2.2.1 hnowrap
        refine ⟨hnw.2.1, hnw.1, fun i' hi' => ?_⟩
        rw [passesAt_succ W hk initStr moves ht, hm]
        exact htr.2.2.2.2 i' hi'

lemma passes_eq_levelPhi_div {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k))
    (i : Fin (d + 1)) (s : ℕ) :
    passesAt W hk initStr moves s i = levelPhi W hk initStr moves i s / k := by
  unfold levelPhi
  have hlt := ((stateAt W hk initStr moves s).bran i).isLt
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt hlt, Nat.zero_add]

lemma bran_val_eq_levelPhi_mod {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k))
    (i : Fin (d + 1)) (s : ℕ) :
    ((stateAt W hk initStr moves s).bran i).val = levelPhi W hk initStr moves i s % k := by
  unfold levelPhi
  have hlt := ((stateAt W hk initStr moves s).bran i).isLt
  rw [Nat.mul_comm _ k, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

lemma levelPhi_zero {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k)) (i : Fin (d + 1)) :
    levelPhi W hk initStr moves i 0 = 0 := by
  simp [levelPhi, stateAt_zero, passesAt_zero, initState]

lemma levelPhi_shift_self {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k))
    (i : Fin (d + 1)) {s : ℕ} (hs : s < moves.length)
    {adv : RoundChoice} {newStr : Fin (d + 1) → Fin k → ℝ}
    (hm : moves[s] = .roundStep adv (.shift i) newStr) :
    levelPhi W hk initStr moves i (s + 1) = levelPhi W hk initStr moves i s + 1 := by
  unfold levelPhi
  rw [stateAt_succ W hk initStr moves hs, passesAt_succ W hk initStr moves hs, hm]
  have htr := state_passes_shift W hk (stateAt W hk initStr moves s)
    (passesAt W hk initStr moves s) adv i newStr
  have hblt := ((stateAt W hk initStr moves s).bran i).isLt
  by_cases hwrap : (nextBranch hk ((stateAt W hk initStr moves s).bran i)).val = 0
  · have h1 := (htr.2.2.1 hwrap).2.2
    have h2 : ((stepState W hk (stateAt W hk initStr moves s)
        (.roundStep adv (.shift i) newStr)).bran i).val = 0 := by
      rw [htr.2.1, hwrap]
    have hbk : ((stateAt W hk initStr moves s).bran i).val + 1 = k :=
      (nextBranch_val_eq_zero_iff hk _).mp hwrap
    have hmul : (passesAt W hk initStr moves s i + 1) * k =
        passesAt W hk initStr moves s i * k + k := by ring
    rw [h1, h2, hmul]
    omega
  · have h1 := (htr.2.2.2.1 hwrap).2.2
    have hbk : ((stateAt W hk initStr moves s).bran i).val + 1 < k := by
      have hne := mt (nextBranch_val_eq_zero_iff hk ((stateAt W hk initStr moves s).bran i)).mpr hwrap
      omega
    have h2 : ((stepState W hk (stateAt W hk initStr moves s)
        (.roundStep adv (.shift i) newStr)).bran i).val =
        ((stateAt W hk initStr moves s).bran i).val + 1 := by
      rw [htr.2.1, nextBranch_val, Nat.mod_eq_of_lt hbk]
    rw [h1, h2]
    ring

lemma levelPhi_step_cases {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k))
    (i : Fin (d + 1)) {s : ℕ} (hs : s < moves.length) :
    (∀ i₀ newStr, moves[s] = .advRebuild i₀ newStr → i₀ ≤ i →
      levelPhi W hk initStr moves i (s + 1) = 0) ∧
    (∀ i₀ adv newStr, moves[s] = .roundStep adv (.shift i₀) newStr → i₀ < i →
      levelPhi W hk initStr moves i (s + 1) = 0) ∧
    (∀ adv newStr, moves[s] = .roundStep adv (.shift i) newStr →
      levelPhi W hk initStr moves i (s + 1) = levelPhi W hk initStr moves i s + 1) ∧
    (PreservesUpTo i moves[s] →
      levelPhi W hk initStr moves i (s + 1) = levelPhi W hk initStr moves i s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i₀ newStr hm hle
    unfold levelPhi
    rw [stateAt_succ W hk initStr moves hs, passesAt_succ W hk initStr moves hs, hm]
    have htr := (state_passes_advRebuild W hk (stateAt W hk initStr moves s)
      (passesAt W hk initStr moves s) i₀ newStr).1 i hle
    rw [htr.1, htr.2.2.2]
    simp
  · intro i₀ adv newStr hm hlt
    unfold levelPhi
    rw [stateAt_succ W hk initStr moves hs, passesAt_succ W hk initStr moves hs, hm]
    have htr := (state_passes_shift W hk (stateAt W hk initStr moves s)
      (passesAt W hk initStr moves s) adv i₀ newStr).1 i hlt
    rw [htr.1, htr.2.2.2]
    simp
  · intro adv newStr hm
    exact levelPhi_shift_self W hk initStr moves i hs hm
  · intro hpres
    unfold levelPhi
    rw [stateAt_succ W hk initStr moves hs, passesAt_succ W hk initStr moves hs]
    have htr := step_preservesUpTo W hk (stateAt W hk initStr moves s)
      (passesAt W hk initStr moves s) moves[s] hpres i le_rfl
    rw [htr.1, htr.2.2.2]

lemma passes_succ_le {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k))
    (i : Fin (d + 1)) {s : ℕ} (hs : s < moves.length) :
    passesAt W hk initStr moves (s + 1) i ≤ passesAt W hk initStr moves s i + 1 := by
  rw [passesAt_succ W hk initStr moves hs]
  cases hm : moves[s] with
  | advDoNothing => simp [stepPasses]
  | advRebuild i₀ _ =>
    dsimp [stepPasses]
    split_ifs <;> omega
  | roundStep _ player _ =>
    cases player with
    | doNothing => simp [stepPasses]
    | shift i₀ =>
      dsimp [stepPasses]
      by_cases hlt : i₀ < i
      · simp [hlt]
      · by_cases heq : i = i₀
        · subst heq
          by_cases hwrap : (nextBranch hk ((stateAt W hk initStr moves s).bran i)).val = 0 <;>
            simp [hwrap]
        · simp [hlt, heq]

lemma preservesUpTo_advDoNothing {d k : ℕ} (i : Fin (d + 1)) :
    PreservesUpTo i (.advDoNothing : Move d k) := by
  refine ⟨?_, ?_⟩
  · intro _ _ h; cases h
  · intro _ _ _ h; cases h

lemma preservesUpTo_roundDoNothing {d k : ℕ} (i : Fin (d + 1))
    (adv : RoundChoice) (newStr : Fin (d + 1) → Fin k → ℝ) :
    PreservesUpTo i (.roundStep adv .doNothing newStr) := by
  refine ⟨?_, ?_⟩
  · intro _ _ h; cases h
  · intro _ _ _ h; cases h

lemma preservesUpTo_advRebuild_gt {d k : ℕ} {i i₀ : Fin (d + 1)}
    (hgt : i < i₀) (newStr : Fin (d + 1) → Fin k → ℝ) :
    PreservesUpTo i (.advRebuild i₀ newStr) := by
  refine ⟨?_, ?_⟩
  · intro i₁ _ h; cases h; exact hgt
  · intro _ _ _ h; cases h

lemma preservesUpTo_shift_gt {d k : ℕ} {i i₀ : Fin (d + 1)}
    (hgt : i < i₀) (adv : RoundChoice) (newStr : Fin (d + 1) → Fin k → ℝ) :
    PreservesUpTo i (.roundStep adv (.shift i₀) newStr) := by
  refine ⟨?_, ?_⟩
  · intro _ _ h; cases h
  · intro i₁ _ _ h; cases h; exact hgt

lemma levelPhi_mono_of_preservesBelow {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k))
    (i : Fin (d + 1)) {s : ℕ} (hs : s < moves.length)
    (hpb : PreservesBelow i moves[s]) :
    levelPhi W hk initStr moves i s ≤ levelPhi W hk initStr moves i (s + 1) ∧
    levelPhi W hk initStr moves i (s + 1) ≤ levelPhi W hk initStr moves i s + 1 := by
  have hcases := levelPhi_step_cases W hk initStr moves i hs
  cases hm : moves[s] with
  | advDoNothing =>
    rw [hcases.2.2.2 (hm ▸ preservesUpTo_advDoNothing i)]
    omega
  | advRebuild i₀ newStr =>
    rw [hcases.2.2.2 (hm ▸ preservesUpTo_advRebuild_gt (hpb.1 i₀ newStr hm) newStr)]
    omega
  | roundStep adv player newStr =>
    cases player with
    | doNothing =>
      rw [hcases.2.2.2 (hm ▸ preservesUpTo_roundDoNothing i adv newStr)]
      omega
    | shift i₀ =>
      rcases lt_or_eq_of_le (hpb.2 i₀ adv newStr hm) with hgt | rfl
      · rw [hcases.2.2.2 (hm ▸ preservesUpTo_shift_gt hgt adv newStr)]
        omega
      · rw [hcases.2.2.1 adv newStr hm]
        omega

lemma shift_self_of_levelPhi_lt {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k))
    {i : Fin (d + 1)} {t : ℕ} (ht : t < moves.length)
    (hpb : PreservesBelow i moves[t])
    (hlt : levelPhi W hk initStr moves i t < levelPhi W hk initStr moves i (t + 1)) :
    ∃ adv newStr, moves[t] = .roundStep adv (.shift i) newStr := by
  have hcases := levelPhi_step_cases W hk initStr moves i ht
  cases hm : moves[t] with
  | advDoNothing =>
    rw [hcases.2.2.2 (hm ▸ preservesUpTo_advDoNothing i)] at hlt; omega
  | advRebuild i₀ newStr =>
    rw [hcases.2.2.2 (hm ▸ preservesUpTo_advRebuild_gt (hpb.1 i₀ newStr hm) newStr)] at hlt; omega
  | roundStep adv player newStr =>
    cases player with
    | doNothing =>
      rw [hcases.2.2.2 (hm ▸ preservesUpTo_roundDoNothing i adv newStr)] at hlt; omega
    | shift i₀ =>
      rcases lt_or_eq_of_le (hpb.2 i₀ adv newStr hm) with hgt | rfl
      · rw [hcases.2.2.2 (hm ▸ preservesUpTo_shift_gt hgt adv newStr)] at hlt; omega
      · exact ⟨adv, newStr, rfl⟩

lemma levelPhi_mono_le {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k))
    (i : Fin (d + 1)) {a b : ℕ} (hb : b ≤ moves.length)
    (hpb : ∀ s, a ≤ s → (hs : s < b) → PreservesBelow i (moves[s]'(lt_of_lt_of_le hs hb)))
    {s₁ s₂ : ℕ} (hs₁ : a ≤ s₁) (hs₁₂ : s₁ ≤ s₂) (hs₂ : s₂ ≤ b) :
    levelPhi W hk initStr moves i s₁ ≤ levelPhi W hk initStr moves i s₂ := by
  induction hs₁₂ with
  | refl => exact le_rfl
  | @step m hle ih =>
    have hm : m < b := by omega
    have hmlen : m < moves.length := lt_of_lt_of_le hm hb
    have hstep := (levelPhi_mono_of_preservesBelow W hk initStr moves i hmlen
      (hpb m (le_trans hs₁ hle) hm)).1
    exact le_trans (ih (by omega)) hstep

lemma interval_str_repT_of_phi_band {d k : ℕ} (W : ℕ → ℝ) (hk : 0 < k)
    (initStr : Fin (d + 1) → Fin k → ℝ) (moves : List (Move d k))
    (i : Fin (d + 1)) {lo hi p₀ : ℕ} (hhi : hi ≤ moves.length)
    (hpb : ∀ t, lo ≤ t → (ht : t < hi) → PreservesBelow i (moves[t]'(lt_of_lt_of_le ht hhi)))
    (hband : ∀ t, lo ≤ t → t ≤ hi →
      p₀ * k ≤ levelPhi W hk initStr moves i t ∧ levelPhi W hk initStr moves i t < (p₀ + 1) * k) :
    ∀ s, lo ≤ s → s ≤ hi →
      (stateAt W hk initStr moves s).str i = (stateAt W hk initStr moves lo).str i ∧
      (stateAt W hk initStr moves s).repT i = (stateAt W hk initStr moves lo).repT i ∧
      (∀ i' < i,
        (stateAt W hk initStr moves s).bran i' = (stateAt W hk initStr moves lo).bran i' ∧
        (stateAt W hk initStr moves s).repT i' = (stateAt W hk initStr moves lo).repT i' ∧
        (stateAt W hk initStr moves s).str i' = (stateAt W hk initStr moves lo).str i' ∧
        passesAt W hk initStr moves s i' = passesAt W hk initStr moves lo i') := by
  intro s hlo hshi
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hlo
  clear hlo
  induction r with
  | zero => simp
  | succ r ih =>
    have hrhi : lo + r < hi := by omega
    have hrlen : lo + r < moves.length := lt_of_lt_of_le hrhi hhi
    have ih' := ih (by omega)
    have hp1 : passesAt W hk initStr moves (lo + r) i = p₀ := by
      rw [passes_eq_levelPhi_div]
      have hb := hband (lo + r) (by omega) (by omega)
      have h1 : p₀ ≤ levelPhi W hk initStr moves i (lo + r) / k := by
        rw [Nat.le_div_iff_mul_le hk]; exact hb.1
      have h2 : levelPhi W hk initStr moves i (lo + r) / k < p₀ + 1 := by
        rw [Nat.div_lt_iff_lt_mul hk]; exact hb.2
      omega
    have hp2 : passesAt W hk initStr moves (lo + r + 1) i = p₀ := by
      rw [passes_eq_levelPhi_div]
      have hb := hband (lo + r + 1) (by omega) hshi
      have h1 : p₀ ≤ levelPhi W hk initStr moves i (lo + r + 1) / k := by
        rw [Nat.le_div_iff_mul_le hk]; exact hb.1
      have h2 : levelPhi W hk initStr moves i (lo + r + 1) / k < p₀ + 1 := by
        rw [Nat.div_lt_iff_lt_mul hk]; exact hb.2
      omega
    have hstep := step_str_repT_of_preservesBelow W hk initStr moves hrlen
      (hpb (lo + r) (by omega) hrhi) (hp2.trans hp1.symm)
    refine ⟨hstep.1.trans ih'.1, hstep.2.1.trans ih'.2.1, fun i' hi' => ?_⟩
    have hs' := hstep.2.2 i' hi'
    have hi'' := ih'.2.2 i' hi'
    exact ⟨hs'.1.trans hi''.1, hs'.2.1.trans hi''.2.1,
      hs'.2.2.1.trans hi''.2.2.1, hs'.2.2.2.trans hi''.2.2.2⟩

/-- Last index `t ∈ [a, b)` where `f t ≤ v`, assuming `a ≤ b`, `f a ≤ v < f b`, and unit upward
steps `f (t + 1) ≤ f t + 1`. -/
lemma unitStep_last_eq (f : ℕ → ℕ) {a b v : ℕ}
    (hab_le : a ≤ b) (hfa : f a ≤ v) (hfb : v < f b)
    (hstep : ∀ t, a ≤ t → t < b → f (t + 1) ≤ f t + 1) :
    ∃ t, a ≤ t ∧ t < b ∧ f t = v ∧ f (t + 1) = v + 1 ∧
      ∀ r, t + 1 ≤ r → r ≤ b → v + 1 ≤ f r := by
  have hab : a < b := by
    by_contra h
    have hEq : a = b := le_antisymm hab_le (not_lt.mp h)
    rw [hEq] at hfa; omega
  let S := (Finset.Ico a b).filter (fun t => f t ≤ v)
  have hS : S.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨le_rfl, hab⟩, hfa⟩⟩
  let t := S.max' hS
  have ht_mem := Finset.mem_filter.mp (Finset.max'_mem S hS)
  have ht_ico := Finset.mem_Ico.mp ht_mem.1
  have ht_le : f t ≤ v := ht_mem.2
  have hge_after : ∀ r, t + 1 ≤ r → r ≤ b → v + 1 ≤ f r := by
    intro r hr1 hr2
    rcases eq_or_lt_of_le hr2 with rfl | hrb
    · exact hfb
    · by_contra hlt
      have hrS : r ∈ S := Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨by omega, hrb⟩, Nat.le_of_lt_succ (not_le.mp hlt)⟩
      have := Finset.le_max' S r hrS
      omega
  have hsucc_ge : v + 1 ≤ f (t + 1) := hge_after (t + 1) le_rfl ht_ico.2
  have hsucc_le : f (t + 1) ≤ f t + 1 := hstep t ht_ico.1 ht_ico.2
  exact ⟨t, ht_ico.1, ht_ico.2, by omega, by omega, hge_after⟩

/-- First index `t ∈ [a, b]` where `v ≤ f t`, assuming `a ≤ b`, `f a ≤ v ≤ f b`, and unit upward
steps `f (t + 1) ≤ f t + 1`. -/
lemma unitStep_first_eq (f : ℕ → ℕ) {a b v : ℕ}
    (hab : a ≤ b) (hfa : f a ≤ v) (hfb : v ≤ f b)
    (hstep : ∀ t, a ≤ t → t < b → f (t + 1) ≤ f t + 1) :
    ∃ t, a ≤ t ∧ t ≤ b ∧ f t = v ∧
      (f a < v → a < t ∧ f (t - 1) + 1 = v) ∧
      ∀ r, a ≤ r → r < t → f r < v := by
  let S := (Finset.Icc a b).filter (fun t => v ≤ f t)
  have hS : S.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hab, le_rfl⟩, hfb⟩⟩
  have ht_mem := Finset.mem_filter.mp (Finset.min'_mem S hS)
  have ht_icc := Finset.mem_Icc.mp ht_mem.1
  have ht_ge : v ≤ f (S.min' hS) := ht_mem.2
  have hlt_before : ∀ r, a ≤ r → r < S.min' hS → f r < v := by
    intro r hr1 hr2
    by_contra hge
    have hrS : r ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hr1, by omega⟩, not_lt.mp hge⟩
    have := Finset.min'_le S r hrS
    omega
  have hft : f (S.min' hS) = v := by
    rcases eq_or_lt_of_le ht_icc.1 with hEq | hat
    · rw [hEq] at hfa
      omega
    · have hprev := hlt_before (S.min' hS - 1) (by omega) (by omega)
      have hup := hstep (S.min' hS - 1) (by omega) (by omega)
      rw [Nat.sub_add_cancel (by omega)] at hup
      omega
  refine ⟨S.min' hS, ht_icc.1, ht_icc.2, hft, ?_, hlt_before⟩
  intro hlt
  have hat : a < S.min' hS := by
    by_contra hnot
    have hEq : a = S.min' hS := le_antisymm ht_icc.1 (not_lt.mp hnot)
    rw [hEq] at hlt
    omega
  have hprev := hlt_before (S.min' hS - 1) (by omega) (by omega)
  have hup := hstep (S.min' hS - 1) (by omega) (by omega)
  rw [Nat.sub_add_cancel (by omega)] at hup
  exact ⟨hat, by omega⟩

lemma shift_step_strategy_props (params : GameParams) {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    (hv : ValidPlayPrefix params W initStr moves)
    (hf : FollowsStrategyPrefix params W initStr moves)
    {s : ℕ} (hs : s < moves.length)
    {i : Fin (params.d + 1)} {adv : RoundChoice} {newStr : Fin (params.d + 1) → Fin params.k → ℝ}
    (hm : moves[s] = .roundStep adv (.shift i) newStr) :
    adv = .roundContinuing ∧
    passesAt W params.hk initStr moves s i < Nat.ceil (2 * params.Ψ) ∧
    (∀ i' : Fin (params.d + 1), i < i' →
      Nat.ceil (2 * params.Ψ) ≤ passesAt W params.hk initStr moves s i') := by
  have hstep := hv.2 s hs
  have hstrat := hf s hs
  dsimp only [ValidStep] at hstep
  dsimp only [StrategyStep] at hstrat
  have hph : (stateAt W params.hk initStr moves s).phase = .stage34 := by
    cases h : (stateAt W params.hk initStr moves s).phase
    · rw [h, hm] at hstep; exact False.elim hstep.2
    · rfl
  rw [hph, hm] at hstrat
  cases adv with
  | roundCompleting =>
    simp at hstrat
  | roundContinuing =>
    rcases hstrat with ⟨i₀, hi₀lt, hi₀max, hEq⟩
    injection hEq with hiEq
    subst hiEq
    refine ⟨rfl, Nat.lt_ceil.mpr hi₀lt, ?_⟩
    intro i' hi'
    by_contra hlt
    have hlt' : (passesAt W params.hk initStr moves s i' : ℝ) < 2 * params.Ψ :=
      Nat.lt_ceil.mp (not_le.mp hlt)
    have hle := hi₀max i' hlt'
    exact absurd hi' (not_lt.mpr hle)

/-- **Lemma 7.5** (page 36), interval form:
on `[a, b)` preserving levels `≤ i`, starting with `passes_{i'} = 0` for `i' > i` and reaching
`passes_{i'} ≥ ⌈2Ψ⌉` for `i' > i` at `b` (for `i < d`), there exists a step `s ∈ [a, b)` where the
player shifts (so Stage 3 chose `roundContinuing`), all levels `i' > i` have current stretch `≤ σ`,
and `passes_{i'} = ⌈2Ψ⌉ - 1`. -/
lemma lemma_7_5_interval (params : GameParams) {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    (hv : ValidPlayPrefix params W initStr moves)
    (hf : FollowsStrategyPrefix params W initStr moves) :
    ∀ (r : ℕ) (i : Fin (params.d + 1)), i.val < params.d → params.d - i.val = r →
      ∀ a b : ℕ, a ≤ b → (hblen : b ≤ moves.length) →
        (∀ s, a ≤ s → (hsb : s < b) →
          PreservesUpTo i (moves[s]'(lt_of_lt_of_le hsb hblen))) →
        (∀ i' : Fin (params.d + 1), i < i' → passesAt W params.hk initStr moves a i' = 0) →
        (∀ i' : Fin (params.d + 1), i < i' →
          Nat.ceil (2 * params.Ψ) ≤ passesAt W params.hk initStr moves b i') →
        ∃ s, a ≤ s ∧ s < b ∧
          (∃ i₀ newStr, moves[s]? = some (.roundStep .roundContinuing (.shift i₀) newStr)) ∧
          (∀ i' : Fin (params.d + 1), i < i' →
            (stateAt W params.hk initStr moves s).str i'
              ((stateAt W params.hk initStr moves s).bran i') ≤ params.σ ∧
            passesAt W params.hk initStr moves s i' = Nat.ceil (2 * params.Ψ) - 1) := by
  intro r
  induction r with
  | zero =>
    intro i hi hdiff
    omega
  | succ r ih =>
    intro i hi hdiff a b hab hblen hpres ha0 hbP
    let P := Nat.ceil (2 * params.Ψ)
    have hP2 : 2 ≤ P := by
      have h1 : (2 : ℝ) ≤ (P : ℝ) := le_trans (by linarith [params.hΨ]) (Nat.le_ceil _)
      exact_mod_cast h1
    let i₁ : Fin (params.d + 1) := ⟨i.val + 1, by omega⟩
    have hi_lt : i < i₁ := Nat.lt_succ_self i.val
    have ha_i₁ : passesAt W params.hk initStr moves a i₁ = 0 := ha0 i₁ hi_lt
    have hb_i₁ : P ≤ passesAt W params.hk initStr moves b i₁ := hbP i₁ hi_lt
    obtain ⟨u₀, hau₀, hu₀b, hu₀_eq, hu₀_succ, hge_u₀⟩ := unitStep_last_eq
      (fun t => passesAt W params.hk initStr moves t i₁)
      hab
      (v := P - 2)
      (by rw [ha_i₁]; omega)
      (by omega)
      (fun t _ htb => passes_succ_le W params.hk initStr moves i₁ (lt_of_lt_of_le htb hblen))
    have hu₀len : u₀ < moves.length := lt_of_lt_of_le hu₀b hblen
    have hu₀_shift : ∃ adv newStr, moves[u₀] = .roundStep adv (.shift i₁) newStr ∧
        (nextBranch params.hk ((stateAt W params.hk initStr moves u₀).bran i₁)).val = 0 := by
      have hsucc := congrArg (fun f => f i₁) (passesAt_succ W params.hk initStr moves hu₀len)
      cases hm : moves[u₀] with
      | advDoNothing =>
        rw [hm] at hsucc
        simp [stepPasses] at hsucc; omega
      | advRebuild i₀ newStr =>
        rw [hm] at hsucc
        dsimp [stepPasses] at hsucc
        by_cases hle : i₀ ≤ i₁ <;> simp [hle] at hsucc <;> omega
      | roundStep adv player newStr =>
        cases player with
        | doNothing =>
          rw [hm] at hsucc
          simp [stepPasses] at hsucc; omega
        | shift i₀ =>
          rw [hm] at hsucc
          dsimp [stepPasses] at hsucc
          by_cases hlt : i₀ < i₁
          · simp [hlt] at hsucc; omega
          · by_cases heq : i₁ = i₀
            · rw [← heq] at hsucc ⊢
              by_cases hwrap : (nextBranch params.hk
                  ((stateAt W params.hk initStr moves u₀).bran i₁)).val = 0
              · exact ⟨adv, newStr, rfl, hwrap⟩
              · simp [hwrap] at hsucc; omega
            · simp [hlt, heq] at hsucc; omega
    rcases hu₀_shift with ⟨adv₀, newStr₀, hmu₀, hwrap₀⟩
    have hu₀_succ_bran : ((stateAt W params.hk initStr moves (u₀ + 1)).bran i₁).val = 0 := by
      rw [stateAt_succ W params.hk initStr moves hu₀len, hmu₀]
      rw [(state_passes_shift W params.hk (stateAt W params.hk initStr moves u₀)
        (passesAt W params.hk initStr moves u₀) adv₀ i₁ newStr₀).2.1]
      exact hwrap₀
    have hu₀_succ_passes : ∀ i' : Fin (params.d + 1), i₁ < i' →
        passesAt W params.hk initStr moves (u₀ + 1) i' = 0 := by
      intro i' hi'
      rw [passesAt_succ W params.hk initStr moves hu₀len, hmu₀]
      simp [stepPasses, hi']
    have hpb_tail : ∀ s, u₀ + 1 ≤ s → (hs2 : s < b) →
        PreservesBelow i₁ (moves[s]'(lt_of_lt_of_le hs2 hblen)) := by
      intro s hs1 hs2
      have hpres_s := hpres s (by omega) hs2
      have h_no_reset : P - 1 ≤ passesAt W params.hk initStr moves (s + 1) i₁ := by
        have h := hge_u₀ (s + 1) (by omega) (Nat.succ_le_of_lt hs2)
        omega
      have hslen : s < moves.length := lt_of_lt_of_le hs2 hblen
      constructor
      · intro i₀ newStr hm
        by_contra hle
        have hle' : i₀ ≤ i₁ := not_lt.mp hle
        rw [passesAt_succ W params.hk initStr moves hslen, hm] at h_no_reset
        have hz := ((state_passes_advRebuild W params.hk
          (stateAt W params.hk initStr moves s) (passesAt W params.hk initStr moves s)
          i₀ newStr).1 i₁ hle').2.2.2
        rw [hz] at h_no_reset
        omega
      · intro i₀ adv newStr hm
        by_contra hlt
        have hlt' : i₀ < i₁ := not_le.mp hlt
        have hlt_val : i₀.val < i₁.val := hlt'
        dsimp only [i₁] at hlt_val
        have hle' : i₀ ≤ i := Fin.le_iff_val_le_val.mpr (by omega)
        have hgt := hpres_s.2 i₀ adv newStr hm
        exact absurd hgt (not_lt.mpr hle')
    have hphi_u₀ : levelPhi W params.hk initStr moves i₁ (u₀ + 1) = (P - 1) * params.k := by
      unfold levelPhi
      rw [hu₀_succ_bran, Nat.add_zero]
      have : passesAt W params.hk initStr moves (u₀ + 1) i₁ = P - 1 := by omega
      rw [this]
    have hphi_b : P * params.k ≤ levelPhi W params.hk initStr moves i₁ b := by
      unfold levelPhi
      calc
        P * params.k ≤ passesAt W params.hk initStr moves b i₁ * params.k :=
          Nat.mul_le_mul_right params.k hb_i₁
        _ ≤ passesAt W params.hk initStr moves b i₁ * params.k +
            ((stateAt W params.hk initStr moves b).bran i₁).val := Nat.le_add_right _ _
    have hstr_u₀ : ValidStretch params.σ ((stateAt W params.hk initStr moves (u₀ + 1)).str i₁) :=
      (str_nonneg_and_valid hv (u₀ + 1) (by omega) i₁).2
    obtain ⟨jStar, hjStar⟩ := hstr_u₀
    let target := (P - 1) * params.k + jStar.val
    have htarget_lo : levelPhi W params.hk initStr moves i₁ (u₀ + 1) ≤ target := by
      rw [hphi_u₀]; exact Nat.le_add_right _ _
    have htarget_hi : target < levelPhi W params.hk initStr moves i₁ b := by
      have hjlt := jStar.isLt
      have hPk : P * params.k = (P - 1) * params.k + params.k := by
        calc
          P * params.k = ((P - 1) + 1) * params.k := by rw [Nat.sub_add_cancel (by omega)]
          _ = (P - 1) * params.k + params.k := by ring
      omega
    have hstep_phi : ∀ t, u₀ + 1 ≤ t → t < b →
        levelPhi W params.hk initStr moves i₁ (t + 1) ≤
          levelPhi W params.hk initStr moves i₁ t + 1 := by
      intro t ht1 ht2
      exact (levelPhi_mono_of_preservesBelow W params.hk initStr moves i₁
        (lt_of_lt_of_le ht2 hblen) (hpb_tail t ht1 ht2)).2
    obtain ⟨u_end, hu_end1, hu_end2, hu_end_eq, hu_end_succ, _⟩ := unitStep_last_eq
      (levelPhi W params.hk initStr moves i₁) (by omega) htarget_lo htarget_hi hstep_phi
    have hu_end_len : u_end < moves.length := lt_of_lt_of_le hu_end2 hblen
    have hu_end_shift : ∃ newStr, moves[u_end] = .roundStep .roundContinuing (.shift i₁) newStr := by
      obtain ⟨adv, newStr, hm⟩ := shift_self_of_levelPhi_lt W params.hk initStr moves hu_end_len
        (hpb_tail u_end hu_end1 hu_end2) (by omega)
      have hadv := (shift_step_strategy_props params hv hf hu_end_len hm).1
      subst hadv
      exact ⟨newStr, hm⟩
    obtain ⟨a', ha'1, ha'2, ha'_eq, ha'_prev, ha'_lt⟩ := unitStep_first_eq
      (levelPhi W params.hk initStr moves i₁) hu_end1 htarget_lo (le_of_eq hu_end_eq.symm)
      (fun t ht1 ht2 => hstep_phi t ht1 (lt_of_lt_of_le ht2 (le_of_lt hu_end2)))
    have hphi_const : ∀ t, a' ≤ t → t ≤ u_end →
        levelPhi W params.hk initStr moves i₁ t = target := by
      intro t ht1 ht2
      have h1 : levelPhi W params.hk initStr moves i₁ a' ≤
          levelPhi W params.hk initStr moves i₁ t :=
        levelPhi_mono_le W params.hk initStr moves i₁ (le_trans (le_of_lt hu_end2) hblen)
          (fun x hx1 hx2 => hpb_tail x (by omega) (by omega)) ha'1 ht1 ht2
      have h2 : levelPhi W params.hk initStr moves i₁ t ≤
          levelPhi W params.hk initStr moves i₁ u_end :=
        levelPhi_mono_le W params.hk initStr moves i₁ (le_trans (le_of_lt hu_end2) hblen)
          (fun x hx1 hx2 => hpb_tail x (by omega) (by omega)) (by omega) ht2 le_rfl
      omega
    have hband' : ∀ t, u₀ + 1 ≤ t → t ≤ u_end →
        (P - 1) * params.k ≤ levelPhi W params.hk initStr moves i₁ t ∧
        levelPhi W params.hk initStr moves i₁ t < ((P - 1) + 1) * params.k := by
      intro t ht1 ht2
      have h1 : levelPhi W params.hk initStr moves i₁ (u₀ + 1) ≤
          levelPhi W params.hk initStr moves i₁ t :=
        levelPhi_mono_le W params.hk initStr moves i₁ (le_trans (le_of_lt hu_end2) hblen)
          (fun x hx1 hx2 => hpb_tail x hx1 (by omega)) le_rfl ht1 ht2
      have h2 : levelPhi W params.hk initStr moves i₁ t ≤
          levelPhi W params.hk initStr moves i₁ u_end :=
        levelPhi_mono_le W params.hk initStr moves i₁ (le_trans (le_of_lt hu_end2) hblen)
          (fun x hx1 hx2 => hpb_tail x hx1 (by omega)) (by omega) ht2 le_rfl
      have hjlt := jStar.isLt
      have hPk : ((P - 1) + 1) * params.k = (P - 1) * params.k + params.k := by ring
      omega
    have hstr_const := interval_str_repT_of_phi_band W params.hk initStr moves i₁
      (le_trans (le_of_lt hu_end2) hblen) (fun t ht1 ht2 => hpb_tail t ht1 (by omega)) hband'
    have hi₁_props : ∀ t, a' ≤ t → t ≤ u_end →
        (stateAt W params.hk initStr moves t).str i₁
          ((stateAt W params.hk initStr moves t).bran i₁) ≤ params.σ ∧
        passesAt W params.hk initStr moves t i₁ = P - 1 := by
      intro t ht1 ht2
      have hphi_t := hphi_const t ht1 ht2
      have hpasses_t : passesAt W params.hk initStr moves t i₁ = P - 1 := by
        rw [passes_eq_levelPhi_div, hphi_t]
        dsimp only [target]
        rw [Nat.add_comm, Nat.mul_comm,
          Nat.add_mul_div_left _ _ params.hk, Nat.div_eq_of_lt jStar.isLt, Nat.zero_add]
      have hbran_t : (stateAt W params.hk initStr moves t).bran i₁ = jStar := by
        ext
        rw [bran_val_eq_levelPhi_mod, hphi_t]
        dsimp only [target]
        rw [Nat.mul_comm _ params.k, Nat.mul_add_mod, Nat.mod_eq_of_lt jStar.isLt]
      have hstr_t := (hstr_const t (by omega) ht2).1
      rw [hbran_t, hstr_t]
      exact ⟨hjStar, hpasses_t⟩
    have ha'_passes_gt : ∀ i' : Fin (params.d + 1), i₁ < i' →
        passesAt W params.hk initStr moves a' i' = 0 := by
      intro i' hi'
      by_cases hj0 : jStar.val = 0
      · have ha'_eq_u₀ : a' = u₀ + 1 := by
          by_contra hne
          have hlt := lt_of_le_of_ne ha'1 (Ne.symm hne)
          have hbad := ha'_lt (u₀ + 1) le_rfl hlt
          dsimp [target] at hbad
          rw [hj0, Nat.add_zero, hphi_u₀] at hbad
          exact lt_irrefl _ hbad
        rw [ha'_eq_u₀]
        exact hu₀_succ_passes i' hi'
      · have hlt_target : levelPhi W params.hk initStr moves i₁ (u₀ + 1) < target := by
          dsimp [target]; rw [hphi_u₀]; omega
        obtain ⟨ha'_gt, hprev_eq⟩ := ha'_prev hlt_target
        have hpred_len : a' - 1 < moves.length := by omega
        have hpred_lt : levelPhi W params.hk initStr moves i₁ (a' - 1) <
            levelPhi W params.hk initStr moves i₁ ((a' - 1) + 1) := by
          rw [Nat.sub_add_cancel (by omega), ha'_eq]
          omega
        obtain ⟨adv_p, newStr_p, hm_p⟩ := shift_self_of_levelPhi_lt W params.hk initStr moves
          hpred_len (hpb_tail (a' - 1) (by omega) (by omega)) hpred_lt
        rw [show a' = (a' - 1) + 1 by omega, passesAt_succ W params.hk initStr moves hpred_len, hm_p]
        simp [stepPasses, hi']
    by_cases htop : i₁.val < params.d
    · have hpres_i₁ : ∀ t, a' ≤ t → (ht2 : t < u_end) →
          PreservesUpTo i₁ (moves[t]'(lt_of_lt_of_le ht2 (le_trans (le_of_lt hu_end2) hblen))) := by
        intro t ht1 ht2
        have hp := hpb_tail t (by omega) (by omega)
        refine ⟨hp.1, fun i₀ adv newStr hm => ?_⟩
        have hge := hp.2 i₀ adv newStr hm
        rcases eq_or_lt_of_le hge with rfl | hgt
        · exfalso
          have hlen_t : t < moves.length := lt_of_lt_of_le ht2 (le_trans (le_of_lt hu_end2) hblen)
          have hinc := levelPhi_shift_self W params.hk initStr moves i₁ hlen_t hm
          have hc1 := hphi_const t ht1 (le_of_lt ht2)
          have hc2 := hphi_const (t + 1) (by omega) ht2
          omega
        · exact hgt
      have hu_end_passes_gt : ∀ i' : Fin (params.d + 1), i₁ < i' →
          P ≤ passesAt W params.hk initStr moves u_end i' := by
        rcases hu_end_shift with ⟨newStr_e, hm_e⟩
        exact (shift_step_strategy_props params hv hf hu_end_len hm_e).2.2
      obtain ⟨s, hs1, hs2, hs_shift, hs_props⟩ := ih i₁ htop (by
          change params.d - (i.val + 1) = r; omega) a' u_end
        ha'2 (le_trans (le_of_lt hu_end2) hblen) hpres_i₁ ha'_passes_gt hu_end_passes_gt
      refine ⟨s, by omega, by omega, hs_shift, fun i' hi' => ?_⟩
      have hi'_ge : i₁ ≤ i' := Fin.le_iff_val_le_val.mpr (show i.val + 1 ≤ i'.val from hi')
      rcases eq_or_lt_of_le hi'_ge with rfl | hi₁_lt
      · exact hi₁_props s hs1 (le_of_lt hs2)
      · exact hs_props i' hi₁_lt
    · rcases hu_end_shift with ⟨newStr_e, hm_e⟩
      refine ⟨u_end, by omega, hu_end2,
        ⟨i₁, newStr_e, by rw [List.getElem?_eq_getElem hu_end_len, hm_e]⟩, fun i' hi' => ?_⟩
      have hi'_eq : i' = i₁ := by
        ext
        have h1 : i.val < i'.val := hi'
        have h2 : i'.val < params.d + 1 := i'.isLt
        have h3 : i₁.val < params.d + 1 := i₁.isLt
        change i.val + 1 < params.d + 1 at h3
        change ¬ i.val + 1 < params.d at htop
        show i'.val = i.val + 1
        omega
      subst hi'_eq
      exact hi₁_props u_end ha'2 le_rfl

/-- **Lemma 7.5** (page 36).
Let `s₁ < s₂` be two consecutive shifts at level `i < d` with no rebuild or shift at any level
`≤ i` in `(s₁, s₂)`. Then there exists a step `s` with `s₁ < s ≤ s₂` (in fact `s < s₂`)
such that at the start of step `s`, every level `i' > i` has current stretch `≤ σ` and
`passes_{i'} = ⌈2Ψ⌉ - 1` (which equals `2Ψ - 1` when `2Ψ` is an integer). -/
theorem lemma_7_5 (params : GameParams) {W : ℕ → ℝ}
    {initStr : Fin (params.d + 1) → Fin params.k → ℝ} {moves : List (Move params.d params.k)}
    (hv : ValidPlayPrefix params W initStr moves)
    (hf : FollowsStrategyPrefix params W initStr moves)
    {i : Fin (params.d + 1)} (hi : i.val < params.d)
    {s₁ s₂ : ℕ} (hs₁₂ : s₁ < s₂) (hs₂ : s₂ < moves.length)
    {adv₁ adv₂ : RoundChoice} {newStr₁ newStr₂ : Fin (params.d + 1) → Fin params.k → ℝ}
    (hm₁ : moves[s₁] = .roundStep adv₁ (.shift i) newStr₁)
    (hm₂ : moves[s₂] = .roundStep adv₂ (.shift i) newStr₂)
    (hnorest : ∀ s, s₁ < s → (hs2' : s < s₂) →
      PreservesUpTo i (moves[s]'(lt_trans hs2' hs₂))) :
    ∃ s, s₁ < s ∧ s ≤ s₂ ∧
      ∀ i' : Fin (params.d + 1), i < i' →
        (stateAt W params.hk initStr moves s).str i'
          ((stateAt W params.hk initStr moves s).bran i') ≤ params.σ ∧
        passesAt W params.hk initStr moves s i' = Nat.ceil (2 * params.Ψ) - 1 := by
  have hs₁ : s₁ < moves.length := lt_trans hs₁₂ hs₂
  have ha0 : ∀ i' : Fin (params.d + 1), i < i' →
      passesAt W params.hk initStr moves (s₁ + 1) i' = 0 := by
    intro i' hi'
    rw [passesAt_succ W params.hk initStr moves hs₁, hm₁]
    exact ((state_passes_shift W params.hk _ _ adv₁ i newStr₁).1 i' hi').2.2.2
  have hbP : ∀ i' : Fin (params.d + 1), i < i' →
      Nat.ceil (2 * params.Ψ) ≤ passesAt W params.hk initStr moves s₂ i' :=
    (shift_step_strategy_props params hv hf hs₂ hm₂).2.2
  obtain ⟨s, hs1, hs2, _, hsprops⟩ := lemma_7_5_interval params hv hf (params.d - i.val) i
    hi rfl (s₁ + 1) s₂ hs₁₂ (le_of_lt hs₂)
    (fun s h1 h2 => hnorest s h1 h2) ha0 hbP
  exact ⟨s, by omega, le_of_lt hs2, hsprops⟩

end

end MinCostFlow.Game
