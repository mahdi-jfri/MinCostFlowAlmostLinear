module

public import MinCostFlow.Chain.Ordered.Algorithm2
import Mathlib.Tactic

/-!
# The shift loop of Algorithm 2 runs at most `(⌈2 Ψ_g⌉ k + 1)^{d+1}` steps in one call

The inner loop of Algorithm 2 (`algorithm2_loopWith`, page 29) shifts the largest level `i` whose
counter `passes i` is below `2 Ψ_g`. A shift at level `i` advances the branch of level `i`, adds
one to `passes i` when the branch wraps around to `0`, and resets the counters and branches of
the levels above `i` to `0`. The pair (`passes j`, branch of level `j`) thus behaves like one
digit `passes j · k + (branch j mod k)` of a counter: a shift at level `i` adds one to digit `i`
and sets the digits above `i` to `0`, and level `i` can be shifted only while its digit is below
`C = ⌈2 Ψ_g⌉ k`.

So the loop runs at most as many steps as such a counter can count. We measure what is left by

  `loopOdometer = Σ_{j ≤ d} (C - digit j) · (C + 1)^{d - j}`,

which each shift lowers by at least one (`loopOdometer_shift_lt`) and which is below
`(C + 1)^{d+1}` (`loopOdometer_lt_pow`). The branch of level `d` is the counter `branD` of
Algorithm 2.

This bound is what makes the space of one call of `Update` polynomial: each loop step may
allocate memory, and the unused shift quota, the other bound on the number of steps, can grow
without bound over a run.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

/-! ## A counter with digits below `C` -/

/-- Lower digits of the counter: `Σ_{j ∈ [a, d]} C (C + 1)^{d - j} + 1 = (C + 1)^{d + 1 - a}`. -/
theorem odometer_geom (C d : ℕ) :
    ∀ t a, a + t = d + 1 →
      (∑ j ∈ Finset.Ico a (d + 1), C * (C + 1) ^ (d - j)) + 1 = (C + 1) ^ (d + 1 - a) := by
  intro t
  induction t with
  | zero =>
    intro a ha
    have : a = d + 1 := by omega
    subst this
    simp
  | succ t ih =>
    intro a ha
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), Nat.add_assoc, ih (a + 1) (by omega)]
    have h1 : d - a = d + 1 - (a + 1) := by omega
    have h2 : d + 1 - a = (d + 1 - (a + 1)) + 1 := by omega
    rw [h1, h2, pow_succ]
    ring

/-- One step of the counter. If digit `i` is below `C` and goes up by one, the digits below `i`
stay and the digits above `i` drop to `0`, then `Σ_{j ≤ d} (C - digit j) (C + 1)^{d - j}` drops
by at least one. -/
theorem odometer_step (C d i : ℕ) (hi : i ≤ d) (f g : ℕ → ℕ)
    (hlt : ∀ j < i, g j = f j) (hi1 : g i = f i + 1) (hC : f i + 1 ≤ C)
    (hgt : ∀ j, i < j → j ≤ d → g j = 0) :
    (∑ j ∈ Finset.range (d + 1), (C - g j) * (C + 1) ^ (d - j)) + 1 ≤
      ∑ j ∈ Finset.range (d + 1), (C - f j) * (C + 1) ^ (d - j) := by
  have hsplit : ∀ h : ℕ → ℕ, ∑ j ∈ Finset.range (d + 1), (C - h j) * (C + 1) ^ (d - j) =
      (∑ j ∈ Finset.range i, (C - h j) * (C + 1) ^ (d - j)) +
        ((C - h i) * (C + 1) ^ (d - i) +
          ∑ j ∈ Finset.Ico (i + 1) (d + 1), (C - h j) * (C + 1) ^ (d - j)) := by
    intro h
    rw [← Finset.sum_range_add_sum_Ico _ (show i ≤ d + 1 by omega),
      Finset.sum_eq_sum_Ico_succ_bot (show i < d + 1 by omega)]
  rw [hsplit g, hsplit f]
  have hlow : ∑ j ∈ Finset.range i, (C - g j) * (C + 1) ^ (d - j) =
      ∑ j ∈ Finset.range i, (C - f j) * (C + 1) ^ (d - j) :=
    Finset.sum_congr rfl fun j hj => by rw [hlt j (Finset.mem_range.mp hj)]
  have hhigh : ∑ j ∈ Finset.Ico (i + 1) (d + 1), (C - g j) * (C + 1) ^ (d - j) =
      ∑ j ∈ Finset.Ico (i + 1) (d + 1), C * (C + 1) ^ (d - j) :=
    Finset.sum_congr rfl fun j hj => by
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hj
      rw [hgt j (by omega) (by omega), Nat.sub_zero]
  have hgeom := odometer_geom C d (d - i) (i + 1) (by omega)
  have hexp : d + 1 - (i + 1) = d - i := by omega
  rw [hexp] at hgeom
  rw [hlow, hhigh, hi1]
  have hci : C - (f i + 1) + 1 = C - f i := by omega
  have hmul : (C - (f i + 1)) * (C + 1) ^ (d - i) + (C + 1) ^ (d - i) =
      (C - f i) * (C + 1) ^ (d - i) := by rw [← hci, add_mul, one_mul]
  omega

/-- The counter is below `(C + 1)^{d + 1}`. -/
theorem odometer_lt_pow (C d : ℕ) (f : ℕ → ℕ) :
    (∑ j ∈ Finset.range (d + 1), (C - f j) * (C + 1) ^ (d - j)) + 1 ≤ (C + 1) ^ (d + 1) := by
  have hgeom := odometer_geom C d (d + 1) 0 (by omega)
  rw [Nat.sub_zero, ← Finset.range_eq_Ico] at hgeom
  rw [← hgeom]
  exact Nat.add_le_add_right (Finset.sum_le_sum fun j _ =>
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)) 1

/-! ## The counter of the shift loop -/

/-- The bound on a digit of the shift-loop counter: `⌈2 Ψ_g⌉ k`. -/
noncomputable def loopDigitCap (cfg : Alg2Config) : ℕ :=
  ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ * cfg.P.k

/-- Digit `j` of the shift-loop counter: `passes j · k + (branch j mod k)`, where the branch of
level `d` is `branD`, and digits above `d` are `0`. -/
noncomputable def loopDigit (cfg : Alg2Config) (ch : ChainState cfg.T cfg.P) (branD : ℕ)
    (passes : Fin (cfg.P.d + 1) → ℕ) (j : ℕ) : ℕ :=
  if h : j < cfg.P.d + 1 then
    passes ⟨j, h⟩ * cfg.P.k + (if j < cfg.P.d then ch.bran j else branD) % cfg.P.k
  else 0

/-- What is left of the shift-loop counter: `Σ_{j ≤ d} (C - digit j) (C + 1)^{d - j}` with
`C = loopDigitCap cfg`. -/
noncomputable def loopOdometer (cfg : Alg2Config) (ch : ChainState cfg.T cfg.P) (branD : ℕ)
    (passes : Fin (cfg.P.d + 1) → ℕ) : ℕ :=
  ∑ j ∈ Finset.range (cfg.P.d + 1),
    (loopDigitCap cfg - loopDigit cfg ch branD passes j) * (loopDigitCap cfg + 1) ^ (cfg.P.d - j)

/-- **The counter is below `(⌈2 Ψ_g⌉ k + 1)^{d+1}`.** -/
theorem loopOdometer_lt_pow (cfg : Alg2Config) (ch : ChainState cfg.T cfg.P) (branD : ℕ)
    (passes : Fin (cfg.P.d + 1) → ℕ) :
    loopOdometer cfg ch branD passes + 1 ≤ (loopDigitCap cfg + 1) ^ (cfg.P.d + 1) :=
  odometer_lt_pow _ _ _

private theorem rebuildSuffix_bran (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State)
      (bran upd cEnc cDec cFwd : ℕ → ℕ) (k : ℕ),
      (rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd).2.2.1 k =
        if idx ≤ k ∧ k < idx + rem then 0 else bran k
  | 0, idx, _, _, _, _, _, _, _, k => by
    have h : ¬ (idx ≤ k ∧ k < idx + 0) := by omega
    simp only [h, ite_false]
    rfl
  | rem + 1, idx, G, sc, bran, upd, cEnc, cDec, cFwd, k => by
    dsimp only [rebuildSuffix]
    rw [rebuildSuffix_bran T L P lvlM N₀ ℓ₀ g₀ rem (idx + 1) _ _ _ _ _ _ _ k]
    split_ifs <;> first | rfl | omega

/-- After a shift at level `i < d`, the branches of the levels below `i` stay, the branch of
level `i` is `(bran i + 1) mod k`, and the branches of the levels above `i` are `0`. -/
theorem algorithm1_shift_bran (T : SparseCoreRestartTool) (L : LastLevelTool) (P : ChainParams)
    (ch : ChainState T P) {i : ℕ} (hi : i < P.d) (j : ℕ) :
    (algorithm1_shift T L P ch i).1.bran j =
      if j < i then ch.bran j
      else if j = i then (ch.bran i + 1) % P.k
      else if j < P.d then 0 else ch.bran j := by
  dsimp only [algorithm1_shift]
  rw [dite_eq_left hi]
  dsimp only
  rw [rebuildSuffix_bran]
  split_ifs <;> first | rfl | omega

/-- A shift at level `d` keeps all branches of the chain. -/
theorem algorithm1_shift_bran_top (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (ch : ChainState T P) {i : ℕ} (hi : ¬ i < P.d) :
    (algorithm1_shift T L P ch i).1.bran = ch.bran := by
  dsimp only [algorithm1_shift]
  rw [dite_eq_right hi]

private theorem digit_succ (p b k : ℕ) (hk : 0 < k) :
    (if (b + 1) % k = 0 then p + 1 else p) * k + (b + 1) % k % k = p * k + b % k + 1 := by
  rcases Nat.eq_or_lt_of_le hk with h1 | h1
  · subst h1
    simp [Nat.mod_one]
  · rw [Nat.mod_mod, Nat.add_mod b 1 k, Nat.mod_eq_of_lt h1]
    have hb := Nat.mod_lt b hk
    rcases Nat.lt_or_ge (b % k + 1) k with h | h
    · rw [Nat.mod_eq_of_lt h, ite_eq_right (by omega)]
      ring
    · have heq : b % k + 1 = k := by omega
      rw [heq, Nat.mod_self, ite_eq_left rfl, Nat.add_mul, one_mul]
      omega

/-- **A shift lowers the counter.** If level `i` is the eligible level of the shift loop
(`findEligibleLevel`), then the counter after the shift that the loop performs at level `i` is
below the counter before it. -/
theorem loopOdometer_shift_lt (cfg : Alg2Config) (ch : ChainState cfg.T cfg.P) (branD : ℕ)
    (passes : Fin (cfg.P.d + 1) → ℕ) (i : Fin (cfg.P.d + 1))
    (hElig : findEligibleLevel cfg.P.d (alg2PsiGame cfg.Ψ cfg.P.M₀) passes = some i) :
    let curB := if i.val < cfg.P.d then ch.bran i.val else branD
    let wrapped := (curB + 1) % cfg.P.k = 0
    let ch' := (algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1
    let branD' := if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k
    let passes' : Fin (cfg.P.d + 1) → ℕ := fun j =>
      if i < j then 0
      else if j = i then (if wrapped then passes i + 1 else passes i)
      else passes j
    loopOdometer cfg ch' branD' passes' < loopOdometer cfg ch branD passes := by
  intro curB wrapped ch' branD' passes'
  have hk := cfg.P.hk
  have hiLe : i.val ≤ cfg.P.d := Nat.lt_succ_iff.mp i.isLt
  -- digit `i` is below the cap, since `passes i < 2 Ψ_g`
  have hpass : passes i + 1 ≤ ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ := by
    have h := (findEligibleLevel_spec hElig).1
    have : passes i < ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ := by
      exact_mod_cast lt_of_lt_of_le h (Nat.le_ceil _)
    omega
  have hdi : loopDigit cfg ch branD passes i.val = passes i * cfg.P.k + curB % cfg.P.k := by
    unfold loopDigit; rw [dite_eq_left i.isLt]
  have hC : loopDigit cfg ch branD passes i.val + 1 ≤ loopDigitCap cfg := by
    rw [hdi]
    unfold loopDigitCap
    have := Nat.mod_lt curB hk
    nlinarith
  apply Nat.lt_of_succ_le
  apply odometer_step _ _ i.val hiLe
  · -- the digits below `i` stay
    intro j hj
    have hjd : j < cfg.P.d + 1 := by omega
    unfold loopDigit
    rw [dite_eq_left hjd, dite_eq_left hjd]
    have hji : ¬ i < (⟨j, hjd⟩ : Fin (cfg.P.d + 1)) := fun h => by
      have h' := Fin.lt_def.mp h
      simp only at h'
      omega
    have hjne : (⟨j, hjd⟩ : Fin (cfg.P.d + 1)) ≠ i := by
      intro h; rw [← h] at hj; simp at hj
    have hjD : j < cfg.P.d := by omega
    simp only [passes', hji, hjne, ite_false, ite_eq_left hjD]
    have hb : ch'.bran j = ch.bran j := by
      by_cases hiD : i.val < cfg.P.d
      · rw [algorithm1_shift_bran _ _ _ _ hiD, ite_eq_left hj]
      · rw [algorithm1_shift_bran_top _ _ _ _ hiD]
    rw [hb]
  · -- digit `i` goes up by one
    rw [hdi]
    unfold loopDigit
    rw [dite_eq_left i.isLt]
    simp only [passes', lt_irrefl, ite_false, ite_true]
    by_cases hiD : i.val < cfg.P.d
    · have hb : ch'.bran i.val = (ch.bran i.val + 1) % cfg.P.k := by
        rw [algorithm1_shift_bran _ _ _ _ hiD, ite_eq_right (lt_irrefl _), ite_eq_left rfl]
      have hcur : curB = ch.bran i.val := ite_eq_left hiD
      simp only [ite_eq_left hiD, hb, wrapped, hcur]
      exact digit_succ _ _ _ hk
    · have hcur : curB = branD := ite_eq_right hiD
      simp only [ite_eq_right hiD, branD', wrapped, hcur]
      exact digit_succ _ _ _ hk
  · exact hC
  · -- the digits above `i` drop to `0`
    intro j hj hjd
    have hjd' : j < cfg.P.d + 1 := by omega
    unfold loopDigit
    rw [dite_eq_left hjd']
    have hij : i < (⟨j, hjd'⟩ : Fin (cfg.P.d + 1)) := by rw [Fin.lt_def]; exact hj
    simp only [passes', ite_eq_left hij, zero_mul, zero_add]
    have hiD : i.val < cfg.P.d := by omega
    by_cases hjD : j < cfg.P.d
    · rw [ite_eq_left hjD, algorithm1_shift_bran _ _ _ _ hiD, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left hjD, Nat.zero_mod]
    · rw [ite_eq_right hjD]
      simp only [branD', ite_eq_left hiD, Nat.zero_mod]

end MinCostFlow.Chain.Ordered
