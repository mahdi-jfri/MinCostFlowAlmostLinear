module

public import MinCostFlow.LowStretch.ProgLog
public import MinCostFlow.LowStretch.Arcs

/-!
# The rounded cost of an arc, by a binary search on the exponent

The petal graph rounds the shifted length `x ≥ 1` of a pair to `rc θ x = max θ 2^⌈log₂ 2x⌉`,
with `θ = 2^lθ`. So `rc θ x = 2^(lθ + e)` for the least `e` with `2x ≤ 2^(lθ + e)`
(`rc_eq_pow`). There are at most `J` such exponents, and `clogP` finds `e` by a binary search in
`O(log J)` steps (`clogP_spec`). A plain doubling loop would take `O(log n)` steps for each pair,
which the count does not allow.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The rounded cost is the power of two of the least good exponent. -/
theorem rc_eq_pow {lθ x e : ℕ} (hx : 1 ≤ x) (h1 : 2 * x ≤ 2 ^ (lθ + e))
    (h2 : e = 0 ∨ 2 ^ (lθ + e - 1) < 2 * x) : rc (2 ^ lθ) x = 2 ^ (lθ + e) := by
  unfold rc
  rw [if_neg (by omega)]
  have hc : Nat.clog 2 (2 * x) ≤ lθ + e := Nat.clog_le_of_le_pow h1
  rcases h2 with rfl | h2
  · rw [Nat.add_zero] at hc ⊢
    exact max_eq_left (Nat.pow_le_pow_right (by norm_num) hc)
  · have hc2 : lθ + e ≤ Nat.clog 2 (2 * x) := by
      have : lθ + e - 1 < Nat.clog 2 (2 * x) := Nat.lt_clog_iff_pow_lt (by norm_num) |>.mpr h2
      omega
    have e1 : Nat.clog 2 (2 * x) = lθ + e := le_antisymm hc hc2
    rw [e1]
    exact max_eq_right (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- `clogP`: `args = [lθ, x, J]`. -/
def clogP : Stmt :=
  .seq (.assign 3 (.const 0))
  (.seq (.assign 4 (.reg 2))
  (.seq (.loop (.bin .lt (.bin .add (.reg 3) (.const 1)) (.reg 4))
      (.seq (.assign 5 (.bin .add (.reg 3) (.bin .div (.bin .sub (.reg 4) (.reg 3)) (.const 2))))
        (.cond (.bin .lt (.const 0) (.bin .shiftRight
            (.bin .sub (.bin .add (.reg 1) (.reg 1)) (.const 1))
            (.bin .sub (.bin .add (.reg 0) (.reg 5)) (.const 1))))
          (.assign 3 (.reg 5)) (.assign 4 (.reg 5)))))
  (.ret (.bin .sub (.reg 4) (.const 1)))))

theorem clogP_noRand : clogP.NoRand := by simp [clogP, Stmt.NoRand]

/-- The contract of `clogP`. -/
def clogC (w : ℕ) : Contract where
  pre args _ := ∃ lθ x J, args = [lθ, x, J] ∧ 1 ≤ x ∧ 2 * x < 2 ^ w ∧ lθ + J < 2 ^ w ∧
    1 ≤ J ∧ 2 * x ≤ 2 ^ (lθ + (J - 1))
  post args mem v mem' := mem' = mem ∧ ∀ lθ x J, args = [lθ, x, J] →
    v < J ∧ 2 * x ≤ 2 ^ (lθ + v) ∧ (v = 0 ∨ 2 ^ (lθ + v - 1) < 2 * x)
  cost args _ := 40 * Nat.clog 2 (args.getD 2 0) + 40

/-- `(2x - 1) >>> k = 0` says `2x ≤ 2^k`. -/
theorem shr_zero_iff {x k : ℕ} (hx : 1 ≤ x) : (2 * x - 1) >>> k = 0 ↔ 2 * x ≤ 2 ^ k := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact absurd h (Nat.two_pow_pos k).ne'
    · omega
  · intro h; right; omega

theorem clogP_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [clogP]) :
    MeetsContract w p b (clogC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨lθ, x, J, rfl, hx1, hxw, hlJ, hJ1, hP⟩ := hpre
  have hproc : p.procs[b]? = some clogP := hp 0 (by simp)
  -- `P e` says that `e` is a good exponent
  let Inv : State → Prop := fun st => st.regs 0 = lθ ∧ st.regs 1 = x ∧ st.mem = mem ∧
    st.regs 3 < st.regs 4 ∧ st.regs 4 ≤ J ∧
    (st.regs 3 = 0 ∨ 2 ^ (lθ + (st.regs 3 - 1)) < 2 * x) ∧ 2 * x ≤ 2 ^ (lθ + (st.regs 4 - 1))
  have hloop : Triple w p Inv
      (.loop (.bin .lt (.bin .add (.reg 3) (.const 1)) (.reg 4))
        (.seq (.assign 5 (.bin .add (.reg 3) (.bin .div (.bin .sub (.reg 4) (.reg 3)) (.const 2))))
          (.cond (.bin .lt (.const 0) (.bin .shiftRight
              (.bin .sub (.bin .add (.reg 1) (.reg 1)) (.const 1))
              (.bin .sub (.bin .add (.reg 0) (.reg 5)) (.const 1))))
            (.assign 3 (.reg 5)) (.assign 4 (.reg 5)))))
      (normalPost fun st => Inv st ∧ st.regs 4 = st.regs 3 + 1)
      (fun st => (5 + 25 + 1) * Nat.clog 2 (st.regs 4 - st.regs 3) + 5 + 1) := by
    refine Triple.loop_const_normal (fun st => Nat.clog 2 (st.regs 4 - st.regs 3))
      (fun st => if st.regs 3 + 1 < st.regs 4 then 1 else 0) 25
      (fun st hI => by
        obtain ⟨-, -, -, h34, h4J, -, -⟩ := hI
        eval_expr)
      (fun st hI h0 => ⟨hI, by
        obtain ⟨-, -, -, h34, -, -, -⟩ := hI
        simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_lt] at h0
        omega⟩)
      (fun st hI hne => ?_)
    obtain ⟨h0, h1, hm, h34, h4J, hlo, hhi⟩ := hI
    simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne
    have hmid1 : st.regs 3 < (st.regs 3 + (st.regs 4 - st.regs 3) / 2) := by omega
    have hmid2 : (st.regs 3 + (st.regs 4 - st.regs 3) / 2) < st.regs 4 := by omega
    have hsh : (st.regs 1 + st.regs 1 - 1) >>> (st.regs 0 + (st.regs 3 + (st.regs 4 - st.regs 3) / 2) - 1) < 2 ^ w :=
      lt_of_le_of_lt (shr_le _ _) (by rw [h1]; omega)
    have ha : st.regs 1 + st.regs 1 < 2 ^ w := by rw [h1]; omega
    have hb : st.regs 0 + (st.regs 3 + (st.regs 4 - st.regs 3) / 2) < 2 ^ w := by rw [h0]; omega
    wram_enter
    · subst hpre
      wram_step
      wram_step
      · -- `(st.regs 3 + (st.regs 4 - st.regs 3) / 2) - 1` is not good: the lower end moves up
        have hng : ¬ 2 * x ≤ 2 ^ (lθ + ((st.regs 3 + (st.regs 4 - st.regs 3) / 2) - 1)) := by
          rw [← shr_zero_iff hx1]
          rw [h0, h1] at hcond
          rw [show 2 * x - 1 = x + x - 1 by omega, show lθ + ((st.regs 3 + (st.regs 4 - st.regs 3) / 2) - 1) = lθ + (st.regs 3 + (st.regs 4 - st.regs 3) / 2) - 1 by omega]
          intro h; rw [h] at hcond; exact absurd hcond (lt_irrefl 0)
        wram_step
        · refine ⟨⟨by simp [h0], by simp [h1], by simp [hm], by simp; omega, by simp; omega,
            ?_, by simpa using hhi⟩, ?_⟩
          · simp (config := { decide := true }) only [Function.update_apply, ite_true, ite_false]
            right; omega
          · simp (config := { decide := true }) only [Function.update_apply, ite_true, ite_false]
            exact clog_half (by omega) (by omega)
        · wram_cost
      · -- `(st.regs 3 + (st.regs 4 - st.regs 3) / 2) - 1` is good: the upper end moves down
        have hg : 2 * x ≤ 2 ^ (lθ + ((st.regs 3 + (st.regs 4 - st.regs 3) / 2) - 1)) := by
          rw [← shr_zero_iff hx1]
          rw [h0, h1] at hcond
          rw [show 2 * x - 1 = x + x - 1 by omega, show lθ + ((st.regs 3 + (st.regs 4 - st.regs 3) / 2) - 1) = lθ + (st.regs 3 + (st.regs 4 - st.regs 3) / 2) - 1 by omega]
          exact Nat.eq_zero_of_not_pos hcond
        wram_step
        · refine ⟨⟨by simp [h0], by simp [h1], by simp [hm], by simp; omega, by simp; omega,
            by simpa using hlo, by simpa using hg⟩, ?_⟩
          simp (config := { decide := true }) only [Function.update_apply, ite_true, ite_false]
          exact clog_half (by omega) (by omega)
        · wram_cost
  refine ⟨clogP, hproc, ?_⟩
  dsimp only [clogP]
  refine runs_start_le ?_
  wram_step
  wram_step
  refine runs_seq_triple_le hloop ⟨by simp [startState], by simp [startState], rfl,
    by simp [startState]; omega, by simp [startState], by simp, by simpa [startState] using hP⟩
    (fun st1 h1 => ?_)
  obtain ⟨⟨h10, h11, h1m, h134, h14J, hlo, hhi⟩, he⟩ := h1
  have hb : st1.regs 4 - 1 < 2 ^ w := by omega
  refine runs_ret_le (by eval_expr) ⟨h1m, fun lθ' x' J' hargs => ?_⟩ ?_
  · simp only [List.cons.injEq] at hargs
    obtain ⟨rfl, rfl, rfl, -⟩ := hargs
    simp only [Outcome.value]
    refine ⟨by omega, by rw [he] at hhi; simpa using hhi, ?_⟩
    by_cases h3 : st1.regs 3 = 0
    · left; omega
    · rcases hlo with h | h
      · omega
      · right
        rw [show lθ + (st1.regs 3 + 1 - 1) - 1 = lθ + (st1.regs 3 - 1) by omega]
        exact h
  · simp only [clogC, List.getD_cons_succ, List.getD_cons_zero, startState]
    simp (config := { decide := true }) only [Function.update_apply, ite_true, ite_false,
      Nat.sub_zero] at *
    wram_cost

/-! ### The class of a rounded cost -/

/-- The exponent of the rounded cost above `θ = 2^lθ`. -/
def rcE (lθ x : ℕ) : ℕ := Nat.clog 2 (2 * x) - lθ

/-- The class of the rounded cost of `x`: `0` for `x = 0`, and `rcE + 2` otherwise. -/
def rcK (lθ x : ℕ) : ℕ := if x = 0 then 0 else rcE lθ x + 2

/-- The cost of class `k`: `0` for `k = 0`, and `2^(lθ + k - 2)` otherwise. -/
def cofK (lθ k : ℕ) : ℕ := if k = 0 then 0 else 2 ^ (lθ + k - 2)

/-- The exponent that `clogP` returns is `rcE`. -/
theorem eq_rcE {lθ x v : ℕ} (hx : 1 ≤ x) (h1 : 2 * x ≤ 2 ^ (lθ + v))
    (h2 : v = 0 ∨ 2 ^ (lθ + v - 1) < 2 * x) : v = rcE lθ x := by
  unfold rcE
  have hc : Nat.clog 2 (2 * x) ≤ lθ + v := Nat.clog_le_of_le_pow h1
  rcases h2 with rfl | h2
  · omega
  · have : lθ + v - 1 < Nat.clog 2 (2 * x) := Nat.lt_clog_iff_pow_lt (by norm_num) |>.mpr h2
    omega

/-- The class gives the rounded cost. -/
theorem cofK_rcK (lθ x : ℕ) : cofK lθ (rcK lθ x) = rc (2 ^ lθ) x := by
  unfold cofK rcK
  by_cases hx : x = 0
  · simp [hx, rc]
  · rw [if_neg hx, if_neg (by omega)]
    have hx1 : 1 ≤ x := by omega
    have h1 : 2 * x ≤ 2 ^ (lθ + rcE lθ x) := by
      unfold rcE
      calc 2 * x ≤ 2 ^ Nat.clog 2 (2 * x) := Nat.le_pow_clog (by norm_num) _
        _ ≤ 2 ^ (lθ + (Nat.clog 2 (2 * x) - lθ)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : rcE lθ x = 0 ∨ 2 ^ (lθ + rcE lθ x - 1) < 2 * x := by
      by_cases h0 : rcE lθ x = 0
      · exact Or.inl h0
      · right
        unfold rcE at h0 ⊢
        have : lθ + (Nat.clog 2 (2 * x) - lθ) - 1 < Nat.clog 2 (2 * x) := by omega
        exact (Nat.lt_clog_iff_pow_lt (by norm_num)).mp this
    rw [rc_eq_pow hx1 h1 h2, show lθ + (rcE lθ x + 2) - 2 = lθ + rcE lθ x by omega]

/-- `rclsP bC`: `args = [lθ, x, J']`, returns `rcK lθ x`. Procedure `bC` is `clogP`. -/
def rclsP (bC : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.seq (.call 3 bC [.reg 0, .reg 1, .reg 2]) (.ret (.bin .add (.reg 3) (.const 2))))

theorem rclsP_noRand (bC : ℕ) : (rclsP bC).NoRand := by simp [rclsP, Stmt.NoRand]

/-- The contract of `rclsP`. -/
def rclsC (w : ℕ) : Contract where
  pre args _ := ∃ lθ x J, args = [lθ, x, J] ∧ 2 * x < 2 ^ w ∧ lθ + J + 2 < 2 ^ w ∧
    1 ≤ J ∧ 2 * x ≤ 2 ^ (lθ + (J - 1))
  post args mem v mem' := mem' = mem ∧ ∀ lθ x J, args = [lθ, x, J] → v = rcK lθ x ∧ v < J + 2
  cost args _ := 40 * Nat.clog 2 (args.getD 2 0) + 60

theorem rclsP_spec {w : ℕ} {p : Program} {b bC : ℕ} (hp : p.HasAt b [rclsP bC])
    (hC : MeetsContract w p bC (clogC w)) : MeetsContract w p b (rclsC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨lθ, x, J, rfl, hxw, hlJ, hJ1, hP⟩ := hpre
  have hproc : p.procs[b]? = some (rclsP bC) := hp 0 (by simp)
  refine ⟨rclsP bC, hproc, ?_⟩
  dsimp only [rclsP]
  refine runs_start_le ?_
  by_cases hx : x = 0
  · subst hx
    wram_run
    all_goals first
      | (show mem = mem ∧ _
         refine ⟨rfl, fun lθ' x' J' he => ?_⟩
         simp only [List.cons.injEq] at he
         obtain ⟨rfl, rfl, rfl, -⟩ := he
         exact ⟨by simp [rcK, Outcome.value], by simp [Outcome.value]⟩)
      | (simp only [rclsC, List.getD_cons_succ, List.getD_cons_zero]; wram_cost)
      | (simp [startState] at *)
  · have hx1 : 1 ≤ x := by omega
    wram_run
    all_goals first
      | (simp [startState] at *; omega)
      | (exact ⟨lθ, x, J, by simp [startState], hx1, by omega, by omega, hJ1, hP⟩)
      | (intro v mem' pos' hpost
         obtain ⟨hm, hv⟩ := hpost
         obtain ⟨hvJ, h1, h2⟩ := hv lθ x J (by simp [startState])
         have hve := eq_rcE hx1 h1 h2
         subst hm
         wram_run
         · refine ⟨rfl, fun lθ' x' J' he => ?_⟩
           simp only [List.cons.injEq] at he
           obtain ⟨rfl, rfl, rfl, -⟩ := he
           refine ⟨?_, ?_⟩
           · simp [rcK, hx, hve, Outcome.value]
           · simp only [Outcome.value]; omega
         · simp only [rclsC, clogC, List.getD_cons_succ, List.getD_cons_zero, startState]
           wram_cost)

end MinCostFlow.LowStretch
