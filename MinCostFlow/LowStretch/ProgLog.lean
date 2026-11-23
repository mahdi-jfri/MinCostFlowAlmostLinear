module

public import WordRAM.Logic
public import WordRAM.Tactic
public import Mathlib.Data.Nat.Log

/-!
# The binary logarithm of a word

The program rounds every weight `x` to the power of two `2^⌊log₂ x⌋`. It finds `⌊log₂ x⌋` in
`O(log(log x + 1) + 1)` steps, which is the cost that item 2 counts (`wsteps`). First it doubles
`k = 1, 2, 4, …` until `x < 2^k`. Then `x` lies in `[2^0, 2^k)`, and a binary search on the exponent
finds the `lo` with `2^lo ≤ x < 2^(lo + 1)` (`log2P_spec`). Both loops use the shift `x >>> k`,
which is `x / 2^k`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- `log2P`: `args = [x]`, returns `⌊log₂ x⌋` for `x ≥ 1`. -/
def log2P : Stmt :=
  .seq (.assign 1 (.const 1))
  (.seq (.loop (.bin .lt (.const 0) (.bin .shiftRight (.reg 0) (.reg 1)))
      (.assign 1 (.bin .add (.reg 1) (.reg 1))))
  (.seq (.assign 2 (.const 0))
  (.seq (.loop (.bin .lt (.bin .add (.reg 2) (.const 1)) (.reg 1))
      (.seq (.assign 3 (.bin .add (.reg 2) (.bin .div (.bin .sub (.reg 1) (.reg 2)) (.const 2))))
        (.cond (.bin .lt (.const 0) (.bin .shiftRight (.reg 0) (.reg 3)))
          (.assign 2 (.reg 3)) (.assign 1 (.reg 3)))))
  (.ret (.reg 2)))))

theorem log2P_noRand : log2P.NoRand := by simp [log2P, Stmt.NoRand]

/-- The cost of `log2P` on `x`. -/
def log2Cost (x : ℕ) : ℕ := 50 * (Nat.log 2 (Nat.log 2 x + 1) + 2)

/-- The contract of `log2P`. -/
def log2C (w : ℕ) : Contract where
  pre args _ := ∃ x, args = [x] ∧ 1 ≤ x ∧ x < 2 ^ w ∧ 2 ≤ w
  post args mem v mem' := v = Nat.log 2 (args.getD 0 0) ∧ mem' = mem
  cost args _ := log2Cost (args.getD 0 0)

theorem shr_pos_iff (x k : ℕ) : 0 < x >>> k ↔ 2 ^ k ≤ x := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_pos_iff]
  exact ⟨fun h => h.2, fun h => ⟨Nat.two_pow_pos k, h⟩⟩

theorem shr_le (x k : ℕ) : x >>> k ≤ x := by
  rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _

/-- The gap of the binary search halves, rounded up. -/
theorem clog_half {g g' : ℕ} (hg : 2 ≤ g) (h : g' ≤ (g + 1) / 2) :
    Nat.clog 2 g' < Nat.clog 2 g := by
  rw [Nat.clog_of_two_le (by norm_num) hg]
  have : Nat.clog 2 g' ≤ Nat.clog 2 ((g + 2 - 1) / 2) := Nat.clog_mono_right 2 (by omega)
  omega

theorem two_mul_le_two_pow (w : ℕ) : 2 * w ≤ 2 ^ w := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [pow_succ]
    have := Nat.one_le_two_pow (n := w)
    omega

theorem log2P_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [log2P]) :
    MeetsContract w p b (log2C w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨x, rfl, hx1, hxw, hw⟩ := hpre
  have hproc : p.procs[b]? = some log2P := hp 0 (by simp)
  have hlx : Nat.log 2 x < w := Nat.log_lt_of_lt_pow (by omega) hxw
  have hw2 : 2 * w ≤ 2 ^ w := two_mul_le_two_pow w
  set a := Nat.log 2 x with ha
  -- the first loop: doubling
  let Inv1 : State → Prop := fun st => ∃ i, st.regs 0 = x ∧ st.regs 1 = 2 ^ i ∧ st.mem = mem ∧
    (i = 0 ∨ 2 ^ 2 ^ (i - 1) ≤ x)
  have hloop1 : Triple w p Inv1
      (.loop (.bin .lt (.const 0) (.bin .shiftRight (.reg 0) (.reg 1)))
        (.assign 1 (.bin .add (.reg 1) (.reg 1))))
      (normalPost fun st => Inv1 st ∧ x < 2 ^ st.regs 1)
      (fun st => (5 + 4 + 1) * (Nat.log 2 a + 2 - Nat.log 2 (st.regs 1)) + 5 + 1) := by
    refine (Triple.loop_const_normal (fun st => Nat.log 2 a + 2 - Nat.log 2 (st.regs 1))
      (fun st => if 0 < st.regs 0 >>> st.regs 1 then 1 else 0) 4
      (fun st hI => by
        obtain ⟨i, h0, h1, -, -⟩ := hI
        have : st.regs 0 >>> st.regs 1 < 2 ^ w := lt_of_le_of_lt (shr_le _ _) (by omega)
        eval_expr)
      (fun st hI h0 => ⟨hI, by
        obtain ⟨i, h0', h1, -, -⟩ := hI
        simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_lt, Nat.le_zero] at h0
        rw [h0'] at h0
        by_contra hc
        push Not at hc
        have := (shr_pos_iff x _).mpr hc
        omega⟩)
      (fun st hI hne => ?_)).mono_cost (fun _ _ => le_rfl)
    obtain ⟨i, h0, h1, hm, hi⟩ := hI
    simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne
    rw [h0, h1] at hne
    have hle : 2 ^ 2 ^ i ≤ x := (shr_pos_iff x _).mp hne
    have hia : 2 ^ i ≤ a := Nat.le_log_of_pow_le (by norm_num) hle
    have hii : i ≤ Nat.log 2 a := Nat.le_log_of_pow_le (by norm_num) hia
    have hka : 2 ^ i + 2 ^ i < 2 ^ w := by omega
    wram_enter
    · subst hpre
      wram_step
      · refine ⟨⟨i + 1, by simp [h0], by simp [h1, pow_succ]; ring, by simp [hm], Or.inr ?_⟩, ?_⟩
        · simpa using hle
        · simp only [Function.update_self, h1]
          rw [show 2 ^ i + 2 ^ i = 2 ^ (i + 1) by ring, Nat.log_pow (by norm_num),
            Nat.log_pow (by norm_num)]
          omega
      · wram_cost
  -- the second loop: binary search
  let Inv2 : State → Prop := fun st => st.regs 0 = x ∧ st.mem = mem ∧ st.regs 2 < st.regs 1 ∧
    2 ^ st.regs 2 ≤ x ∧ x < 2 ^ st.regs 1 ∧ st.regs 1 ≤ 2 * a + 1
  have hnext : ∀ (st : State) (R : ℕ → ℕ) (M : ℕ → ℕ) (q : ℕ), M = mem → R 0 = x →
      R 2 < R 1 → 2 ^ R 2 ≤ x → x < 2 ^ R 1 → R 1 ≤ 2 * a + 1 →
      R 1 - R 2 ≤ (st.regs 1 - st.regs 2 + 1) / 2 → 2 ≤ st.regs 1 - st.regs 2 →
      Inv2 { mem := M, regs := R, pos := q } ∧
        Nat.clog 2 (R 1 - R 2) < Nat.clog 2 (st.regs 1 - st.regs 2) :=
    fun st R M q hM h0 h21 hlo hhi hk hg hg2 =>
      ⟨⟨h0, hM, h21, hlo, hhi, hk⟩, clog_half hg2 hg⟩
  have hloop2 : Triple w p Inv2
      (.loop (.bin .lt (.bin .add (.reg 2) (.const 1)) (.reg 1))
        (.seq (.assign 3 (.bin .add (.reg 2) (.bin .div (.bin .sub (.reg 1) (.reg 2)) (.const 2))))
          (.cond (.bin .lt (.const 0) (.bin .shiftRight (.reg 0) (.reg 3)))
            (.assign 2 (.reg 3)) (.assign 1 (.reg 3)))))
      (normalPost fun st => Inv2 st ∧ st.regs 1 = st.regs 2 + 1)
      (fun st => (5 + 20 + 1) * Nat.clog 2 (st.regs 1 - st.regs 2) + 5 + 1) := by
    refine Triple.loop_const_normal (fun st => Nat.clog 2 (st.regs 1 - st.regs 2))
      (fun st => if st.regs 2 + 1 < st.regs 1 then 1 else 0) 20
      (fun st hI => by
        obtain ⟨h0, -, h21, -, -, hk⟩ := hI
        eval_expr)
      (fun st hI h0 => ⟨hI, by
        obtain ⟨-, -, h21, -, -, -⟩ := hI
        simp only [ite_eq_right_iff, one_ne_zero, imp_false, not_lt] at h0
        omega⟩)
      (fun st hI hne => ?_)
    obtain ⟨h0, hm, h21, hlo, hhi, hk⟩ := hI
    simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne
    set mid := st.regs 2 + (st.regs 1 - st.regs 2) / 2 with hmid
    have hsh : x >>> mid < 2 ^ w := lt_of_le_of_lt (shr_le _ _) hxw
    have hsh' : st.regs 0 >>> mid < 2 ^ w := by rw [h0]; exact hsh
    wram_enter
    · subst hpre
      wram_step
      wram_step
      · -- `2^mid ≤ x`: the lower end moves up
        have hle : 2 ^ mid ≤ x := (shr_pos_iff x _).mp (by simpa [h0] using hcond)
        wram_step
        · exact hnext st _ _ _ hm (by simp [h0]) (by simp; omega) (by simpa using hle)
            (by simpa using hhi) (by simpa using hk) (by simp; omega) (by omega)
        · wram_cost
      · -- `x < 2^mid`: the upper end moves down
        have hlt : x < 2 ^ mid := by
          by_contra hc
          push Not at hc
          have := (shr_pos_iff x _).mpr hc
          rw [h0] at hcond
          exact hcond this
        wram_step
        · exact hnext st _ _ _ hm (by simp [h0]) (by simp; omega) (by simpa using hlo)
            (by simpa using hlt) (by simp; omega) (by simp; omega) (by omega)
        · wram_cost
  -- the whole procedure
  have htriple : Triple w p (fun st => st = startState [x] mem pos) log2P
      (fun o st' => o.value = Nat.log 2 x ∧ st'.mem = mem) (fun _ => log2Cost x) := by
    wram_enter
    · subst hpre
      dsimp only [log2P]
      wram_step
      refine runs_seq_triple_le hloop1 ⟨0, by simp [startState], by simp, rfl, Or.inl rfl⟩
        (fun st1 h1 => ?_)
      obtain ⟨⟨i, h10, h11, h1m, hi⟩, hx1'⟩ := h1
      have hk : st1.regs 1 ≤ 2 * a + 1 := by
        rw [h11]
        rcases hi with rfl | hi
        · simp
        · rcases Nat.eq_zero_or_pos i with rfl | hipos
          · simp
          have h2 : 2 ^ (i - 1) ≤ a := Nat.le_log_of_pow_le (by norm_num) hi
          have : 2 ^ i = 2 * 2 ^ (i - 1) := by
            rw [← pow_succ']; congr 1; omega
          omega
      have hk1 : 1 ≤ st1.regs 1 := by rw [h11]; exact Nat.one_le_two_pow
      wram_step
      refine runs_seq_triple_le hloop2 ⟨by simp [h10], by simp [h1m], by simp; omega,
        by simp; omega, by simpa using hx1', by simpa using hk⟩ (fun st2 h2 => ?_)
      obtain ⟨⟨h20, h2m, -, hlo, hhi, -⟩, he⟩ := h2
      wram_step
      · refine ⟨?_, h2m⟩
        simp only [Outcome.value]
        rw [he] at hhi
        exact (Nat.log_eq_of_pow_le_of_lt_pow hlo hhi).symm
      · -- the cost
        have hc1 : Nat.clog 2 (st1.regs 1) ≤ Nat.log 2 (a + 1) + 2 := by
          refine Nat.clog_le_of_le_pow ?_
          have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (a + 1)
          rw [pow_succ] at this
          rw [pow_succ]
          omega
        have hc2 : Nat.log 2 a ≤ Nat.log 2 (a + 1) := Nat.log_mono_right (by omega)
        have hc3 : st1.regs 1 - 0 = st1.regs 1 := by omega
        unfold log2Cost
        rw [← ha]
        simp only [Function.update_self, Function.update_apply, startState,
          Nat.log_one_right, show ((1 : ℕ) = 2) = False from by decide, ite_false,
          Nat.sub_zero] at *
        wram_cost
  obtain ⟨o, st', c, hrun, hpost, hcost⟩ := htriple (startState [x] mem pos) ω rfl
  exact ⟨log2P, hproc, o, st', c, hrun, ⟨hpost.1, hpost.2⟩, hcost⟩

end MinCostFlow.LowStretch
