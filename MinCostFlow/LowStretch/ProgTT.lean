module

public import WordRAM.Logic
public import WordRAM.Tactic
public import Mathlib.Data.Nat.Log

/-!
# A tournament tree

Dijkstra and the petal searches keep one queue per weight class, and they need the class whose
first entry is smallest. There are only `O(log n)` classes, so a tournament tree over them gives
this class in one step, and a change of one class costs `O(log log n)`.

The tree with `S` leaves lives at `T + 1, …, T + 2S - 1`. Leaf `j` is the cell `T + S + j`, and
each inner cell `T + i` with `1 ≤ i < S` holds the smaller of its two children `T + 2i` and
`T + 2i + 1` (`TTOk`). Then the root `T + 1` holds the least leaf (`TTOk.root_le`,
`TTOk.root_mem`). The procedure `ttUpdate` changes one leaf and repairs the cells above it, in
`O(log S)` steps (`ttUpdate_spec`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- Every inner cell of the tree holds the smaller of its two children. -/
def TTOk (mem : ℕ → ℕ) (T S : ℕ) : Prop :=
  ∀ i, 1 ≤ i → i < S → mem (T + i) = min (mem (T + 2 * i)) (mem (T + 2 * i + 1))

section math

variable {mem : ℕ → ℕ} {T S : ℕ}

/-- Each cell holds at most the cells below it. -/
theorem TTOk.le_below (h : TTOk mem T S) {ℓ : ℕ} (hℓ : ℓ < 2 * S) :
    ∀ k, 1 ≤ ℓ / 2 ^ k → mem (T + ℓ / 2 ^ k) ≤ mem (T + ℓ)
  | 0 => fun _ => by simp
  | k + 1 => fun hk => by
    have hy : ℓ / 2 ^ (k + 1) = ℓ / 2 ^ k / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
    have hyle : ℓ / 2 ^ k ≤ ℓ := Nat.div_le_self _ _
    rw [hy] at hk ⊢
    have ih := TTOk.le_below h hℓ k (by omega)
    have hm := h (ℓ / 2 ^ k / 2) hk (by omega)
    rw [hm]
    rcases Nat.mod_two_eq_zero_or_one (ℓ / 2 ^ k) with h2 | h2
    · have e : T + 2 * (ℓ / 2 ^ k / 2) = T + ℓ / 2 ^ k := by omega
      rw [e]
      exact (min_le_left _ _).trans ih
    · have e : T + 2 * (ℓ / 2 ^ k / 2) + 1 = T + ℓ / 2 ^ k := by omega
      rw [e]
      exact (min_le_right _ _).trans ih

/-- The root holds at most every leaf. -/
theorem TTOk.root_le (h : TTOk mem T S) {j : ℕ} (hj : j < S) : mem (T + 1) ≤ mem (T + S + j) := by
  have hpos : S + j ≠ 0 := by omega
  have h1 := Nat.pow_log_le_self 2 hpos
  have h2 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (S + j)
  have e : (S + j) / 2 ^ Nat.log 2 (S + j) = 1 := by
    refine Nat.div_eq_of_lt_le (by omega) ?_
    rw [pow_succ] at h2
    omega
  have := h.le_below (ℓ := S + j) (by omega) (Nat.log 2 (S + j)) (by rw [e])
  rw [e] at this
  rwa [Nat.add_assoc]

/-- Each cell holds the value of some leaf below it. -/
theorem TTOk.exists_leaf (h : TTOk mem T S) :
    ∀ d x, 2 * S - x = d → 1 ≤ x → x < 2 * S → ∃ ℓ, S ≤ ℓ ∧ ℓ < 2 * S ∧ mem (T + x) = mem (T + ℓ) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro x hd hx1 hx2
    by_cases hxS : S ≤ x
    · exact ⟨x, hxS, hx2, rfl⟩
    · push Not at hxS
      have hm := h x hx1 hxS
      rcases min_choice (mem (T + 2 * x)) (mem (T + 2 * x + 1)) with hc | hc
      · obtain ⟨ℓ, h1, h2, h3⟩ := ih (2 * S - 2 * x) (by omega) (2 * x) rfl (by omega) (by omega)
        exact ⟨ℓ, h1, h2, by rw [hm, hc, h3]⟩
      · obtain ⟨ℓ, h1, h2, h3⟩ := ih (2 * S - (2 * x + 1)) (by omega) (2 * x + 1) rfl (by omega)
          (by omega)
        exact ⟨ℓ, h1, h2, by rw [hm, hc, show T + 2 * x + 1 = T + (2 * x + 1) by ring, h3]⟩

/-- The root holds the value of some leaf. -/
theorem TTOk.root_mem (h : TTOk mem T S) (hS : 1 ≤ S) :
    ∃ j < S, mem (T + 1) = mem (T + S + j) := by
  obtain ⟨ℓ, h1, h2, h3⟩ := h.exists_leaf _ 1 rfl le_rfl (by omega)
  exact ⟨ℓ - S, by omega, by rw [h3, Nat.add_assoc, Nat.add_sub_cancel' h1]⟩

/-- `x` is a cell strictly above leaf `j`. -/
def IsAnc (S j x : ℕ) : Prop := ∃ k, 1 ≤ k ∧ (S + j) / 2 ^ k = x

theorem IsAnc.le {S j x : ℕ} (h : IsAnc S j x) : x ≤ (S + j) / 2 := by
  obtain ⟨k, hk, rfl⟩ := h
  have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  exact Nat.div_le_div_left (by simpa using this) (by norm_num)

theorem IsAnc.half {S j x : ℕ} (h : IsAnc S j x) : x / 2 = 0 ∨ IsAnc S j (x / 2) := by
  obtain ⟨k, hk, rfl⟩ := h
  right
  exact ⟨k + 1, by omega, by rw [pow_succ, Nat.div_div_eq_div_mul]⟩

/-- Two cells above the same leaf: the lower one is at most half the higher one. -/
theorem IsAnc.le_half {S j x i : ℕ} (hx : IsAnc S j x) (hi : IsAnc S j i) (hlt : x < i) :
    x ≤ i / 2 := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hi
  have hab : b + 1 ≤ a := by
    by_contra hc
    have : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.div_le_div_left (a := S + j) this (by positivity)
    omega
  have : 2 ^ (b + 1) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hab
  calc (S + j) / 2 ^ a ≤ (S + j) / 2 ^ (b + 1) := Nat.div_le_div_left this (by positivity)
    _ = (S + j) / 2 ^ b / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]

/-- One repair step of `ttUpdate`: cell `i` takes the smaller of its children, and the cells that
are still to be repaired are those above `i / 2`. -/
theorem tt_step {M : ℕ → ℕ} {j i : ℕ} (hi1 : 1 ≤ i) (hia : IsAnc S j i) (hjS : j < S)
    (h2 : ∀ x, 1 ≤ x → x < 2 * S → x ≠ S + j → ¬ (IsAnc S j x ∧ i < x) → M (T + x) = mem (T + x))
    (h3 : ∀ x, 1 ≤ x → x < S → ¬ (IsAnc S j x ∧ x ≤ i) →
      M (T + x) = min (M (T + 2 * x)) (M (T + 2 * x + 1))) :
    (∀ x, 1 ≤ x → x < 2 * S → x ≠ S + j → ¬ (IsAnc S j x ∧ i / 2 < x) →
      Function.update M (T + i) (min (M (T + 2 * i)) (M (T + 2 * i + 1))) (T + x) = mem (T + x)) ∧
    (∀ x, 1 ≤ x → x < S → ¬ (IsAnc S j x ∧ x ≤ i / 2) →
      Function.update M (T + i) (min (M (T + 2 * i)) (M (T + 2 * i + 1))) (T + x) =
        min (Function.update M (T + i) (min (M (T + 2 * i)) (M (T + 2 * i + 1))) (T + 2 * x))
          (Function.update M (T + i) (min (M (T + 2 * i)) (M (T + 2 * i + 1))) (T + 2 * x + 1))) := by
  have hiS : i < S := by have := hia.le; omega
  constructor
  · intro x hx1 hx2 hxj hn
    have hxi : x ≠ i := by
      rintro rfl
      exact hn ⟨hia, by omega⟩
    rw [Function.update_of_ne (by omega)]
    exact h2 x hx1 hx2 hxj fun ⟨ha, hlt⟩ => hn ⟨ha, by omega⟩
  · intro x hx1 hxS hn
    have hc1 : T + 2 * x ≠ T + i := by
      intro he
      have : x = i / 2 := by omega
      rcases hia.half with h0 | ha
      · omega
      · exact hn ⟨this ▸ ha, by omega⟩
    have hc2 : T + 2 * x + 1 ≠ T + i := by
      intro he
      have : x = i / 2 := by omega
      rcases hia.half with h0 | ha
      · omega
      · exact hn ⟨this ▸ ha, by omega⟩
    rw [Function.update_of_ne hc1, Function.update_of_ne hc2]
    by_cases hxi : x = i
    · subst hxi
      rw [Function.update_self]
    · rw [Function.update_of_ne (by omega)]
      refine h3 x hx1 hxS fun ⟨ha, hle⟩ => hn ⟨ha, ?_⟩
      exact ha.le_half hia (by omega)

end math

/-! ### The update procedure -/

/-- `ttUpdate`: `args = [T, S, j, v]`. Leaf `j` becomes `v`, then the cells above it are repaired
from the bottom up. -/
def ttUpdate : Stmt :=
  .seq (.store (.bin .add (.reg 0) (.bin .add (.reg 1) (.reg 2))) (.reg 3))
  (.seq (.assign 4 (.bin .div (.bin .add (.reg 1) (.reg 2)) (.const 2)))
  (.seq (.loop (.bin .lt (.const 0) (.reg 4))
      (.seq (.assign 5 (.load (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 4)))))
      (.seq (.assign 6 (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 4)))
        (.const 1))))
      (.seq (.cond (.bin .lt (.reg 5) (.reg 6))
          (.store (.bin .add (.reg 0) (.reg 4)) (.reg 5))
          (.store (.bin .add (.reg 0) (.reg 4)) (.reg 6)))
        (.assign 4 (.bin .div (.reg 4) (.const 2)))))))
  (.ret (.const 0))))

theorem ttUpdate_noRand : ttUpdate.NoRand := by simp [ttUpdate, Stmt.NoRand]

/-- The contract of `ttUpdate`. -/
def ttUpdateC (w : ℕ) : Contract where
  pre args mem := ∃ T S j v, args = [T, S, j, v] ∧ j < S ∧ T + 2 * S < 2 ^ w ∧ 2 < 2 ^ w ∧
    TTOk mem T S
  post args mem _ mem' :=
    let T := args.getD 0 0
    let S := args.getD 1 0
    let j := args.getD 2 0
    let v := args.getD 3 0
    TTOk mem' T S ∧ mem' (T + S + j) = v ∧
      (∀ j' < S, j' ≠ j → mem' (T + S + j') = mem (T + S + j')) ∧
      ∀ a, a ≤ T ∨ T + 2 * S ≤ a → mem' a = mem a
  cost args _ := 50 * (Nat.log 2 (args.getD 1 0) + 2)

theorem ttUpdate_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [ttUpdate]) :
    MeetsContract w p b (ttUpdateC w) := by
  intro args mem pos ω hwords hpre
  dsimp only [ttUpdateC] at hpre
  obtain ⟨T, S, j, v, rfl, hjS, hTS, hw2, htt⟩ := hpre
  have hproc : p.procs[b]? = some ttUpdate := hp 0 (by simp)
  -- the loop
  let Inv : State → Prop := fun st =>
    st.regs 0 = T ∧ st.regs 1 = S ∧ st.regs 2 = j ∧ st.regs 3 = v ∧
    (st.regs 4 = 0 ∨ IsAnc S j (st.regs 4)) ∧
    st.mem (T + S + j) = v ∧
    (∀ x, 1 ≤ x → x < 2 * S → x ≠ S + j → ¬ (IsAnc S j x ∧ st.regs 4 < x) →
      st.mem (T + x) = mem (T + x)) ∧
    (∀ x, 1 ≤ x → x < S → ¬ (IsAnc S j x ∧ x ≤ st.regs 4) →
      st.mem (T + x) = min (st.mem (T + 2 * x)) (st.mem (T + 2 * x + 1))) ∧
    (∀ a, a ≤ T ∨ T + 2 * S ≤ a → st.mem a = mem a)
  have hloop : Triple w p Inv
      (.loop (.bin .lt (.const 0) (.reg 4))
        (.seq (.assign 5 (.load (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 4)))))
        (.seq (.assign 6 (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 4)))
          (.const 1))))
        (.seq (.cond (.bin .lt (.reg 5) (.reg 6))
            (.store (.bin .add (.reg 0) (.reg 4)) (.reg 5))
            (.store (.bin .add (.reg 0) (.reg 4)) (.reg 6)))
          (.assign 4 (.bin .div (.reg 4) (.const 2)))))))
      (normalPost fun st' => Inv st' ∧ st'.regs 4 = 0)
      (fun st => (3 + 40 + 1) * Nat.log 2 (2 * st.regs 4) + 3 + 1) := by
    refine Triple.loop_const_normal (fun st => Nat.log 2 (2 * st.regs 4))
      (fun st => if 0 < st.regs 4 then 1 else 0) 40
      (fun st hI => by eval_expr)
      (fun st hI h0 => ⟨hI, by simp only [ite_eq_right_iff, one_ne_zero, imp_false] at h0; omega⟩)
      (fun st hI hne => ?_)
    simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at hne
    obtain ⟨hr0, hr1, hr2, hr3, hanc, hleaf, h2, h3, hfr⟩ := hI
    have hia : IsAnc S j (st.regs 4) := hanc.resolve_left (by omega)
    have hiS : st.regs 4 < S := by have := hia.le; omega
    have hstep := tt_step (mem := mem) (T := T) (M := st.mem) hne hia hjS h2 h3
    have hlog : Nat.log 2 (2 * (st.regs 4 / 2)) < Nat.log 2 (2 * st.regs 4) := by
      have e : Nat.log 2 (2 * st.regs 4) = Nat.log 2 (st.regs 4) + 1 := by
        rw [mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
      rw [e]
      exact Nat.lt_succ_of_le (Nat.log_mono_right (by omega))
    -- the state after the body
    have hnext : ∀ M', M' = Function.update st.mem (T + st.regs 4)
        (min (st.mem (T + 2 * st.regs 4)) (st.mem (T + 2 * st.regs 4 + 1))) →
        ∀ R : ℕ → ℕ, R 0 = T → R 1 = S → R 2 = j → R 3 = v → R 4 = st.regs 4 / 2 →
        ∀ pos', Inv { mem := M', regs := R, pos := pos' } ∧
          Nat.log 2 (2 * R 4) < Nat.log 2 (2 * st.regs 4) := by
      intro M' hM' R h0 h1 h2' h3' h4 pos'
      subst hM'
      refine ⟨⟨h0, h1, h2', h3', ?_, ?_, ?_, ?_, ?_⟩, by rw [h4]; exact hlog⟩
      · dsimp only; rw [h4]; exact hia.half
      · dsimp only
        rw [Function.update_of_ne (by omega)]; exact hleaf
      · intro x a1 a2 a3 a4; dsimp only at a4 ⊢; rw [h4] at a4; exact hstep.1 x a1 a2 a3 a4
      · intro x a1 a2 a3; dsimp only at a3 ⊢; rw [h4] at a3; exact hstep.2 x a1 a2 a3
      · intro a ha
        dsimp only
        rw [Function.update_of_ne (by omega)]; exact hfr a ha
    wram_enter
    · subst hpre
      wram_run
      · dsimp only [normalPost_normal]
        rw [hr0] at hcond
        refine hnext _ ?_ _ ?_ ?_ ?_ ?_ ?_ _ <;> simp [hr0, hr1, hr2, hr3]
        rw [Nat.min_def, if_pos hcond.le]
      · wram_cost
      · dsimp only [normalPost_normal]
        rw [hr0] at hcond
        refine hnext _ ?_ _ ?_ ?_ ?_ ?_ ?_ _ <;> simp [hr0, hr1, hr2, hr3]
        rw [min_eq_right (by omega)]
      · wram_cost
  have htriple : Triple w p (fun st => st = startState [T, S, j, v] mem pos) ttUpdate
      (fun o st' => TTOk st'.mem T S ∧ st'.mem (T + S + j) = v ∧
        (∀ j' < S, j' ≠ j → st'.mem (T + S + j') = mem (T + S + j')) ∧
        ∀ a, a ≤ T ∨ T + 2 * S ≤ a → st'.mem a = mem a)
      (fun _ => 50 * (Nat.log 2 S + 2)) := by
    wram_enter
    · subst hpre
      dsimp only [ttUpdate]
      have hT : T < 2 ^ w := by omega
      have hS : S < 2 ^ w := by omega
      have hj : j < 2 ^ w := by omega
      wram_step
      wram_step
      have hlogS : Nat.log 2 (2 * ((S + j) / 2)) ≤ Nat.log 2 S + 1 := by
        have : Nat.log 2 (2 * S) = Nat.log 2 S + 1 := by
          rw [mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
        rw [← this]
        exact Nat.log_mono_right (by omega)
      refine runs_seq_triple_le hloop ?_ (fun st' hst' => ?_)
      · refine ⟨by simp [startState], by simp [startState], by simp [startState],
          by simp [startState], ?_, ?_, ?_, ?_, ?_⟩
        · simp only [Function.update_self]
          by_cases h0 : (S + j) / 2 = 0
          · left; exact h0
          · right; exact ⟨1, le_rfl, by simp⟩
        · simp [startState, Nat.add_assoc]
        · intro x hx1 hx2 hxj _
          simp only [startState]
          rw [Function.update_of_ne (by omega)]
        · intro x hx1 hxS hn
          simp only [startState, Function.update_self] at hn ⊢
          have hna : ¬ IsAnc S j x := fun ha => hn ⟨ha, ha.le⟩
          have hc1 : T + 2 * x ≠ T + (S + j) := by
            intro he
            exact hna ⟨1, le_rfl, by simp; omega⟩
          have hc2 : T + 2 * x + 1 ≠ T + (S + j) := by
            intro he
            exact hna ⟨1, le_rfl, by simp; omega⟩
          rw [Function.update_of_ne (by omega), Function.update_of_ne hc1,
            Function.update_of_ne hc2]
          exact htt x hx1 hxS
        · intro a ha
          simp only [startState]
          rw [Function.update_of_ne (by omega)]
      · obtain ⟨⟨-, -, -, -, -, hleaf, h2, h3, hfr⟩, h0⟩ := hst'
        wram_step
        · refine ⟨fun x hx1 hxS => h3 x hx1 hxS (by omega), hleaf, fun j' hj' hne => ?_, hfr⟩
          have := h2 (S + j') (by omega) (by omega) (by omega) (fun ⟨ha, _⟩ => by
            have := ha.le; omega)
          rwa [← Nat.add_assoc] at this
        · simp only [Expr.size_const, Expr.size_reg, Expr.size_bin, Expr.size_load,
            startState, Function.update_self] at *
          omega
  obtain ⟨o, st', c, hrun, hpost, hcost⟩ := htriple (startState [T, S, j, v] mem pos) ω rfl
  exact ⟨ttUpdate, hproc, o, st', c, hrun, hpost, hcost⟩

end MinCostFlow.LowStretch
