module

public import MinCostFlow.LowStretch.ProgLog

/-!
# Rounding the weights

`rndP` rounds the weight `x` of every edge to `2^(⌊log₂ x⌋ + σ)`, the weight of its pair in
`toPG G σ`. It writes the exponent and the power to two arrays (`rndP_spec`). The cost is one
binary logarithm per edge.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

theorem log2Cost_mono {x y : ℕ} (h : x ≤ y) : log2Cost x ≤ log2Cost y := by
  unfold log2Cost
  have := Nat.log_mono_right (b := 2) (Nat.add_le_add_right (Nat.log_mono_right (b := 2) h) 1)
  omega

/-- `rndP bLog` with `args = [m, σ, IN, PE, PW, W]`: for every edge `j < m` with weight
`x = mem (IN + 3j + 2)`, writes `⌊log₂ x⌋ + σ` to `PE + j` and `2^(⌊log₂ x⌋ + σ)` to `PW + j`.
`W` bounds the weights; it is used only by the cost. -/
def rndP (bLog : ℕ) : Stmt :=
  .seq (forRange 6 (.const 0) (.reg 0)
    (.seq (.call 7 bLog [.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 6)))
        (.const 2))])
    (.seq (.assign 7 (.bin .add (.reg 7) (.reg 1)))
    (.seq (.store (.bin .add (.reg 3) (.reg 6)) (.reg 7))
      (.store (.bin .add (.reg 4) (.reg 6)) (.bin .shiftLeft (.const 1) (.reg 7)))))))
  (.ret (.const 0))

theorem rndP_noRand (bLog : ℕ) : (rndP bLog).NoRand := by
  simp [rndP, forRange, forUp, Stmt.NoRand]

/-- The rounded exponent of edge `j`. -/
def rexp (mem : ℕ → ℕ) (IN σ j : ℕ) : ℕ := Nat.log 2 (mem (IN + 3 * j + 2)) + σ

/-- The contract of `rndP`. -/
def rndC (w : ℕ) : Contract where
  pre args mem := ∃ m σ IN PE PW W, args = [m, σ, IN, PE, PW, W] ∧ 2 ≤ w ∧
    (∀ j < m, 1 ≤ mem (IN + 3 * j + 2) ∧ mem (IN + 3 * j + 2) ≤ W) ∧ W * 2 ^ σ < 2 ^ w ∧
    IN + 3 * m ≤ PE ∧ PE + m ≤ PW ∧ PW + m < 2 ^ w
  post args mem _ mem' :=
    (∀ j < args.getD 0 0,
      mem' (args.getD 3 0 + j) = rexp mem (args.getD 2 0) (args.getD 1 0) j ∧
      mem' (args.getD 4 0 + j) = 2 ^ rexp mem (args.getD 2 0) (args.getD 1 0) j) ∧
    ∀ a, (a < args.getD 3 0 ∨ args.getD 4 0 + args.getD 0 0 ≤ a) → mem' a = mem a
  cost args _ := args.getD 0 0 * (log2Cost (args.getD 5 0) + 70) + 20

theorem rndP_spec {w : ℕ} {p : Program} {b bLog : ℕ} (hp : p.HasAt b [rndP bLog])
    (hlog : p.HasAt bLog [log2P]) : MeetsContract w p b (rndC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨m, σ, IN, PE, PW, W, rfl, hw2, hwt, hWσ, h1, h2, h3⟩ := hpre
  have hproc : p.procs[b]? = some (rndP bLog) := hp 0 (by simp)
  have hL := log2P_spec (w := w) hlog
  clear hp hlog hwords
  have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hpowσ : 1 ≤ 2 ^ σ := Nat.one_le_two_pow
  -- the bounds of one edge
  have hE : ∀ j < m, rexp mem IN σ j < 2 ^ w ∧ 2 ^ rexp mem IN σ j < 2 ^ w ∧
      mem (IN + 3 * j + 2) < 2 ^ w ∧ log2Cost (mem (IN + 3 * j + 2)) ≤ log2Cost W := by
    intro j hj
    obtain ⟨hx1, hxW⟩ := hwt j hj
    have hpow : 2 ^ rexp mem IN σ j ≤ mem (IN + 3 * j + 2) * 2 ^ σ := by
      unfold rexp; rw [pow_add]
      exact Nat.mul_le_mul_right _ (Nat.pow_log_le_self 2 (by omega))
    have hle : mem (IN + 3 * j + 2) * 2 ^ σ ≤ W * 2 ^ σ := Nat.mul_le_mul_right _ hxW
    have hlt := Nat.lt_two_pow_self (n := rexp mem IN σ j)
    refine ⟨by omega, by omega, ?_, log2Cost_mono hxW⟩
    have : mem (IN + 3 * j + 2) ≤ mem (IN + 3 * j + 2) * 2 ^ σ := Nat.le_mul_of_pos_right _ hpowσ
    omega
  generalize hLC : log2Cost = LC at hE
  let R : State → Prop := fun st => st.regs 0 = m ∧ st.regs 1 = σ ∧ st.regs 2 = IN ∧
    st.regs 3 = PE ∧ st.regs 4 = PW
  have hR : ∀ st r v, R st → 5 ≤ r → R { st with regs := Function.update st.regs r v } := by
    intro st r v ⟨a0, a1, a2, a3, a4⟩ hr
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Function.update_apply] <;> (rw [if_neg (by omega)]; assumption)
  let Fr : (ℕ → ℕ) → Prop := fun M' => ∀ a, (a < PE ∨ PW + m ≤ a) → M' a = mem a
  let I : ℕ → State → Prop := fun i st => R st ∧ st.regs 6 = i ∧ Fr st.mem ∧
    ∀ j < i, st.mem (PE + j) = rexp mem IN σ j ∧ st.mem (PW + j) = 2 ^ rexp mem IN σ j
  have hloop := Triple.forRange_const (p := p) (r := 6) (lo := .const 0) (hi := .reg 0)
    (body := .seq (.call 7 bLog [.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 3)
        (.reg 6))) (.const 2))])
      (.seq (.assign 7 (.bin .add (.reg 7) (.reg 1)))
      (.seq (.store (.bin .add (.reg 3) (.reg 6)) (.reg 7))
        (.store (.bin .add (.reg 4) (.reg 6)) (.bin .shiftLeft (.const 1) (.reg 7))))))
    (P := fun st => R st ∧ st.mem = mem) (Inv := I) (LC W + 60) 0 m (Nat.zero_le _) hw1
    (fun _ => by omega)
    (fun st ⟨hr, hm⟩ => ⟨by eval_expr, hR st 6 0 hr (by omega), by simp, fun a _ => by simp [hm],
      fun j hj => absurd hj (by omega)⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.1; eval_expr)
    (fun i _ hi st ω hI => by
      obtain ⟨hr, h6, hfr, hdone⟩ := hI
      obtain ⟨r0, r1, r2, r3, r4⟩ := hr
      obtain ⟨hE1, hE2, hE3, hE4⟩ := hE i hi
      have hx : st.mem (IN + 3 * i + 2) = mem (IN + 3 * i + 2) := hfr _ (by omega)
      have hcl := hwt i hi
      refine runs_start_le ?_
      wram_step
      · exact ⟨mem (IN + 3 * i + 2), by simp [r2, h6, hx], by omega, hE3, hw2⟩
      intro v mem1 pos1 ⟨hv, hm1⟩
      simp only [List.getD_cons_zero, r2, h6, hx] at hv
      subst hm1
      have ev : v + σ = rexp mem IN σ i := by rw [hv]; rfl
      clear hv
      have hs : 1 <<< (v + σ) = 2 ^ rexp mem IN σ i := by rw [ev]; simp [Nat.shiftLeft_eq]
      rw [← ev] at hE1
      rw [← hs] at hE2
      have hE2' : 1 <<< (v + st.regs 1) < 2 ^ w := by rw [r1]; exact hE2
      have hE1' : v + st.regs 1 < 2 ^ w := by rw [r1]; exact hE1
      wram_run
      · refine ⟨⟨by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Function.update_apply, *],
          by simp, fun a ha => ?_, fun j hj => ?_⟩, by simp [h6]⟩
        · simp only [Function.update_apply, r3, r4, h6]
          rw [if_neg (by omega), if_neg (by omega)]; exact hfr a ha
        · simp only [Function.update_apply, r3, r4, h6, r1]
          by_cases hji : j = i
          · subst hji
            have hne : PE ≠ PW := by omega
            simp [ev, hne, Nat.shiftLeft_eq]
          · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
            exact hdone j (by omega)
      · simp only [log2C, List.getD_cons_zero, r2, h6, hx]
        rw [hLC]
        wram_cost)
  refine ⟨rndP bLog, hproc, ?_⟩
  dsimp only [rndP]
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop ?_ (fun st hI => ?_)
  · exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  obtain ⟨-, -, hfr, hall⟩ := hI
  refine runs_ret_le (by eval_expr) ⟨fun j hj => hall j hj, fun a ha => hfr a ha⟩ ?_
  simp only [rndC, List.getD_cons_zero, List.getD_cons_succ, Expr.size]
  rw [hLC]
  have : (m - 0) * (LC W + 60 + 1 + 8) ≤ m * (LC W + 70) := by
    rw [Nat.sub_zero]; exact Nat.mul_le_mul_left _ (by omega)
  omega

end MinCostFlow.LowStretch
