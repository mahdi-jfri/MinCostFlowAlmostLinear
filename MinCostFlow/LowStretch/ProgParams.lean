module

public import MinCostFlow.LowStretch.ProgLog
public import MinCostFlow.LowStretch.Params

/-!
# The constants of the construction

`parP` computes the numbers of `par n m` and the shift `pσ n` from `n` and `m`, with three
binary logarithms, and writes them to six cells (`parP_spec`). The bounds of this file show that
every number fits in a word when `2^16 (n + 4)^4` does.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

theorem pa_le_lin (n : ℕ) : pa n ≤ n + 2 := by
  have := Nat.log_lt_self 2 (show n + 2 ≠ 0 by omega)
  unfold pa; omega

theorem two_pow_pL_le (n : ℕ) : 2 ^ pL n ≤ 4 * pa n + 4 := by
  unfold pL
  rw [pow_succ]
  have := Nat.pow_log_le_self 2 (show 2 * pa n + 2 ≠ 0 by omega)
  omega

theorem pL_le_two_pow (n : ℕ) : pL n ≤ 2 ^ pL n := (Nat.lt_two_pow_self).le

theorem pB_le_poly (n : ℕ) : pB n ≤ 64 * (n + 4) ^ 2 := by
  have h1 := two_pow_pL_le n
  have h2 := pL_le_two_pow n
  have h3 := pa_le_lin n
  have h4 : pL n ≤ 4 * n + 12 := by omega
  have h5 : 2 ^ pL n + 3 ≤ 4 * n + 15 := by omega
  unfold pB
  calc 4 * pL n * (2 ^ pL n + 3) ≤ 4 * (4 * n + 12) * (4 * n + 15) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 4 h4) h5
    _ ≤ 64 * (n + 4) ^ 2 := by nlinarith

/-- `parP bLog` with `args = [n, m, out]`: writes `pa n, pL n, pB n, pσ n, Q, pκ n m` to
`out, …, out + 5`, where `Q = 512 · pB n · n²`. It calls `log2P` at `bLog`. -/
def parP (bLog : ℕ) : Stmt :=
  .seq (.call 3 bLog [.bin .add (.reg 0) (.const 2)])
  (.seq (.assign 3 (.bin .add (.reg 3) (.const 1)))
  (.seq (.call 4 bLog [.bin .add (.bin .mul (.const 2) (.reg 3)) (.const 2)])
  (.seq (.assign 4 (.bin .add (.reg 4) (.const 1)))
  (.seq (.assign 5 (.bin .mul (.bin .mul (.const 4) (.reg 4))
      (.bin .add (.bin .shiftLeft (.const 1) (.reg 4)) (.const 3))))
  (.seq (.call 6 bLog [.bin .mul (.bin .mul (.const 8) (.reg 5)) (.reg 0)])
  (.seq (.assign 6 (.bin .add (.reg 6) (.const 1)))
  (.seq (.store (.reg 2) (.reg 3))
  (.seq (.store (.bin .add (.reg 2) (.const 1)) (.reg 4))
  (.seq (.store (.bin .add (.reg 2) (.const 2)) (.reg 5))
  (.seq (.store (.bin .add (.reg 2) (.const 3)) (.reg 6))
  (.seq (.store (.bin .add (.reg 2) (.const 4))
      (.bin .mul (.bin .mul (.bin .mul (.const 512) (.reg 5)) (.reg 0)) (.reg 0)))
  (.seq (.store (.bin .add (.reg 2) (.const 5))
      (.bin .add (.bin .div (.reg 1) (.bin .mul (.reg 0) (.reg 0))) (.const 1)))
  (.ret (.const 0))))))))))))))

theorem parP_noRand (bLog : ℕ) : (parP bLog).NoRand := by simp [parP, Stmt.NoRand]

/-- The six numbers that `parP` writes. -/
def parVal (n m : ℕ) : ℕ → ℕ
  | 0 => pa n
  | 1 => pL n
  | 2 => pB n
  | 3 => pσ n
  | 4 => 512 * pB n * n ^ 2
  | _ => pκ n m

theorem log2Cost_le {x n : ℕ} (hx : x ≤ 2 ^ 16 * (n + 4) ^ 4) : log2Cost x ≤ 50 * (4 * n + 36) := by
  have h1 : (n + 4) ^ 4 < 2 ^ (4 * (n + 4)) := by
    rw [pow_mul']
    exact Nat.pow_lt_pow_left Nat.lt_two_pow_self (by norm_num)
  have h2 : x < 2 ^ (16 + 4 * (n + 4)) := by
    rw [pow_add]; nlinarith [Nat.one_le_two_pow (n := 16)]
  have h3 : Nat.log 2 x < 16 + 4 * (n + 4) := by
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h; simp
    · exact Nat.log_lt_of_lt_pow (by omega) h2
  have h4 := Nat.log_le_self 2 (Nat.log 2 x + 1)
  unfold log2Cost; omega

/-- The contract of `parP`. -/
def parC (w : ℕ) : Contract where
  pre args _ := ∃ n m out, args = [n, m, out] ∧ 1 ≤ n ∧ 2 ^ 16 * (n + 4) ^ 4 < 2 ^ w ∧
    m + 1 < 2 ^ w ∧ out + 6 < 2 ^ w
  post args mem _ mem' := (∀ i < 6, mem' (args.getD 2 0 + i) =
      parVal (args.getD 0 0) (args.getD 1 0) i) ∧
    ∀ a, (a < args.getD 2 0 ∨ args.getD 2 0 + 6 ≤ a) → mem' a = mem a
  cost args _ := 1000 * (args.getD 0 0 + 9)

theorem parP_spec {w : ℕ} {p : Program} {b bLog : ℕ} (hp : p.HasAt b [parP bLog])
    (hlog : p.HasAt bLog [log2P]) : MeetsContract w p b (parC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨n, m, out, rfl, hn, hbig, hm, hout⟩ := hpre
  have hproc : p.procs[b]? = some (parP bLog) := hp 0 (by simp)
  have hL := log2P_spec (w := w) hlog
  clear hp hlog
  have hB := pB_le_poly n
  have ha := pa_le_lin n
  have hl := two_pow_pL_le n
  have hl' := pL_le_two_pow n
  have hw16 : 2 ^ 16 < 2 ^ w := by
    have : 1 ≤ (n + 4) ^ 4 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hw2 : 2 ≤ w := by
    by_contra h
    have : 2 ^ w ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hn4 : n + 4 ≤ (n + 4) ^ 4 := Nat.le_self_pow (by norm_num) _
  have hn2 : n * n ≤ (n + 4) ^ 2 := by nlinarith
  have hsq : (n + 4) ^ 2 ≤ (n + 4) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hQ : 512 * pB n * n * n ≤ 2 ^ 15 * (n + 4) ^ 4 := by
    calc 512 * pB n * n * n = 512 * pB n * (n * n) := by ring
      _ ≤ 512 * (64 * (n + 4) ^ 2) * (n + 4) ^ 2 := by gcongr
      _ = 2 ^ 15 * (n + 4) ^ 4 := by ring
  have hBn : 8 * pB n * n ≤ 2 ^ 9 * (n + 4) ^ 4 := by
    calc 8 * pB n * n ≤ 8 * (64 * (n + 4) ^ 2) * (n + 4) ^ 2 := by gcongr; nlinarith
      _ = 2 ^ 9 * (n + 4) ^ 4 := by ring
  have hBpos : 1 ≤ pB n := pB_pos n
  have hBn1 : 1 ≤ 8 * pB n * n := by nlinarith
  have hc1 := log2Cost_le (x := n + 2) (n := n) (by nlinarith)
  have hc2 := log2Cost_le (x := 2 * pa n + 2) (n := n) (by nlinarith)
  have hc3 := log2Cost_le (x := 8 * pB n * n) (n := n) (by nlinarith)
  have hk1 : n + 2 < 2 ^ w := by omega
  have hw512 : 512 < 2 ^ w := by omega
  have hk2 : 2 * pa n + 2 < 2 ^ w := by omega
  have hk0 : 2 ^ pL n < 2 ^ w := by omega
  have hk3 : 2 ^ pL n + 3 < 2 ^ w := by omega
  have hk4 : 4 * pL n * (2 ^ pL n + 3) < 2 ^ w := by
    show pB n < 2 ^ w; omega
  have hk4' : 4 * pL n < 2 ^ w := by omega
  have hk5 : 8 * pB n * n < 2 ^ w := by omega
  have hk5' : 8 * pB n < 2 ^ w := by nlinarith
  have hk6 : 512 * pB n * n * n < 2 ^ w := by omega
  have hk6' : 512 * pB n * n < 2 ^ w := by nlinarith
  have hk6'' : 512 * pB n < 2 ^ w := by nlinarith
  have hk7 : n * n < 2 ^ w := by omega
  have hk8 : m / (n * n) + 1 < 2 ^ w := by
    have := Nat.div_le_self m (n * n); omega
  have hσ : pσ n < 2 ^ w := by
    have := Nat.log_lt_self 2 (show 8 * pB n * n ≠ 0 by omega)
    show Nat.log 2 (8 * pB n * n) + 1 < 2 ^ w; omega
  have hcost : log2Cost (n + 2) + log2Cost (2 * pa n + 2) + log2Cost (8 * pB n * n) ≤
      600 * (n + 9) := by omega
  have hσd : Nat.log 2 (8 * pB n * n) + 1 = pσ n := rfl
  have hBd : 4 * pL n * (2 ^ pL n + 3) = pB n := rfl
  have hLd : Nat.log 2 (2 * pa n + 2) + 1 = pL n := rfl
  have hAd : Nat.log 2 (n + 2) + 1 = pa n := rfl
  have hshl : 1 <<< pL n = 2 ^ pL n := by simp [Nat.shiftLeft_eq]
  rw [← hshl] at hk0 hk3 hk4 hBd
  clear hshl hbig hB ha hl hl' hw16 hn4 hn2 hsq hQ hBn hc1 hc2 hc3 hwords hBpos
  generalize hLC : log2Cost = LC at hcost
  generalize hS : pσ n = S at *
  generalize hB : pB n = B at *
  generalize hLp : pL n = Lp at *
  generalize hA : pa n = A at *
  refine ⟨parP bLog, hproc, ?_⟩
  refine runs_start_le ?_
  dsimp only [parP]
  wram_step
  · exact ⟨n + 2, by simp, by omega, hk1, hw2⟩
  intro v1 mem1 pos1 ⟨hv1, hm1⟩
  simp only [List.getD_cons_zero] at hv1
  subst hm1
  have e1 : v1 + 1 = A := by rw [hv1]; exact hAd
  clear hv1 hAd
  subst e1
  wram_step
  wram_step
  · exact ⟨2 * (v1 + 1) + 2, by simp, by omega, by omega, hw2⟩
  intro v2 mem2 pos2 ⟨hv2, hm2⟩
  simp only [List.getD_cons_zero] at hv2
  subst hm2
  have e2 : v2 + 1 = Lp := by rw [hv2]; exact hLd
  clear hv2 hLd
  subst e2
  wram_step
  wram_step
  wram_step
  · exact ⟨8 * B * n, by simp [hBd], by omega, by omega, hw2⟩
  intro v3 mem3 pos3 ⟨hv3, hm3⟩
  simp only [List.getD_cons_zero] at hv3
  subst hm3
  have e3 : v3 + 1 = S := by rw [hv3]; exact hσd
  clear hv3 hσd
  subst e3
  rw [hBd]
  wram_run
  · refine ⟨fun i hi => ?_, fun a ha => ?_⟩
    · simp only [List.getD_cons_zero, List.getD_cons_succ]
      interval_cases i <;> simp [Function.update_apply, parVal, hA, hLp, hB, hS, pκ, sq] <;>
        first | omega | ring
    · simp only [List.getD_cons_zero, List.getD_cons_succ] at ha ⊢
      simp only [Function.update_apply]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]
  · simp only [log2C, List.getD_cons_zero, List.getD_cons_succ, startState, parC]
    rw [← hLC] at hcost
    wram_cost

end MinCostFlow.LowStretch
