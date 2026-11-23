module

public import WordRAM.Logic
public import MinCostFlow.Expander.DecomposePhi
public import MinCostFlow.Expander.CsrBfsProg

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Deterministic Word-RAM Computation of `phiDenHalf`

Implements and verifies `computePhiDenStmt`, computing `phiDenHalf K_nat thr m` from register
`rM` into `rOut` in `O(Nat.log 2 (4 * m + 2) + K_nat * (rOf (4 * m)) ^ 2 + 1)` Word-RAM steps
without touching memory.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited

/-- Register-only deterministic statement computing `phiDenHalf K_nat thr m` from `rM` into `rOut`.
Scratch registers `[rL, rR, rPow, rIdx, rCur]` and `[rM, rOut]` must be distinct. -/
def computePhiDenStmt (K_nat thr rM rOut rL rR rPow rIdx rCur : ℕ) : Stmt :=
  seqStmts
    [ .assign rCur (.bin .add (.bin .mul (.const 4) (.reg rM)) (.const 2))
    , .assign rL (.const 0)
    , .loop (.bin .lt (.const 1) (.reg rCur))
        (seqStmts [ .assign rCur (.bin .div (.reg rCur) (.const 2)),
                    .assign rL (.bin .add (.reg rL) (.const 1)) ])
    , .assign rL (.bin .add (.reg rL) (.const 2))
    , .assign rCur (.bin .mul (.const 4) (.reg rM))
    , .assign rR (.const 0)
    , .loop (.bin .lt (.const 1) (.reg rCur))
        (seqStmts [ .assign rCur (.bin .div (.reg rCur) (.const 2)),
                    .assign rR (.bin .add (.reg rR) (.const 1)) ])
    , .assign rIdx (.reg rR)
    , .assign rR (.const 0)
    , .assign rCur (.const 1)
    , .loop (.bin .lt (.bin .mul (.bin .mul (.reg rCur) (.reg rCur)) (.reg rCur))
        (.bin .add (.reg rIdx) (.const 1)))
        (seqStmts [ .assign rR (.bin .add (.reg rR) (.const 1)),
                    .assign rCur (.bin .add (.reg rR) (.const 1)) ])
    , .assign rIdx (.bin .mul (.bin .mul (.const K_nat) (.reg rR)) (.reg rR))
    , .assign rPow (.const 1)
    , .assign rCur (.const 0)
    , .loop (.bin .lt (.reg rCur) (.reg rIdx))
        (seqStmts [ .assign rPow (.bin .mul (.reg rPow) (.reg rL)),
                    .assign rCur (.bin .add (.reg rCur) (.const 1)) ])
    , .assign rOut (.bin .mul (.const (200 * K_nat)) (.reg rPow))
    , .cond (.bin .lt (.reg rOut) (.const (thr + 1)))
        (.assign rOut (.const (thr + 1))) .nop ]

lemma computePhiDenStmt_noRand (K_nat thr rM rOut rL rR rPow rIdx rCur : ℕ) :
    (computePhiDenStmt K_nat thr rM rOut rL rR rPow rIdx rCur).NoRand := by
  simp [computePhiDenStmt, seqStmts, Stmt.NoRand]

lemma log2_loop_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (rCur rCnt : ℕ) (hne : rCur ≠ rCnt) (x0 : ℕ) (hx : x0 < 2 ^ w) (h4 : 4 ≤ 2 ^ w)
    (st₀ : State) (hrc : st₀.regs rCur = x0) (hrk : st₀.regs rCnt = 0)
    (hk2w : Nat.log 2 x0 < 2 ^ w) :
    ∃ st' c,
      Runs w p ω
        (.loop (.bin .lt (.const 1) (.reg rCur))
          (seqStmts [ .assign rCur (.bin .div (.reg rCur) (.const 2)),
                      .assign rCnt (.bin .add (.reg rCnt) (.const 1)) ]))
        st₀ .normal st' c ∧
      st'.regs rCnt = Nat.log 2 x0 ∧
      st'.mem = st₀.mem ∧
      st'.pos = st₀.pos ∧
      (∀ r, r ≠ rCur → r ≠ rCnt → st'.regs r = st₀.regs r) ∧
      c ≤ 13 * (Nat.log 2 x0 + 1) := by
  have hinv : ∀ d k (st : State), k + Nat.log 2 d = Nat.log 2 x0 → d ≤ x0 →
      (∀ r, r ≠ rCur → r ≠ rCnt → st.regs r = st₀.regs r) →
      st.regs rCur = d → st.regs rCnt = k → st.mem = st₀.mem → st.pos = st₀.pos →
      ∃ st' c, Runs w p ω
        (.loop (.bin .lt (.const 1) (.reg rCur))
          (seqStmts [ .assign rCur (.bin .div (.reg rCur) (.const 2)),
                      .assign rCnt (.bin .add (.reg rCnt) (.const 1)) ]))
        st .normal st' c ∧
        st'.regs rCnt = Nat.log 2 x0 ∧ st'.mem = st₀.mem ∧ st'.pos = st₀.pos ∧
        (∀ r, r ≠ rCur → r ≠ rCnt → st'.regs r = st₀.regs r) ∧
        c ≤ 13 * (Nat.log 2 d + 1) := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro k st hsum hd hreg hcur hcnt hmem hpos
      by_cases hd1 : 1 < d
      · have he_cond : (Expr.bin .lt (.const 1) (.reg rCur)).eval w st = some 1 := by
          simp [Expr.eval, BinOp.eval, hcur, hd1, show (1 : ℕ) < 2 ^ w by omega]
        have hd_lt : d < 2 ^ w := by omega
        have hd2_lt : d / 2 < d := Nat.div_lt_self (by omega) (by decide)
        have hlog_eq : Nat.log 2 d = Nat.log 2 (d / 2) + 1 := by
          rw [Nat.log_of_one_lt_of_le (by omega) hd1]
        let st1 : State := { st with regs := Function.update st.regs rCur (d / 2) }
        have hstep1 : Runs w p ω (.assign rCur (.bin .div (.reg rCur) (.const 2))) st .normal st1 4 :=
          runs_assign_iff.mpr ⟨d / 2, by
            simp [Expr.eval, BinOp.eval, hcur, show (2 : ℕ) < 2 ^ w by omega,
              show d / 2 < 2 ^ w by omega],
            rfl, rfl, by simp [Expr.size]⟩
        have hcnt_lt : k + 1 < 2 ^ w := by omega
        let st2 : State := { st1 with regs := Function.update st1.regs rCnt (k + 1) }
        have hstep2 : Runs w p ω (.assign rCnt (.bin .add (.reg rCnt) (.const 1))) st1 .normal st2 4 :=
          runs_assign_iff.mpr ⟨k + 1, by
            simp [st1, Expr.eval, BinOp.eval, Function.update_of_ne (Ne.symm hne), hcnt,
              show (1 : ℕ) < 2 ^ w by omega, hcnt_lt],
            rfl, rfl, by simp [Expr.size]⟩
        obtain ⟨st', c_rest, hrun_rest, hr_fin, hm_fin, hp_fin, hregs_fin, hc_rest⟩ :=
          ih (d / 2) hd2_lt (k + 1) st2
            (by omega) (le_trans (Nat.div_le_self _ _) hd)
            (fun r h1 h2 => by dsimp [st2, st1]; rw [Function.update_of_ne h2, Function.update_of_ne h1]; exact hreg r h1 h2)
            (by dsimp [st2, st1]; rw [Function.update_of_ne hne, Function.update_self])
            (by dsimp [st2]; rw [Function.update_self]) hmem hpos
        have hloop := runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st2, _, c_rest, he_cond, by decide,
          runs_seq_iff.mpr (Or.inr ⟨st1, 4, 4, hstep1, hstep2, rfl⟩), hrun_rest, rfl⟩))
        refine ⟨st', _, hloop, hr_fin, hm_fin, hp_fin, hregs_fin, ?_⟩
        simp only [Expr.size]
        rw [hlog_eq]
        omega
      · have hlog0 : Nat.log 2 d = 0 := by simp [Nat.log_eq_zero_iff, show d < 2 by omega]
        have he_cond : (Expr.bin .lt (.const 1) (.reg rCur)).eval w st = some 0 := by
          simp [Expr.eval, BinOp.eval, hcur, hd1, show (1 : ℕ) < 2 ^ w by omega]
        refine ⟨st, _, runs_loop_iff.mpr (Or.inl ⟨he_cond, rfl, rfl, rfl⟩),
          by rw [hcnt]; omega, hmem, hpos, hreg, by simp [Expr.size, hlog0]⟩
  exact hinv x0 0 st₀ (by omega) le_rfl (fun _ _ _ => rfl) hrc hrk rfl rfl

private lemma cubeRoot_log_eq_rOf (x : ℕ) : cubeRoot (Nat.log 2 x) = rOf x := by
  have h1 := cubeRoot_pow_le (Nat.log 2 x)
  have h2 := lt_cubeRoot_succ_pow (Nat.log 2 x)
  have h3 := rOf_pow_le x
  have h4 := lt_rOf_succ_pow x
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hpow := Nat.pow_le_pow_left (show cubeRoot (Nat.log 2 x) + 1 ≤ rOf x by omega) 3
    omega
  · have hpow := Nat.pow_le_pow_left (show rOf x + 1 ≤ cubeRoot (Nat.log 2 x) by omega) 3
    omega

lemma cubeRoot_loop_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (rR rIdx rCur : ℕ) (hd : [rR, rIdx, rCur].Nodup) (t : ℕ)
    (ht2w : (cubeRoot t + 1) ^ 3 < 2 ^ w) (htp : t + 1 < 2 ^ w) (h4 : 4 ≤ 2 ^ w)
    (st₀ : State) (hr_idx : st₀.regs rIdx = t) (hr_r : st₀.regs rR = 0) (hr_c : st₀.regs rCur = 1) :
    ∃ st' c,
      Runs w p ω
        (.loop (.bin .lt (.bin .mul (.bin .mul (.reg rCur) (.reg rCur)) (.reg rCur))
            (.bin .add (.reg rIdx) (.const 1)))
          (seqStmts [ .assign rR (.bin .add (.reg rR) (.const 1)),
                      .assign rCur (.bin .add (.reg rR) (.const 1)) ]))
        st₀ .normal st' c ∧
      st'.regs rR = cubeRoot t ∧
      st'.mem = st₀.mem ∧
      st'.pos = st₀.pos ∧
      (∀ r, r ≠ rR → r ≠ rIdx → r ≠ rCur → st'.regs r = st₀.regs r) ∧
      c ≤ 19 * (cubeRoot t + 1) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hd
  rcases hd with ⟨⟨hr_i, hr_c_ne⟩, hi_c, _⟩
  have hr_done := lt_cubeRoot_succ_pow t
  have hcb_lt : cubeRoot t + 1 < 2 ^ w := by
    have hle : cubeRoot t + 1 ≤ (cubeRoot t + 1) ^ 3 := by
      have := Nat.one_le_pow 2 (cubeRoot t + 1) (by omega)
      nlinarith [show (cubeRoot t + 1) ^ 3 = (cubeRoot t + 1) * (cubeRoot t + 1) * (cubeRoot t + 1) by ring]
    omega
  have hrem : ∀ rem k (st : State), k ≤ cubeRoot t → cubeRoot t - k = rem →
      st.regs rR = k → st.regs rCur = k + 1 → st.regs rIdx = t →
      st.mem = st₀.mem → st.pos = st₀.pos →
      (∀ r, r ≠ rR → r ≠ rIdx → r ≠ rCur → st.regs r = st₀.regs r) →
      ∃ st' c, Runs w p ω
        (.loop (.bin .lt (.bin .mul (.bin .mul (.reg rCur) (.reg rCur)) (.reg rCur))
            (.bin .add (.reg rIdx) (.const 1)))
          (seqStmts [ .assign rR (.bin .add (.reg rR) (.const 1)),
                      .assign rCur (.bin .add (.reg rR) (.const 1)) ]))
        st .normal st' c ∧
        st'.regs rR = cubeRoot t ∧ st'.mem = st₀.mem ∧ st'.pos = st₀.pos ∧
        (∀ r, r ≠ rR → r ≠ rIdx → r ≠ rCur → st'.regs r = st₀.regs r) ∧
        c ≤ 19 * (rem + 1) := by
    intro rem
    induction rem with
    | zero =>
      intro k st hk heq hrr hrc hri hmem hpos hregs
      have hkeq : k = cubeRoot t := by omega
      subst hkeq
      have he_cond : (Expr.bin .lt (.bin .mul (.bin .mul (.reg rCur) (.reg rCur)) (.reg rCur))
          (.bin .add (.reg rIdx) (.const 1))).eval w st = some 0 := by
        have hm1 : (cubeRoot t + 1) * (cubeRoot t + 1) < 2 ^ w := by
          have : (cubeRoot t + 1) * (cubeRoot t + 1) ≤ (cubeRoot t + 1) ^ 3 := by
            have := Nat.one_le_pow 1 (cubeRoot t + 1) (by omega)
            nlinarith [show (cubeRoot t + 1) ^ 3 = (cubeRoot t + 1) * (cubeRoot t + 1) * (cubeRoot t + 1) by ring]
          omega
        have hm2 : (cubeRoot t + 1) * (cubeRoot t + 1) * (cubeRoot t + 1) < 2 ^ w := by
          simpa only [pow_three, mul_assoc] using ht2w
        simp [Expr.eval, BinOp.eval, hrc, hri, hm1, hm2, htp,
          show (1 : ℕ) < 2 ^ w by omega, show ¬ ((cubeRoot t + 1) * (cubeRoot t + 1) * (cubeRoot t + 1) < t + 1) by
            intro hlt; have : (cubeRoot t + 1) ^ 3 < t + 1 := by simpa [pow_three, mul_assoc] using hlt
            omega]
      exact ⟨st, _, runs_loop_iff.mpr (Or.inl ⟨he_cond, rfl, rfl, rfl⟩), hrr, hmem, hpos, hregs, by simp [Expr.size]⟩
    | succ rem ih =>
      intro k st hk heq hrr hrc hri hmem hpos hregs
      have hk_lt : k < cubeRoot t := by omega
      have hk1_le : (k + 1) ^ 3 ≤ t :=
        le_trans (Nat.pow_le_pow_left hk_lt 3) (cubeRoot_pow_le t)
      have hm2 : (k + 1) * (k + 1) * (k + 1) < 2 ^ w := by
        have : (k + 1) ^ 3 < 2 ^ w := by omega
        simpa [pow_three, mul_assoc] using this
      have hm1 : (k + 1) * (k + 1) < 2 ^ w := by nlinarith
      have he_cond : (Expr.bin .lt (.bin .mul (.bin .mul (.reg rCur) (.reg rCur)) (.reg rCur))
          (.bin .add (.reg rIdx) (.const 1))).eval w st = some 1 := by
        simp [Expr.eval, BinOp.eval, hrc, hri, hm1, hm2, htp, show (1 : ℕ) < 2 ^ w by omega,
          show (k + 1) * (k + 1) * (k + 1) < t + 1 by
            have : (k + 1) ^ 3 ≤ t := hk1_le
            linarith [show (k + 1) ^ 3 = (k + 1) * (k + 1) * (k + 1) by ring]]
      have hk1_lt : k + 1 < 2 ^ w := by omega
      have hk2_lt : k + 2 < 2 ^ w := by omega
      let st1 : State := { st with regs := Function.update st.regs rR (k + 1) }
      have hstep1 : Runs w p ω (.assign rR (.bin .add (.reg rR) (.const 1))) st .normal st1 4 :=
        runs_assign_iff.mpr ⟨k + 1, by
          simp [Expr.eval, BinOp.eval, hrr, show (1 : ℕ) < 2 ^ w by omega, hk1_lt],
          rfl, rfl, by simp [Expr.size]⟩
      let st2 : State := { st1 with regs := Function.update st1.regs rCur (k + 2) }
      have hstep2 : Runs w p ω (.assign rCur (.bin .add (.reg rR) (.const 1))) st1 .normal st2 4 :=
        runs_assign_iff.mpr ⟨k + 2, by
          have heq12 : k + 1 + 1 = k + 2 := by omega
          simp [st1, Expr.eval, BinOp.eval, Function.update_self, show (1 : ℕ) < 2 ^ w by omega, heq12, hk2_lt],
          rfl, rfl, by simp [Expr.size]⟩
      obtain ⟨st', c_rest, hrun_rest, hr_fin, hm_fin, hp_fin, hregs_fin, hc_rest⟩ :=
        ih (k + 1) st2 (by omega) (by omega)
          (by dsimp [st2, st1]; rw [Function.update_of_ne hr_c_ne, Function.update_self])
          (by dsimp [st2]; rw [Function.update_self])
          (by dsimp [st2, st1]; rw [Function.update_of_ne hi_c, Function.update_of_ne (Ne.symm hr_i)]; exact hri)
          hmem hpos
          (fun r h1 h2 h3 => by dsimp [st2, st1]; rw [Function.update_of_ne h3, Function.update_of_ne h1]; exact hregs r h1 h2 h3)
      have hloop := runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st2, _, c_rest, he_cond, by decide,
        runs_seq_iff.mpr (Or.inr ⟨st1, 4, 4, hstep1, hstep2, rfl⟩), hrun_rest, rfl⟩))
      refine ⟨st', _, hloop, hr_fin, hm_fin, hp_fin, hregs_fin, ?_⟩
      simp only [Expr.size]
      omega
  exact hrem (cubeRoot t) 0 st₀ (Nat.zero_le _) (Nat.sub_zero _) hr_r hr_c hr_idx rfl rfl (fun _ _ _ _ => rfl)

private lemma pow_loop_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (rPow rCur rIdx rL : ℕ) (hd : [rPow, rCur, rIdx, rL].Nodup) (base exp : ℕ)
    (_hbase_lt : base < 2 ^ w) (hexp_lt : exp < 2 ^ w) (hpow_lt : base ^ exp < 2 ^ w)
    (hbase1 : 1 ≤ base) (h4 : 4 ≤ 2 ^ w) (st₀ : State)
    (hr_pow : st₀.regs rPow = 1) (hr_cur : st₀.regs rCur = 0)
    (hr_idx : st₀.regs rIdx = exp) (hr_L : st₀.regs rL = base) :
    ∃ st' c,
      Runs w p ω
        (.loop (.bin .lt (.reg rCur) (.reg rIdx))
          (seqStmts [ .assign rPow (.bin .mul (.reg rPow) (.reg rL)),
                      .assign rCur (.bin .add (.reg rCur) (.const 1)) ]))
        st₀ .normal st' c ∧
      st'.regs rPow = base ^ exp ∧
      st'.mem = st₀.mem ∧
      st'.pos = st₀.pos ∧
      (∀ r, r ≠ rPow → r ≠ rCur → st'.regs r = st₀.regs r) ∧
      c ≤ 13 * (exp + 1) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hd
  rcases hd with ⟨⟨hp_c, hp_i, hp_L⟩, ⟨hc_i, hc_L⟩, _, _⟩
  have hrem : ∀ rem k (st : State), k ≤ exp → exp - k = rem →
      st.regs rPow = base ^ k → st.regs rCur = k → st.regs rIdx = exp → st.regs rL = base →
      st.mem = st₀.mem → st.pos = st₀.pos →
      (∀ r, r ≠ rPow → r ≠ rCur → st.regs r = st₀.regs r) →
      ∃ st' c, Runs w p ω
        (.loop (.bin .lt (.reg rCur) (.reg rIdx))
          (seqStmts [ .assign rPow (.bin .mul (.reg rPow) (.reg rL)),
                      .assign rCur (.bin .add (.reg rCur) (.const 1)) ]))
        st .normal st' c ∧
        st'.regs rPow = base ^ exp ∧ st'.mem = st₀.mem ∧ st'.pos = st₀.pos ∧
        (∀ r, r ≠ rPow → r ≠ rCur → st'.regs r = st₀.regs r) ∧
        c ≤ 13 * (rem + 1) := by
    intro rem
    induction rem with
    | zero =>
      intro k st hk heq hrp hrc hri hrL hmem hpos hregs
      have hkeq : k = exp := by omega
      subst hkeq
      have he_cond : (Expr.bin .lt (.reg rCur) (.reg rIdx)).eval w st = some 0 := by
        simp [Expr.eval, BinOp.eval, hrc, hri]
      exact ⟨st, _, runs_loop_iff.mpr (Or.inl ⟨he_cond, rfl, rfl, rfl⟩), hrp, hmem, hpos, hregs, by simp [Expr.size]⟩
    | succ rem ih =>
      intro k st hk heq hrp hrc hri hrL hmem hpos hregs
      have hk_lt : k < exp := by omega
      have he_cond : (Expr.bin .lt (.reg rCur) (.reg rIdx)).eval w st = some 1 := by
        simp [Expr.eval, BinOp.eval, hrc, hri, hk_lt, show (1 : ℕ) < 2 ^ w by omega]
      have hmul_le : base ^ k * base ≤ base ^ exp := by
        rw [← pow_succ]; exact Nat.pow_le_pow_right hbase1 (by omega)
      have hmul_lt : base ^ (k + 1) < 2 ^ w := by rw [pow_succ]; omega
      have hk1_lt : k + 1 < 2 ^ w := by omega
      let st1 : State := { st with regs := Function.update st.regs rPow (base ^ (k + 1)) }
      have hstep1 : Runs w p ω (.assign rPow (.bin .mul (.reg rPow) (.reg rL))) st .normal st1 4 :=
        runs_assign_iff.mpr ⟨base ^ (k + 1), by
          simp [Expr.eval, BinOp.eval, hrp, hrL, ← pow_succ, hmul_lt],
          rfl, rfl, by simp [Expr.size]⟩
      let st2 : State := { st1 with regs := Function.update st1.regs rCur (k + 1) }
      have hstep2 : Runs w p ω (.assign rCur (.bin .add (.reg rCur) (.const 1))) st1 .normal st2 4 :=
        runs_assign_iff.mpr ⟨k + 1, by
          simp [st1, Expr.eval, BinOp.eval, Function.update_of_ne (Ne.symm hp_c), hrc,
            show (1 : ℕ) < 2 ^ w by omega, hk1_lt],
          rfl, rfl, by simp [Expr.size]⟩
      obtain ⟨st', c_rest, hrun_rest, hr_fin, hm_fin, hp_fin, hregs_fin, hc_rest⟩ :=
        ih (k + 1) st2 (by omega) (by omega)
          (by dsimp [st2, st1]; rw [Function.update_of_ne hp_c, Function.update_self])
          (by dsimp [st2]; rw [Function.update_self])
          (by dsimp [st2, st1]; rw [Function.update_of_ne (Ne.symm hc_i), Function.update_of_ne (Ne.symm hp_i)]; exact hri)
          (by dsimp [st2, st1]; rw [Function.update_of_ne (Ne.symm hc_L), Function.update_of_ne (Ne.symm hp_L)]; exact hrL)
          hmem hpos
          (fun r h1 h2 => by dsimp [st2, st1]; rw [Function.update_of_ne h2, Function.update_of_ne h1]; exact hregs r h1 h2)
      have hloop := runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st2, _, c_rest, he_cond, by decide,
        runs_seq_iff.mpr (Or.inr ⟨st1, 4, 4, hstep1, hstep2, rfl⟩), hrun_rest, rfl⟩))
      refine ⟨st', _, hloop, hr_fin, hm_fin, hp_fin, hregs_fin, ?_⟩
      simp only [Expr.size]
      omega
  exact hrem exp 0 st₀ (Nat.zero_le _) (Nat.sub_zero _) hr_pow hr_cur hr_idx hr_L rfl rfl (fun _ _ _ => rfl)

theorem computePhiDenStmt_triple {w : ℕ} {p : Program}
    {K_nat thr m : ℕ} (hK : 1 ≤ K_nat)
    {rM rOut rL rR rPow rIdx rCur : ℕ}
    (hd : [rM, rOut, rL, rR, rPow, rIdx, rCur].Nodup)
    (st₀ : State) (hrm : st₀.regs rM = m)
    (hm_lt : 4 * m + 2 < 2 ^ w)
    (hcube_lt : (Nat.log 2 (4 * m + 2) + 2) ^ 3 < 2 ^ w)
    (hphi_lt : phiDenHalf K_nat thr m < 2 ^ w) :
    Triple w p (fun st => st = st₀)
      (computePhiDenStmt K_nat thr rM rOut rL rR rPow rIdx rCur)
      (normalPost fun st' =>
        st'.regs rOut = phiDenHalf K_nat thr m ∧
        st'.mem = st₀.mem ∧
        st'.pos = st₀.pos ∧
        ∀ r, r ≠ rOut → r ≠ rL → r ≠ rR → r ≠ rPow → r ≠ rIdx → r ≠ rCur →
          st'.regs r = st₀.regs r)
      (fun _ => 120 * (Nat.log 2 (4 * m + 2) + K_nat * (rOf (4 * m)) ^ 2 + 4)) := by
  intro st ω hst
  subst st
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hd
  rcases hd with ⟨⟨hm_out, hm_L, hm_R, hm_pow, hm_idx, hm_cur⟩,
    ⟨ho_L, ho_R, ho_pow, ho_idx, ho_cur⟩, ⟨hL_R, hL_pow, hL_idx, hL_cur⟩,
    ⟨hR_pow, hR_idx, hR_cur⟩, ⟨hp_idx, hp_cur⟩, hi_cur, _⟩
  set L := Nat.log 2 (4 * m + 2) + 2
  set r := rOf (4 * m)
  set E := K_nat * r ^ 2
  have hphi_rhs : 200 * K_nat * L ^ E ≤ phiDenHalf K_nat thr m := le_max_right _ _
  have hpow_le : L ^ E ≤ phiDenHalf K_nat thr m := by
    have h1 : 1 ≤ 200 * K_nat := by omega
    calc L ^ E = 1 * L ^ E := (one_mul _).symm
      _ ≤ 200 * K_nat * L ^ E := Nat.mul_le_mul_right _ h1
      _ ≤ phiDenHalf K_nat thr m := hphi_rhs
  have hK2w : 200 * K_nat < 2 ^ w := by
    have : 200 * K_nat ≤ phiDenHalf K_nat thr m :=
      le_trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega))) hphi_rhs
    omega
  have h4 : 4 ≤ 2 ^ w := by omega
  have h4lt : 4 < 2 ^ w := by omega
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have hw0 : w ≠ 0 := by rintro rfl; simp at h1w
  have hL_def : L ≤ L ^ 3 := by
    have := Nat.one_le_pow 2 L (by dsimp [L]; omega)
    nlinarith [show L ^ 3 = L * L * L by ring]
  have hL_lt2w : L < 2 ^ w := by exact lt_of_le_of_lt hL_def (by simpa [L] using hcube_lt)
  have h4m_lt2w : 4 * m < 2 ^ w := by omega
  have hlog4m_lt : Nat.log 2 (4 * m) ≤ Nat.log 2 (4 * m + 2) := Nat.log_mono_right (by omega)
  have hcb_le_L : cubeRoot (Nat.log 2 (4 * m)) + 1 ≤ L := by
    have hr3 : (cubeRoot (Nat.log 2 (4 * m))) ^ 3 ≤ Nat.log 2 (4 * m) := cubeRoot_pow_le _
    by_contra hgt
    have hge : L ≤ cubeRoot (Nat.log 2 (4 * m)) := by omega
    have := Nat.pow_le_pow_left hge 3
    have hge2 : 8 ≤ L ^ 3 := by
      have : 2 ≤ L := by dsimp [L]; omega
      exact le_trans (by norm_num : 2 ^ 3 ≤ _) (Nat.pow_le_pow_left this 3)
    omega
  have hr_cube_lt : (cubeRoot (Nat.log 2 (4 * m)) + 1) ^ 3 < 2 ^ w :=
    lt_of_le_of_lt (Nat.pow_le_pow_left hcb_le_L 3) (by simpa [L] using hcube_lt)
  have hE_lt : E < 2 ^ w := by
    have : E ≤ L ^ E := le_of_lt (Nat.lt_pow_self (a := L) (by dsimp [L]; omega : 1 < L))
    omega
  have hKrr_lt : K_nat * r < 2 ^ w := by
    have : K_nat * r ≤ E := by
      rcases r with _ | r'
      · simp [E]
      · dsimp [E]
        calc K_nat * (r' + 1) = K_nat * (r' + 1) * 1 := by ring
          _ ≤ K_nat * (r' + 1) * (r' + 1) := Nat.mul_le_mul_left _ (by omega)
          _ = K_nat * (r' + 1) ^ 2 := by ring
    omega
  have hthr_lt : thr + 1 < 2 ^ w := by
    have := le_phiDenHalf_thr K_nat thr m
    omega
  dsimp only [computePhiDenStmt, seqStmts]
  let st0a : State := { st₀ with regs := Function.update st₀.regs rCur (4 * m + 2) }
  let st1 : State := { st0a with regs := Function.update st0a.regs rL 0 }
  have h1a : Runs w p ω (.assign rCur (.bin .add (.bin .mul (.const 4) (.reg rM)) (.const 2)))
      st₀ .normal st0a 6 :=
    runs_assign_iff.mpr ⟨4 * m + 2, by
      simp [Expr.eval, BinOp.eval, hrm, h4lt, show (2 : ℕ) < 2 ^ w by omega, h4m_lt2w, hm_lt],
      rfl, rfl, by simp [Expr.size]⟩
  have h1b : Runs w p ω (.assign rL (.const 0)) st0a .normal st1 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0w], rfl, rfl, by simp [Expr.size]⟩
  obtain ⟨st2, c2, hr2, hr2_L, hm2, hp2, hreg2, hc2⟩ :=
    log2_loop_runs rCur rL (Ne.symm hL_cur) (4 * m + 2) hm_lt h4 st1
      (by dsimp [st1, st0a]; rw [Function.update_of_ne (Ne.symm hL_cur), Function.update_self])
      (by simp [st1]) (by dsimp [L] at hL_lt2w; omega)
  let st3 : State := { st2 with regs := Function.update st2.regs rL L }
  have h3a : Runs w p ω (.assign rL (.bin .add (.reg rL) (.const 2))) st2 .normal st3 4 :=
    runs_assign_iff.mpr ⟨L, by
      simp [Expr.eval, BinOp.eval, hr2_L, show (2 : ℕ) < 2 ^ w by omega, hL_lt2w, L],
      rfl, rfl, by simp [Expr.size]⟩
  let st4a : State := { st3 with regs := Function.update st3.regs rCur (4 * m) }
  have h4a : Runs w p ω (.assign rCur (.bin .mul (.const 4) (.reg rM))) st3 .normal st4a 4 :=
    runs_assign_iff.mpr ⟨4 * m, by
      have hm_st3 : st3.regs rM = m := by
        dsimp [st3]; rw [Function.update_of_ne hm_L, hreg2 rM hm_cur hm_L]
        dsimp [st1, st0a]
        rw [Function.update_of_ne hm_L, Function.update_of_ne hm_cur, hrm]
      simp [Expr.eval, BinOp.eval, hm_st3, h4lt, h4m_lt2w],
      rfl, rfl, by simp [Expr.size]⟩
  let st4 : State := { st4a with regs := Function.update st4a.regs rR 0 }
  have h4b : Runs w p ω (.assign rR (.const 0)) st4a .normal st4 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0w], rfl, rfl, by simp [Expr.size]⟩
  obtain ⟨st5, c5, hr5, hr5_R, hm5, hp5, hreg5, hc5⟩ :=
    log2_loop_runs rCur rR (Ne.symm hR_cur) (4 * m) h4m_lt2w h4 st4
      (by dsimp [st4, st4a]; rw [Function.update_of_ne (Ne.symm hR_cur), Function.update_self])
      (by simp [st4]) (by dsimp [L] at hL_lt2w; omega)
  let st6a : State := { st5 with regs := Function.update st5.regs rIdx (Nat.log 2 (4 * m)) }
  have h6a : Runs w p ω (.assign rIdx (.reg rR)) st5 .normal st6a 2 :=
    runs_assign_iff.mpr ⟨Nat.log 2 (4 * m), by simp [Expr.eval, hr5_R], rfl, rfl, by simp [Expr.size]⟩
  let st6b : State := { st6a with regs := Function.update st6a.regs rR 0 }
  have h6b : Runs w p ω (.assign rR (.const 0)) st6a .normal st6b 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0w], rfl, rfl, by simp [Expr.size]⟩
  let st6 : State := { st6b with regs := Function.update st6b.regs rCur 1 }
  have h6c : Runs w p ω (.assign rCur (.const 1)) st6b .normal st6 2 :=
    runs_assign_iff.mpr ⟨1, by simp [Expr.eval, h1w], rfl, rfl, by simp [Expr.size]⟩
  obtain ⟨st7, c7, hr7, hr7_R, hm7, hp7, hreg7, hc7⟩ :=
    cubeRoot_loop_runs rR rIdx rCur (by simp [List.nodup_cons, hR_idx, hR_cur, hi_cur])
      (Nat.log 2 (4 * m)) hr_cube_lt (by dsimp [L] at hL_lt2w; omega) h4 st6
      (by dsimp [st6, st6b, st6a]; rw [Function.update_of_ne hi_cur, Function.update_of_ne (Ne.symm hR_idx), Function.update_self])
      (by dsimp [st6, st6b]; rw [Function.update_of_ne hR_cur, Function.update_self])
      (by simp [st6])
  have hr7_R' : st7.regs rR = r := by rw [hr7_R, cubeRoot_log_eq_rOf]
  have hc7' : c7 ≤ 19 * (r + 1) := by simpa [r, cubeRoot_log_eq_rOf] using hc7
  let st8a : State := { st7 with regs := Function.update st7.regs rIdx E }
  have h8a : Runs w p ω (.assign rIdx (.bin .mul (.bin .mul (.const K_nat) (.reg rR)) (.reg rR)))
      st7 .normal st8a 6 :=
    runs_assign_iff.mpr ⟨E, by
      have hK_lt : K_nat < 2 ^ w := by omega
      have hm1 : K_nat * r < 2 ^ w := hKrr_lt
      have hm2 : K_nat * r * r = E := by dsimp [E]; ring
      simp [Expr.eval, BinOp.eval, hK_lt, hr7_R', hm1, hm2, E, hE_lt],
      rfl, rfl, by simp [Expr.size]⟩
  let st8b : State := { st8a with regs := Function.update st8a.regs rPow 1 }
  have h8b : Runs w p ω (.assign rPow (.const 1)) st8a .normal st8b 2 :=
    runs_assign_iff.mpr ⟨1, by simp [Expr.eval, h1w], rfl, rfl, by simp [Expr.size]⟩
  let st8 : State := { st8b with regs := Function.update st8b.regs rCur 0 }
  have h8c : Runs w p ω (.assign rCur (.const 0)) st8b .normal st8 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0w], rfl, rfl, by simp [Expr.size]⟩
  have hst8_L : st8.regs rL = L := by
    have h7L : st7.regs rL = L := by
      rw [hreg7 rL hL_R hL_idx hL_cur]
      dsimp [st6, st6b, st6a]
      rw [Function.update_of_ne hL_cur, Function.update_of_ne hL_R,
        Function.update_of_ne hL_idx]
      rw [hreg5 rL hL_cur hL_R]
      dsimp [st4, st4a]
      rw [Function.update_of_ne hL_R, Function.update_of_ne hL_cur]
      simp [st3]
    dsimp [st8, st8b, st8a]
    rw [Function.update_of_ne hL_cur, Function.update_of_ne hL_pow,
      Function.update_of_ne hL_idx, h7L]
  obtain ⟨st9, c9, hr9, hr9_pow, hm9, hp9, hreg9, hc9⟩ :=
    pow_loop_runs rPow rCur rIdx rL (by simp [List.nodup_cons, hp_cur, hp_idx, Ne.symm hL_pow,
        Ne.symm hi_cur, Ne.symm hL_cur, Ne.symm hL_idx])
      L E hL_lt2w hE_lt (by omega) (by dsimp [L]; omega) h4 st8
      (by dsimp [st8, st8b]; rw [Function.update_of_ne hp_cur, Function.update_self])
      (by simp [st8])
      (by dsimp [st8, st8b, st8a]; rw [Function.update_of_ne hi_cur, Function.update_of_ne (Ne.symm hp_idx), Function.update_self])
      hst8_L
  let st10 : State := { st9 with regs := Function.update st9.regs rOut (200 * K_nat * L ^ E) }
  have h10 : Runs w p ω (.assign rOut (.bin .mul (.const (200 * K_nat)) (.reg rPow))) st9 .normal st10 4 :=
    runs_assign_iff.mpr ⟨200 * K_nat * L ^ E, by
      simp [Expr.eval, BinOp.eval, hK2w, hr9_pow, show 200 * K_nat * L ^ E < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  obtain ⟨st11, c11, hr11, hr11_out, hm11, hp11, hreg11, hc11⟩ :
      ∃ st11 c11, Runs w p ω (.cond (.bin .lt (.reg rOut) (.const (thr + 1)))
          (.assign rOut (.const (thr + 1))) .nop) st10 .normal st11 c11 ∧
        st11.regs rOut = phiDenHalf K_nat thr m ∧
        st11.mem = st10.mem ∧ st11.pos = st10.pos ∧
        (∀ r, r ≠ rOut → st11.regs r = st10.regs r) ∧ c11 ≤ 6 := by
    by_cases hlt : 200 * K_nat * L ^ E < thr + 1
    · have hc : (Expr.bin .lt (.reg rOut) (.const (thr + 1))).eval w st10 = some 1 := by
        simp [st10, Expr.eval, BinOp.eval, hthr_lt, hlt, hw0]
      let st11' : State := { st10 with regs := Function.update st10.regs rOut (thr + 1) }
      have ha : Runs w p ω (.assign rOut (.const (thr + 1))) st10 .normal st11' 2 :=
        runs_assign_iff.mpr ⟨thr + 1, by simp [Expr.eval, hthr_lt], rfl, rfl, by simp [Expr.size]⟩
      refine ⟨st11', 6, runs_cond_iff.mpr ⟨1, 2, hc, by simpa using ha, by simp [Expr.size]⟩,
        by dsimp [st11', L, r, E] at hlt ⊢; rw [phiDenHalf, Function.update_self, max_eq_left (le_of_lt hlt)],
        rfl, rfl, fun q hq => by dsimp [st11']; exact Function.update_of_ne hq _ _, le_rfl⟩
    · have hc : (Expr.bin .lt (.reg rOut) (.const (thr + 1))).eval w st10 = some 0 := by
        simp [st10, Expr.eval, BinOp.eval, hthr_lt, hlt]
      refine ⟨st10, 5, runs_cond_iff.mpr ⟨0, 1, hc, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩,
        by dsimp [st10, L, r, E] at hlt ⊢; rw [phiDenHalf, Function.update_self, max_eq_right (Nat.le_of_not_lt hlt)],
        rfl, rfl, fun _ _ => rfl, by omega⟩
  have hr_pres : ∀ q, q ≠ rOut → q ≠ rL → q ≠ rR → q ≠ rPow → q ≠ rIdx → q ≠ rCur →
      st11.regs q = st₀.regs q := by
    intro q hqo hqL hqR hqP hqI hqC
    rw [hreg11 q hqo]
    dsimp [st10]
    rw [Function.update_of_ne hqo, hreg9 q hqP hqC]
    dsimp [st8, st8b, st8a]
    rw [Function.update_of_ne hqC, Function.update_of_ne hqP, Function.update_of_ne hqI, hreg7 q hqR hqI hqC]
    dsimp [st6, st6b, st6a]
    rw [Function.update_of_ne hqC, Function.update_of_ne hqR, Function.update_of_ne hqI, hreg5 q hqC hqR]
    dsimp [st4, st4a]
    rw [Function.update_of_ne hqR, Function.update_of_ne hqC]
    dsimp [st3]
    rw [Function.update_of_ne hqL, hreg2 q hqC hqL]
    dsimp [st1, st0a]
    rw [Function.update_of_ne hqL, Function.update_of_ne hqC]
  have hmem_fin : st11.mem = st₀.mem := by
    rw [hm11]; dsimp [st10]; rw [hm9]; dsimp [st8, st8b, st8a]; rw [hm7]
    dsimp [st6, st6b, st6a]; rw [hm5]; dsimp [st4, st4a]; dsimp [st3]; rw [hm2]
  have hpos_fin : st11.pos = st₀.pos := by
    rw [hp11]; dsimp [st10]; rw [hp9]; dsimp [st8, st8b, st8a]; rw [hp7]
    dsimp [st6, st6b, st6a]; rw [hp5]; dsimp [st4, st4a]; dsimp [st3]; rw [hp2]
  have runs_seq' : ∀ {s₁ s₂ : Stmt} {a b c : State} {k₁ k₂ : ℕ},
      Runs w p ω s₁ a .normal b k₁ → Runs w p ω s₂ b .normal c k₂ →
      Runs w p ω (.seq s₁ s₂) a .normal c (k₁ + k₂ + 1) :=
    fun h1 h2 => runs_seq_iff.mpr (Or.inr ⟨_, _, _, h1, h2, rfl⟩)
  have hfull :=
    runs_seq' h1a <| runs_seq' h1b <| runs_seq' hr2 <| runs_seq' h3a <| runs_seq' h4a <| runs_seq' h4b <|
    runs_seq' hr5 <| runs_seq' h6a <| runs_seq' h6b <| runs_seq' h6c <| runs_seq' hr7 <| runs_seq' h8a <|
    runs_seq' h8b <| runs_seq' h8c <| runs_seq' hr9 <| runs_seq' h10 hr11
  have hr_le_log : r ≤ Nat.log 2 (4 * m + 2) := by
    by_contra hgt
    have hge : Nat.log 2 (4 * m + 2) + 1 ≤ r := by omega
    have h1 : r ^ 3 ≤ Nat.log 2 (4 * m) := rOf_pow_le (4 * m)
    have h2 : r ≤ r ^ 3 := by
      rcases r with _ | r'
      · omega
      · exact Nat.le_self_pow (by decide) _
    omega
  refine ⟨.normal, st11, _, hfull, ⟨hr11_out, hmem_fin, hpos_fin, hr_pres⟩, ?_⟩
  omega

end MinCostFlow.Expander
