module

public import MinCostFlow.Expander.PathDSProg.MemoryLayout
public import MinCostFlow.Expander.PathDSProg.BoundsLoopProg
public import MinCostFlow.Expander.BfsPathProg

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Runtime Blocks and Procedures for `PathDSImpl`

Defines the deterministic (`Stmt.NoRand`) helper blocks, top-level procedures
`initProc`, `deleteProc`, `getPathProc`, the procedure table `pathDSProcs`,
and the deterministic call bridge `csCall_stripRand` for `[CS21]`.

1. `zeroRangeStmt`: zeros `mem[lo..hi)` using `r20 = lo, r21 = hi` (`r < 20` preserved).
2. `qOfStmt`: computes `r21 := qOf M` from `r20 = M` (`r < 20`, `mem` preserved).
3. `csGamma3mStmt`: computes `r21 := c * csGamma Kγ (3 * m)` from `r20 = m` (`r < 20`, `mem` preserved).
4. `fbHStmt`: computes `r22 := C_cap = 40 * d + 1` and `r23 := H` (`r < 20`, `mem` preserved).
5. `initProc`, `deleteProc`, `getPathProc`, and `pathDSProcs`.
-/

@[expose] public section

namespace MinCostFlow.Expander.PathDSProg

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Range Zeroing (`zeroRangeStmt`) -/

/-- Zeros memory addresses `[r20, r21)`, using `r22` as loop index. Preserves `r < 20` and `pos`. -/
def zeroRangeStmt : Stmt :=
  forRange 22 (.reg 20) (.reg 21) (.store (.reg 22) (.const 0))

lemma zeroRangeStmt_noRand : zeroRangeStmt.NoRand := by
  simp [zeroRangeStmt, forRange, forUp, Stmt.NoRand]

theorem zeroRangeStmt_triple {w lo hi : ℕ} {p : Program}
    (st₀ : State) (hr20 : st₀.regs 20 = lo) (hr21 : st₀.regs 21 = hi)
    (hle : lo ≤ hi) (hhi_w : lo < hi → hi < 2 ^ w) (hw2 : 1 < 2 ^ w) :
    Triple w p (fun st => st = st₀) zeroRangeStmt
      (normalPost fun st' =>
        MemFrame st₀.mem st'.mem lo hi ∧
        (∀ a, lo ≤ a → a < hi → st'.mem a = 0) ∧
        (∀ r < 20, st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos)
      (fun _ => 12 * (hi - lo) + 10) := by
  let Inv : ℕ → State → Prop := fun i st =>
    lo ≤ i ∧ i ≤ hi ∧ st.regs 20 = lo ∧ st.regs 21 = hi ∧ st.regs 22 = i ∧
    MemFrame st₀.mem st.mem lo hi ∧
    (∀ a, lo ≤ a → a < i → st.mem a = 0) ∧
    (∀ r < 20, st.regs r = st₀.regs r) ∧ st.pos = st₀.pos
  have hloop := Triple.forRange_const (p := p) (P := fun st => st = st₀) (r := 22)
    (lo := .reg 20) (hi := .reg 21) (body := .store (.reg 22) (.const 0))
    (Inv := Inv) 3 lo hi hle hw2 hhi_w
    (fun st hst => by
      subst hst
      refine ⟨Expr.eval_reg_of_eq hr20, le_rfl, hle, ?_, ?_, ?_,
        memFrame_refl _ _ _, fun _ h1 h2 => absurd h1 (not_le.mpr h2),
        fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)], rfl⟩
      · dsimp only; rw [Function.update_of_ne (by decide)]; exact hr20
      · dsimp only; rw [Function.update_of_ne (by decide)]; exact hr21
      · simp)
    (fun _ _ _ _ hI => hI.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.2.1)
    (fun i hlo_i hi_lt st ω ⟨_, _, h20, h21, h22, hfr, hz, hlt20, hpos⟩ => by
      have hiw : i < 2 ^ w := lt_trans hi_lt (hhi_w (lt_of_le_of_lt hlo_i hi_lt))
      have hz_w : 0 < 2 ^ w := by omega
      refine runs_start_le ?_
      wram_run
      · refine ⟨⟨by omega, hi_lt, by simp [h20], by simp [h21], by simp, ?_, fun a ha1 ha2 => ?_,
          fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hlt20 r hr, hpos⟩, h22⟩
        · dsimp only
          exact memFrame_trans hfr (memFrame_update (by omega) (by omega))
        · dsimp only
          rcases Nat.lt_succ_iff_lt_or_eq.mp ha2 with ha2' | rfl
          · rw [Function.update_of_ne (by omega)]; exact hz a ha1 ha2'
          · rw [Function.update_self]
      · wram_cost)
  refine hloop.conseq (fun _ h => h) ?_ (fun _ _ => ?_)
  · intro o st' h
    cases o with
    | returned _ => exact False.elim h
    | normal =>
      rcases h with ⟨_, _, _, _, _, hfr, hz, hlt20, hpos⟩
      exact ⟨hfr, hz, hlt20, hpos⟩
  · simp only [Expr.size]; omega

/-! ## 2. `qOfStmt` (`r20 = M` → `r21 := qOf M`) -/

/-- Computes `r21 := qOf M` from `r20 = M`, using scratch registers `20..25`. Preserves `r < 20`,
`mem`, and `pos`. -/
def qOfStmt : Stmt :=
  .assign 22 (.bin .add (.reg 20) (.const 2)) ;;
  .assign 23 (.const 0) ;;
  .loop (.bin .lt (.const 1) (.reg 22))
    (.assign 22 (.bin .div (.reg 22) (.const 2)) ;;
     .assign 23 (.bin .add (.reg 23) (.const 1))) ;;
  .assign 24 (.reg 23) ;;
  .assign 25 (.const 0) ;;
  .assign 22 (.const 1) ;;
  kthRootLoop 25 22 24 (pow8Expr 22) ;;
  .assign 21 (.bin .add (.reg 25) (.const 2))

lemma qOfStmt_noRand : qOfStmt.NoRand := by
  simp [qOfStmt, kthRootLoop_noRand, Stmt.NoRand]

theorem qOfStmt_triple {w M : ℕ} {p : Program}
    (st₀ : State) (hr20 : st₀.regs 20 = M)
    (hM2_w : M + 2 < 2 ^ w) (hq8_w : (qRoot M + 1) ^ 8 < 2 ^ w)
    (hq2_w : qRoot M + 2 < 2 ^ w) (h4w : 4 ≤ 2 ^ w) :
    Triple w p (fun st => st = st₀) qOfStmt
      (normalPost fun st' =>
        st'.regs 21 = qOf M ∧ st'.mem = st₀.mem ∧ st'.pos = st₀.pos ∧
        ∀ r < 20, st'.regs r = st₀.regs r)
      (fun _ => 65 * (Nat.log 2 (M + 2) + 1) + 80) := by
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have hl_w : Nat.log 2 (M + 2) < 2 ^ w :=
    lt_trans (Nat.log_lt_self 2 (by omega)) hM2_w
  have hl1_w : Nat.log 2 (M + 2) + 1 < 2 ^ w := by
    by_cases hM0 : M = 0
    · subst hM0; have := Nat.log_lt_self 2 (by decide : 0 + 2 ≠ 0); omega
    · have := Nat.log_lt_self 2 (by omega : M + 2 ≠ 0)
      omega
  have hpow8 : ∀ st, st.regs 22 ≤ qRoot M + 1 →
      (pow8Expr 22).eval w st = some (st.regs 22 ^ 8) := fun st hs =>
    pow8Expr_eval rfl (lt_of_le_of_lt (Nat.pow_le_pow_left hs 8) hq8_w)
  intro st ω hst; subst hst
  refine runs_start_le ?_
  let st1 : State := { st with regs := Function.update st.regs 22 (M + 2) }
  refine runs_seq_assign_le (v := M + 2)
    (Expr.eval_add (Expr.eval_reg_of_eq hr20) (Expr.eval_const h2w) hM2_w) ?_
  let st2 : State := { st1 with regs := Function.update st1.regs 23 0 }
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  have hr3_tr := log2Loop_triple (w := w) (p := p) 22 23 (M + 2) (by decide) hM2_w h4w hl_w st2
    (by dsimp [st2, st1]; rw [Function.update_of_ne (by decide), Function.update_self])
    (by simp [st2])
  refine runs_seq_triple_le hr3_tr rfl ?_
  intro st3 ⟨hr3_23, hm3, hp3, hreg3⟩
  let st4 : State := { st3 with regs := Function.update st3.regs 24 (Nat.log 2 (M + 2)) }
  refine runs_seq_assign_le (v := Nat.log 2 (M + 2)) (Expr.eval_reg_of_eq hr3_23) ?_
  let st5 : State := { st4 with regs := Function.update st4.regs 25 0 }
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  let st6 : State := { st5 with regs := Function.update st5.regs 22 1 }
  refine runs_seq_assign_le (v := 1) (Expr.eval_const h1w) ?_
  have h8ans : (qRoot M) ^ 8 ≤ Nat.log 2 (M + 2) ∧ Nat.log 2 (M + 2) < (qRoot M + 1) ^ 8 :=
    eighthRoot_iff.mp rfl
  have hq_tr := kthRootLoop_triple (w := w) (p := p) 25 22 24 8 (Nat.log 2 (M + 2)) (qRoot M)
    (pow8Expr 22) (by decide) (by decide) h8ans hpow8 hl1_w hq8_w st6
    (by dsimp [st6, st5]; rw [Function.update_of_ne (by decide), Function.update_self])
    (by simp [st6])
    (by dsimp [st6, st5, st4]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self])
  refine runs_seq_triple_le hq_tr rfl ?_
  intro st7 ⟨hr7_25, hm7, hp7, hreg7⟩
  have hqM : qRoot M + 2 = qOf M := (qOf_eq_qRoot_add_two M).symm
  have he_out : (Expr.bin .add (.reg 25) (.const 2)).eval w st7 = some (qOf M) := by
    rw [← hqM]
    exact Expr.eval_add (Expr.eval_reg_of_eq hr7_25) (Expr.eval_const h2w) hq2_w
  refine runs_assign_le he_out ?_ ?_
  · refine ⟨by simp, hm7.trans hm3, hp7.trans hp3, fun r hr => ?_⟩
    dsimp only
    rw [Function.update_of_ne (by omega)]
    rw [hreg7 r (by omega) (by omega)]
    dsimp only [st6, st5, st4]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    rw [hreg3 r (by omega) (by omega)]
    dsimp only [st2, st1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · have hqroot_le : qRoot M ≤ Nat.log 2 (M + 2) := by
      have h1 := qRoot_pow_eight_le M
      have h2 := Nat.le_self_pow (by decide : 8 ≠ 0) (qRoot M)
      omega
    have hpow_sz : (pow8Expr 22).size = 15 := rfl
    rw [hpow_sz]
    simp only [Expr.size]
    nlinarith

/-! ## 3. `csGamma3mStmt` (`r20 = m` → `r21 := c * csGamma Kγ (3 * m)`) -/

/-- Computes `r21 := c * Cited.csGamma Kγ (3 * m)` from `r20 = m`, using scratch `20..27`.
Preserves `r < 20`, `mem`, and `pos`. -/
def csGamma3mStmt (Kγ c : ℕ) : Stmt :=
  .assign 22 (.bin .mul (.const 3) (.reg 20)) ;;
  csGammaExpBlock Kγ 22 23 24 25 26 27 ;;
  .assign 21 (.bin .mul (.const c) (.bin .shiftLeft (.const 1) (.reg 23)))

lemma csGamma3mStmt_noRand (Kγ c : ℕ) : (csGamma3mStmt Kγ c).NoRand := by
  simp [csGamma3mStmt, csGammaExpBlock_noRand, Stmt.NoRand]

theorem csGamma3mStmt_triple {w Kγ c m : ℕ} {p : Program}
    (hc : 1 ≤ c) (st₀ : State) (hr20 : st₀.regs 20 = m)
    (hK_w : Kγ < 2 ^ w) (hc_w : c < 2 ^ w) (h3m_w : 3 * m < 2 ^ w)
    (hcube_w : (Nat.log 2 (3 * m) + 2) ^ 4 < 2 ^ w)
    (hce_w : csGammaExp Kγ (3 * m) < 2 ^ w)
    (hprod_w : c * Cited.csGamma Kγ (3 * m) < 2 ^ w)
    (h4w : 4 ≤ 2 ^ w) :
    Triple w p (fun st => st = st₀) (csGamma3mStmt Kγ c)
      (normalPost fun st' =>
        st'.regs 21 = c * Cited.csGamma Kγ (3 * m) ∧ st'.mem = st₀.mem ∧ st'.pos = st₀.pos ∧
        ∀ r < 20, st'.regs r = st₀.regs r)
      (fun _ => 35 * (Nat.log 2 (3 * m) + 1) + 80) := by
  have h1w : 1 < 2 ^ w := by omega
  have h3w : 3 < 2 ^ w := by omega
  intro st ω hst; subst hst
  refine runs_start_le ?_
  let st1 : State := { st with regs := Function.update st.regs 22 (3 * m) }
  refine runs_seq_assign_le (v := 3 * m)
    (Expr.eval_mul (Expr.eval_const h3w) (Expr.eval_reg_of_eq hr20) h3m_w) ?_
  have hcs_tr := csGammaExpBlock_triple (w := w) (p := p) Kγ 22 23 24 25 26 27 (3 * m)
    (by decide) ⟨by decide, by decide⟩ hK_w h3m_w hcube_w hce_w h4w st1 (by simp [st1])
  refine runs_seq_triple_le hcs_tr rfl ?_
  intro st2 ⟨hr23, hm2, hp2, hreg2⟩
  have hgam_eq : Cited.csGamma Kγ (3 * m) = 2 ^ csGammaExp Kγ (3 * m) := rfl
  have hsh : 1 <<< csGammaExp Kγ (3 * m) = Cited.csGamma Kγ (3 * m) := by
    rw [Nat.shiftLeft_eq, one_mul, ← hgam_eq]
  have hgam_w : 1 <<< csGammaExp Kγ (3 * m) < 2 ^ w := by
    rw [hsh]
    exact lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hc) hprod_w
  have he_sh : (Expr.bin .shiftLeft (.const 1) (.reg 23)).eval w st2 =
      some (1 <<< csGammaExp Kγ (3 * m)) :=
    Expr.eval_shiftLeft (Expr.eval_const h1w) (Expr.eval_reg_of_eq hr23) hgam_w
  have he_out : (Expr.bin .mul (.const c) (.bin .shiftLeft (.const 1) (.reg 23))).eval w st2 =
      some (c * Cited.csGamma Kγ (3 * m)) := by
    have := Expr.eval_mul (Expr.eval_const hc_w) he_sh (by simpa only [hsh] using hprod_w)
    simpa only [hsh] using this
  refine runs_assign_le he_out ?_ ?_
  · refine ⟨by simp, hm2, hp2, fun r hr => ?_⟩
    dsimp only
    rw [Function.update_of_ne (by omega)]
    rw [hreg2 r (by omega) (by omega) (by omega) (by omega) (by omega)]
    dsimp only [st1]
    rw [Function.update_of_ne (by omega)]
  · simp only [Expr.size]; omega

/-! ## 4. `fbHStmt` (`r20 = d, r21 = m_s` → `r22 := C_cap, r23 := H`) -/

/-- Computes `r22 := 40 * d + 1` and `r23 := 4 * r22 * (Nat.log 2 (2 * m_s + 1) + 1) + 2`,
using scratch `20..25`. Preserves `r < 20`, `mem`, and `pos`. -/
def fbHStmt : Stmt :=
  .assign 22 (.bin .add (.bin .mul (.const 40) (.reg 20)) (.const 1)) ;;
  .assign 24 (.bin .add (.bin .mul (.const 2) (.reg 21)) (.const 1)) ;;
  .assign 25 (.const 0) ;;
  .loop (.bin .lt (.const 1) (.reg 24))
    (.assign 24 (.bin .div (.reg 24) (.const 2)) ;;
     .assign 25 (.bin .add (.reg 25) (.const 1))) ;;
  .assign 23 (.bin .add (.bin .mul (.bin .mul (.const 4) (.reg 22))
    (.bin .add (.reg 25) (.const 1))) (.const 2))

lemma fbHStmt_noRand : fbHStmt.NoRand := by
  simp [fbHStmt, Stmt.NoRand]

theorem fbHStmt_triple {w d m_s : ℕ} {p : Program}
    (hd : 1 ≤ d) (st₀ : State) (hr20 : st₀.regs 20 = d) (hr21 : st₀.regs 21 = m_s)
    (hm2_w : 2 * m_s + 1 < 2 ^ w)
    (hH_w : 4 * (40 * d + 1) * (Nat.log 2 (2 * m_s + 1) + 1) + 2 < 2 ^ w) :
    Triple w p (fun st => st = st₀) fbHStmt
      (normalPost fun st' =>
        st'.regs 22 = 40 * d + 1 ∧
        st'.regs 23 = 4 * (40 * d + 1) * (Nat.log 2 (2 * m_s + 1) + 1) + 2 ∧
        st'.mem = st₀.mem ∧ st'.pos = st₀.pos ∧
        ∀ r < 20, st'.regs r = st₀.regs r)
      (fun _ => 15 * (Nat.log 2 (2 * m_s + 1) + 1) + 40) := by
  set C_cap := 40 * d + 1
  set l := Nat.log 2 (2 * m_s + 1)
  set H := 4 * C_cap * (l + 1) + 2
  have hC_le_H : C_cap ≤ H := by
    have h1 : C_cap ≤ C_cap * (l + 1) := Nat.le_mul_of_pos_right C_cap (Nat.succ_pos _)
    have h2 : 4 * C_cap * (l + 1) = 4 * (C_cap * (l + 1)) := mul_assoc _ _ _
    dsimp [H]; omega
  have h4Cl_w : 4 * C_cap * (l + 1) < 2 ^ w := by
    have : 4 * C_cap * (l + 1) ≤ H := by dsimp [H]; omega
    omega
  have h166_w : 166 ≤ H := by
    have h1 : 41 ≤ C_cap := by dsimp [C_cap]; omega
    have hm : 41 ≤ C_cap * (l + 1) := Nat.le_trans h1 (Nat.le_mul_of_pos_right C_cap (Nat.succ_pos _))
    have h2 : 4 * C_cap * (l + 1) = 4 * (C_cap * (l + 1)) := mul_assoc _ _ _
    dsimp [H]; omega
  have h40_w : 40 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have h4_w : 4 ≤ 2 ^ w := by omega
  have hC_w : C_cap < 2 ^ w := omega_le_lt hC_le_H hH_w
  have h4C_w : 40 * d < 2 ^ w := omega_le_lt (by dsimp [C_cap]; omega) hC_w
  have hl_w : l < 2 ^ w := lt_trans (Nat.log_lt_self 2 (by omega : 2 * m_s + 1 ≠ 0)) hm2_w
  have hl1_w : l + 1 < 2 ^ w := by
    have h1 : 1 ≤ 4 * C_cap := by dsimp [C_cap]; omega
    have h2 : l + 1 ≤ 4 * C_cap * (l + 1) := Nat.le_mul_of_pos_left (l + 1) h1
    omega
  have h4C4_w : 4 * C_cap < 2 ^ w := by
    have h1 : 4 * C_cap ≤ 4 * C_cap * (l + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    omega
  have h2ms_w : 2 * m_s < 2 ^ w := by omega
  intro st ω hst; subst hst
  refine runs_start_le ?_
  let st1 : State := { st with regs := Function.update st.regs 22 C_cap }
  have he1 : (Expr.bin .add (.bin .mul (.const 40) (.reg 20)) (.const 1)).eval w st = some C_cap :=
    Expr.eval_add (Expr.eval_mul (Expr.eval_const h40_w) (Expr.eval_reg_of_eq hr20) h4C_w)
      (Expr.eval_const (by omega)) hC_w
  refine runs_seq_assign_le he1 ?_
  let st2 : State := { st1 with regs := Function.update st1.regs 24 (2 * m_s + 1) }
  have he2 : (Expr.bin .add (.bin .mul (.const 2) (.reg 21)) (.const 1)).eval w st1 = some (2 * m_s + 1) :=
    Expr.eval_add (Expr.eval_mul (Expr.eval_const h2_w)
      (Expr.eval_reg_of_eq (by dsimp [st1]; rw [Function.update_of_ne (by decide), hr21])) h2ms_w)
      (Expr.eval_const (by omega)) hm2_w
  refine runs_seq_assign_le he2 ?_
  let st3 : State := { st2 with regs := Function.update st2.regs 25 0 }
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  have hr_tr := log2Loop_triple (w := w) (p := p) 24 25 (2 * m_s + 1) (by decide) hm2_w h4_w hl_w st3
    (by dsimp [st3, st2]; rw [Function.update_of_ne (by decide), Function.update_self])
    (by simp [st3])
  refine runs_seq_triple_le hr_tr rfl ?_
  intro st4 ⟨hr4_25, hm4, hp4, hreg4⟩
  have h22_4 : st4.regs 22 = C_cap := by
    rw [hreg4 22 (by decide) (by decide)]
    dsimp [st3, st2, st1]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
  have he_out : (Expr.bin .add (.bin .mul (.bin .mul (.const 4) (.reg 22))
      (.bin .add (.reg 25) (.const 1))) (.const 2)).eval w st4 = some H :=
    Expr.eval_add
      (Expr.eval_mul
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq h22_4) h4C4_w)
        (Expr.eval_add (Expr.eval_reg_of_eq hr4_25) (Expr.eval_const (by omega)) hl1_w)
        h4Cl_w)
      (Expr.eval_const h2_w) hH_w
  refine runs_assign_le he_out ?_ ?_
  · refine ⟨?_, by simp, hm4, hp4, fun r hr => ?_⟩
    · dsimp only; rw [Function.update_of_ne (by decide), h22_4]
    · dsimp only
      rw [Function.update_of_ne (by omega)]
      rw [hreg4 r (by omega) (by omega)]
      dsimp only [st3, st2, st1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
  · simp only [Expr.size]; omega
where
  omega_le_lt {a b c : ℕ} (h1 : a ≤ b) (h2 : b < c) : a < c := lt_of_le_of_lt h1 h2

/-! ## 5. Top-Level Procedures (`initProc`, `deleteProc`, `getPathProc`, `pathDSProcs`) -/

/-- Initialization procedure (`fn = b`): args `[gAddr, phiNum, phiDen, M, h]`. -/
def initProc (Kγ c b : ℕ) : Stmt :=
  seqStmts
    [ .assign 5 (.load (.reg 0))
    , .assign 6 (.load (.bin .add (.reg 0) (.const 1)))
    , .assign 7 (.bin .add (.reg 4) (.const hdrSize))
    , .assign 8 (.bin .add (.bin .add (.reg 7) (.const 2)) (.bin .mul (.const 6) (.reg 6)))
    , .assign 9 (.bin .add (.reg 8) (.reg 5))
    , .assign 10 (.bin .mul (.const 3) (.reg 6))
    , .assign 11 (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 6)))
    , .store (.bin .add (.reg 4) (.const hdrN)) (.reg 5)
    , .store (.bin .add (.reg 4) (.const hdrM)) (.reg 6)
    , .store (.bin .add (.reg 4) (.const hdrPhiNum)) (.reg 1)
    , .store (.bin .add (.reg 4) (.const hdrPhiDen)) (.reg 2)
    , .store (.bin .add (.reg 4) (.const hdrMCap)) (.reg 3)
    , .store (.bin .add (.reg 4) (.const hdrGsAddr)) (.reg 7)
    , .store (.bin .add (.reg 4) (.const hdrInVhat)) (.reg 8)
    , .store (.bin .add (.reg 4) (.const hdrDelCount)) (.const 0)
    , .assign 20 (.reg 0)
    , .assign 21 (.reg 7)
    , writeSubdivGraphStmt
    , .assign 20 (.reg 3)
    , qOfStmt
    , .assign 12 (.reg 21)
    , .store (.bin .add (.reg 4) (.const hdrQVal)) (.reg 12)
    , .assign 20 (.reg 6)
    , csGamma3mStmt Kγ c
    , .assign 13 (.reg 21)
    , .cond (.bin .lt (.bin .mul (.reg 1) (.reg 13)) (.bin .mul (.const 10) (.reg 2)))
        (seqStmts
          [ .assign 14 (.reg 9)
          , .assign 15 (.bin .add (.reg 14)
              (.bin .add (.bin .mul (.const 2) (.reg 11))
                (.bin .add (.const 1) (.bin .mul (.const 4) (.reg 10)))))
          , .assign 16 (.bin .add (.reg 15) (.reg 11))
          , .assign 17 (.bin .add (.reg 16) (.reg 11))
          , .assign 18 (.bin .add (.reg 17) (.reg 10))
          , .store (.bin .add (.reg 4) (.const hdrMode)) (.const 1)
          , .store (.bin .add (.reg 4) (.const hdrCsrAddr)) (.reg 14)
          , .store (.bin .add (.reg 4) (.const hdrInBAddr)) (.reg 15)
          , .store (.bin .add (.reg 4) (.const hdrOutRAddr)) (.reg 16)
          , .store (.bin .add (.reg 4) (.const hdrEMaskAddr)) (.reg 17)
          , .store (.bin .add (.reg 4) (.const hdrAllocEnd)) (.reg 18)
          , .call 25 (b + 3) [.reg 7, .reg 14]
          , .assign 20 (.reg 16)
          , .assign 21 (.reg 11)
          , .assign 22 (.reg 17)
          , .assign 23 (.reg 10)
          , initMasksStmt
          , .ret (.reg 18) ])
        (seqStmts
          [ .assign 14 (.bin .div (.reg 10) (.bin .mul (.const 10) (.reg 13)))
          , .store (.bin .add (.reg 4) (.const hdrMode)) (.const 0)
          , .store (.bin .add (.reg 4) (.const hdrCsHandle)) (.reg 9)
          , .store (.bin .add (.reg 4) (.const hdrCsDelCap)) (.reg 14)
          , .store (.bin .add (.reg 4) (.const hdrOverBudget)) (.const 0)
          , .store (.bin .add (.reg 4) (.const hdrAllocEnd)) (.reg 9)
          , .call 25 (b + 6) [.reg 7, .reg 12, .reg 9]
          , .ret (.reg 25) ]) ]

/-- Deletion procedure (`op 0 = b + 1`): args `[b, e, h]`. In `[CS21]` mode it deletes the middle
edge `3e + 1` of the subdivided graph. The `[CS21]` call may keep new cells of its state above its
heap pointer `h + n + 2`, so the procedure returns the heap pointer of that call and does not clear
those cells. -/
def deleteProc (b : ℕ) : Stmt :=
  seqStmts
    [ .assign 3 (.load (.bin .add (.reg 0) (.const hdrMode)))
    , .assign 4 (.load (.bin .add (.reg 0) (.const hdrN)))
    , .assign 5 (.load (.bin .add (.reg 0) (.const hdrM)))
    , .assign 6 (.load (.bin .add (.reg 0) (.const hdrDelCount)))
    , .store (.bin .add (.reg 0) (.const hdrDelCount)) (.bin .add (.reg 6) (.const 1))
    , .assign 7 (.load (.bin .add (.reg 0) (.const hdrInVhat)))
    , .cond (.bin .eq (.reg 3) (.const 0))
        (seqStmts
          [ .assign 8 (.load (.bin .add (.reg 0) (.const hdrOverBudget)))
          , .assign 9 (.load (.bin .add (.reg 0) (.const hdrCsDelCap)))
          , .cond (.bin .eq (.reg 8) (.const 1))
              (.store (.reg 2) (.const 0) ;; .ret (.bin .add (.reg 2) (.const 1)))
              (.cond (.bin .eq (.reg 6) (.reg 9))
                (seqStmts
                  [ .store (.bin .add (.reg 0) (.const hdrOverBudget)) (.const 1)
                  , .assign 20 (.reg 2)
                  , .assign 21 (.reg 7)
                  , .assign 22 (.reg 4)
                  , emitAllVhatStmt
                  , .assign 12 (.reg 24)
                  , .assign 20 (.reg 12)
                  , .assign 21 (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 4))
                  , zeroRangeStmt
                  , .ret (.reg 12) ])
                (seqStmts
                  [ .assign 10 (.load (.bin .add (.reg 0) (.const hdrCsHandle)))
                  , .assign 11 (.bin .add (.bin .add (.reg 2) (.reg 4)) (.const 2))
                  , .call 12 (b + 7)
                      [.reg 10, .bin .add (.bin .mul (.const 3) (.reg 1)) (.const 1), .reg 11]
                  , .assign 20 (.reg 11)
                  , .assign 21 (.reg 2)
                  , .assign 22 (.reg 7)
                  , .assign 23 (.reg 4)
                  , filterNewVhatStmt
                  , .ret (.reg 12) ])) ])
        (seqStmts
          [ .assign 8 (.load (.bin .add (.reg 0) (.const hdrPhiNum)))
          , .assign 9 (.load (.bin .add (.reg 0) (.const hdrPhiDen)))
          , .assign 10 (.load (.bin .add (.reg 0) (.const hdrGsAddr)))
          , .assign 11 (.load (.bin .add (.reg 0) (.const hdrCsrAddr)))
          , .assign 12 (.load (.bin .add (.reg 0) (.const hdrInBAddr)))
          , .assign 13 (.load (.bin .add (.reg 0) (.const hdrOutRAddr)))
          , .assign 14 (.load (.bin .add (.reg 0) (.const hdrEMaskAddr)))
          , .assign 15 (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 5)))
          , .assign 16 (.bin .mul (.const 3) (.reg 5))
          , .assign 20 (.reg 13)
          , .assign 21 (.reg 12)
          , .assign 22 (.reg 14)
          , .assign 23 (.reg 1)
          , .assign 24 (.reg 4)
          , .assign 25 (.reg 15)
          , fbUpdateBStmt
          , .assign 17 (.bin .div (.bin .sub (.bin .add (.reg 9) (.reg 8)) (.const 1)) (.reg 8))
          , .assign 20 (.reg 17)
          , .assign 21 (.reg 16)
          , fbHStmt
          , .assign 18 (.reg 22)
          , .assign 19 (.reg 23)
          , .assign 17 (.bin .add (.bin .add (.reg 2) (.reg 4)) (.const 2))
          , .call 25 (b + 5) [.reg 10, .reg 11, .reg 12, .reg 13, .reg 17, .reg 18, .reg 19, .const 1]
          , .assign 20 (.reg 2)
          , .assign 21 (.reg 7)
          , .assign 22 (.reg 13)
          , .assign 23 (.reg 4)
          , emitNewVhatFromOutRStmt
          , .assign 18 (.reg 24)
          , .assign 19 (.bin .add (.reg 17)
              (.bin .add (.bin .add (.bin .mul (.const 12) (.reg 15)) (.reg 16))
                (.bin .add (.bin .mul (.const 2) (.reg 19)) (.const 2))))
          , .assign 20 (.reg 18)
          , .assign 21 (.reg 19)
          , zeroRangeStmt
          , .ret (.reg 18) ]) ]

/-- Path query procedure (`op 1 = b + 2`): args `[b, u, v, h]`. In `[CS21]` mode it returns the heap
pointer of the `[CS21]` query, whose new cells may belong to that state. -/
def getPathProc (b : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.reg 2))
    (.store (.reg 3) (.const 0) ;;
     .store (.bin .add (.reg 3) (.const 1)) (.const 0) ;;
     .ret (.bin .add (.reg 3) (.const 2)))
    (seqStmts
      [ .assign 4 (.load (.bin .add (.reg 0) (.const hdrMode)))
      , .assign 5 (.load (.bin .add (.reg 0) (.const hdrN)))
      , .assign 6 (.load (.bin .add (.reg 0) (.const hdrM)))
      , .cond (.bin .eq (.reg 4) (.const 0))
          (seqStmts
            [ .assign 7 (.load (.bin .add (.reg 0) (.const hdrCsHandle)))
            , .assign 8 (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 5))) (.const 4))
            , .call 9 (b + 8) [.reg 7, .reg 1, .reg 2, .reg 8]
            , .assign 20 (.reg 8)
            , .assign 21 (.reg 3)
            , .assign 22 (.reg 5)
            , projSeqToWalkStmt
            , .ret (.reg 9) ])
          (seqStmts
            [ .assign 7 (.load (.bin .add (.reg 0) (.const hdrCsrAddr)))
            , .assign 8 (.load (.bin .add (.reg 0) (.const hdrOutRAddr)))
            , .assign 9 (.load (.bin .add (.reg 0) (.const hdrEMaskAddr)))
            , .assign 10 (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 6)))
            , .assign 11 (.bin .mul (.const 3) (.reg 6))
            , .assign 12 (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 5))) (.const 4))
            , .assign 13 (.bin .add (.reg 12) (.bin .add (.bin .mul (.const 2) (.reg 10)) (.const 2)))
            , .assign 14 (.bin .add (.reg 13) (.bin .mul (.const 4) (.reg 10)))
            , .call 25 (b + 4) [.reg 10, .reg 11, .reg 7, .reg 8, .reg 9, .reg 1, .reg 2, .reg 13, .reg 12]
            , .assign 20 (.reg 12)
            , .assign 21 (.reg 3)
            , .assign 22 (.reg 5)
            , projSeqToWalkStmt
            , .assign 15 (.reg 23)
            , .assign 20 (.reg 12)
            , .assign 21 (.reg 14)
            , zeroRangeStmt
            , .ret (.reg 15) ]) ])

lemma initProc_noRand (Kγ c b : ℕ) : (initProc Kγ c b).NoRand := by
  simp [initProc, seqStmts, writeSubdivGraphStmt_noRand, qOfStmt_noRand,
    csGamma3mStmt_noRand, initMasksStmt_noRand, Stmt.NoRand]

lemma deleteProc_noRand (b : ℕ) : (deleteProc b).NoRand := by
  simp [deleteProc, seqStmts, emitAllVhatStmt_noRand, zeroRangeStmt_noRand,
    filterNewVhatStmt_noRand, fbUpdateBStmt_noRand, fbHStmt_noRand,
    emitNewVhatFromOutRStmt_noRand, Stmt.NoRand]

lemma getPathProc_noRand (b : ℕ) : (getPathProc b).NoRand := by
  simp [getPathProc, seqStmts, projSeqToWalkStmt_noRand, zeroRangeStmt_noRand, Stmt.NoRand]

/-- Full deterministic procedure table for `PathDSImpl`:
- `b + 0`: `initProc Kγ c b`
- `b + 1`: `deleteProc b`
- `b + 2`: `getPathProc b`
- `b + 3`: `buildCsrProc`
- `b + 4`: `bfsPathProc`
- `b + 5`: `pruneWrapProc`
- `b + 6 + ...`: stripped deterministic `[CS21]` procedures. -/
def pathDSProcs (Kγ c : ℕ) (csMk : ℕ → List Stmt) (b : ℕ) : List Stmt :=
  [initProc Kγ c b, deleteProc b, getPathProc b, buildCsrProc, bfsPathProc, pruneWrapProc] ++
    (csMk (b + 6)).map stripRandStmt

lemma pathDSProcs_length (Kγ c : ℕ) (csMk : ℕ → List Stmt) (b : ℕ) :
    3 ≤ (pathDSProcs Kγ c csMk b).length := by
  simp [pathDSProcs]

lemma pathDSProcs_noRand (Kγ c : ℕ) (csMk : ℕ → List Stmt) (b : ℕ) :
    ∀ s ∈ pathDSProcs Kγ c csMk b, s.NoRand := by
  intro s hs
  simp only [pathDSProcs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map] at hs
  rcases hs with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨s₀, _, rfl⟩
  · exact initProc_noRand Kγ c b
  · exact deleteProc_noRand b
  · exact getPathProc_noRand b
  · exact buildCsrProc_noRand
  · exact bfsPathProc_noRand
  · exact by simp [pruneWrapProc, pruneExpanderStmt_noRand, Stmt.NoRand]
  · exact stripRandStmt_noRand s₀

/-! ## 6. `Program.HasAt` Extractors and Deterministic `[CS21]` Call Bridge -/

lemma hasAt_buildCsr {Kγ c b : ℕ} {csMk : ℕ → List Stmt} {p : Program}
    (hp : p.HasAt b (pathDSProcs Kγ c csMk b)) :
    p.HasAt (b + 3) [buildCsrProc] := by
  intro i hi
  have hi0 : i = 0 := by simp at hi; omega
  subst hi0
  simpa [pathDSProcs] using hp 3 (by simp [pathDSProcs])

lemma hasAt_bfsPath {Kγ c b : ℕ} {csMk : ℕ → List Stmt} {p : Program}
    (hp : p.HasAt b (pathDSProcs Kγ c csMk b)) :
    p.HasAt (b + 4) [bfsPathProc] := by
  intro i hi
  have hi0 : i = 0 := by simp at hi; omega
  subst hi0
  simpa [pathDSProcs] using hp 4 (by simp [pathDSProcs])

lemma hasAt_pruneWrap {Kγ c b : ℕ} {csMk : ℕ → List Stmt} {p : Program}
    (hp : p.HasAt b (pathDSProcs Kγ c csMk b)) :
    p.HasAt (b + 5) [pruneWrapProc] := by
  intro i hi
  have hi0 : i = 0 := by simp at hi; omega
  subst hi0
  simpa [pathDSProcs] using hp 5 (by simp [pathDSProcs])

lemma hasAt_cs {Kγ c b : ℕ} {csMk : ℕ → List Stmt} {p : Program}
    (hp : p.HasAt b (pathDSProcs Kγ c csMk b)) :
    p.HasAt (b + 6) ((csMk (b + 6)).map stripRandStmt) := by
  intro i hi
  have hget := hp (6 + i) (by simp only [pathDSProcs, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢; omega)
  rw [show b + (6 + i) = b + 6 + i by omega] at hget
  unfold pathDSProcs at hget
  rw [List.getElem_append_right (by simp)] at hget
  have hi' : 6 + i - [initProc Kγ c b, deleteProc b, getPathProc b, buildCsrProc, bfsPathProc, pruneWrapProc].length = i := by simp
  simp only [hi'] at hget
  exact hget

lemma csCall_stripRand {w b opIdx : ℕ} {orig : List Stmt} {p : Program} {ω : ℕ → Bool}
    (hp : p.HasAt b (orig.map stripRandStmt))
    {body : Stmt} {csArgs : List ℕ} {mem : ℕ → ℕ} {pos : ℕ}
    {o : Outcome} {st1' : State} {c1 : ℕ}
    (hproc_orig : (⟨List.replicate b (.loop (.const 1) .nop) ++ orig⟩ : Program).procs[b + opIdx]? = some body)
    (hrun_orig : Runs w ⟨List.replicate b (.loop (.const 1) .nop) ++ orig⟩ (fun _ => false)
      body (startState csArgs mem pos) o st1' c1)
    {r : ℕ} {argExprs : List Expr} {st : State}
    (hargs : evalArgs w st argExprs = some csArgs)
    (hmem : st.mem = mem) (_hpos : st.pos = pos) :
    ∃ st2' c2,
      Runs w p ω (.call r (b + opIdx) argExprs) st .normal st2' c2 ∧
      st2'.regs = Function.update st.regs r o.value ∧
      st2'.mem = st1'.mem ∧
      c2 ≤ argsSize argExprs + 2 * c1 + 1 := by
  have hop_lt : opIdx < orig.length := by
    by_contra hge
    have hnone : (List.replicate b (Stmt.loop (.const 1) .nop) ++ orig)[b + opIdx]? = none := by
      rw [List.getElem?_append_right (by simp), List.length_replicate, Nat.add_sub_cancel_left]
      exact List.getElem?_eq_none (by omega)
    rw [show (⟨List.replicate b (.loop (.const 1) .nop) ++ orig⟩ : Program).procs =
      List.replicate b (Stmt.loop (.const 1) .nop) ++ orig from rfl] at hproc_orig
    rw [hnone] at hproc_orig
    cases hproc_orig
  have hbody_eq : orig[opIdx] = body := by
    have hget : (List.replicate b (Stmt.loop (.const 1) .nop) ++ orig)[b + opIdx]? = some orig[opIdx] := by
      rw [List.getElem?_append_right (by simp), List.length_replicate, Nat.add_sub_cancel_left,
        List.getElem?_eq_getElem hop_lt]
    rw [show (⟨List.replicate b (.loop (.const 1) .nop) ++ orig⟩ : Program).procs =
      List.replicate b (Stmt.loop (.const 1) .nop) ++ orig from rfl] at hproc_orig
    exact Option.some.inj (hget.symm.trans hproc_orig)
  have hp_call : p.procs[b + opIdx]? = some (stripRandStmt body) := by
    have h := hp opIdx (by simp [hop_lt])
    simpa [hbody_eq] using h
  obtain ⟨fuel, hfuel⟩ := hrun_orig
  have hstart_eq : (startState csArgs mem pos).regs = (startState csArgs st.mem st.pos).regs := rfl
  obtain ⟨st2_b, c2_b, hexec, _, hmem2, hc2⟩ := exec_stripRand_block (ω := ω) hp fuel body
    (startState csArgs mem pos) (startState csArgs st.mem st.pos) o st1' c1 hstart_eq hmem.symm hfuel
  exact ⟨{ st2_b with regs := Function.update st.regs r o.value }, argsSize argExprs + c2_b + 1,
    runs_call_iff.mpr ⟨csArgs, stripRandStmt body, o, st2_b, c2_b, hargs, hp_call, ⟨fuel, hexec⟩,
      rfl, rfl, rfl⟩, rfl, hmem2, by omega⟩

/-! ## 7. Cost-Accumulating Continuation Helpers -/

lemma runs_start_phi {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt}
    {st : State} {Q : Outcome → State → ℕ → Prop}
    (h : ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' (0 + c)) :
    ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' c := by
  simpa using h

lemma runs_seq_assign_phi {w r : ℕ} {e : Expr} {s2 : Stmt} {p : Program} {ω : ℕ → Bool}
    {st : State} {v k : ℕ} {Q : Outcome → State → ℕ → Prop}
    (he : e.eval w st = some v)
    (h : ∃ o st' c₂, Runs w p ω s2 { st with regs := Function.update st.regs r v } o st' c₂ ∧
      Q o st' ((k + (e.size + 2)) + c₂)) :
    ∃ o st' c, Runs w p ω (.assign r e ;; s2) st o st' c ∧ Q o st' (k + c) := by
  rcases h with ⟨o, st', c₂, hr2, hq⟩
  have hr1 : Runs w p ω (.assign r e) st .normal { st with regs := Function.update st.regs r v } (e.size + 1) :=
    runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩
  refine ⟨o, st', (e.size + 1) + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr1, hr2, rfl⟩), ?_⟩
  simpa [show k + ((e.size + 1) + c₂ + 1) = (k + (e.size + 2)) + c₂ by omega] using hq

lemma runs_seq_store_phi {w : ℕ} {aExpr vExpr : Expr} {s2 : Stmt} {p : Program} {ω : ℕ → Bool}
    {st : State} {a v k : ℕ} {Q : Outcome → State → ℕ → Prop}
    (ha : aExpr.eval w st = some a) (hv : vExpr.eval w st = some v)
    (h : ∃ o st' c₂, Runs w p ω s2 { st with mem := Function.update st.mem a v } o st' c₂ ∧
      Q o st' ((k + (aExpr.size + vExpr.size + 2)) + c₂)) :
    ∃ o st' c, Runs w p ω (.store aExpr vExpr ;; s2) st o st' c ∧ Q o st' (k + c) := by
  rcases h with ⟨o, st', c₂, hr2, hq⟩
  have hr1 : Runs w p ω (.store aExpr vExpr) st .normal { st with mem := Function.update st.mem a v }
      (aExpr.size + vExpr.size + 1) := runs_store_iff.mpr ⟨a, v, ha, hv, rfl, rfl, rfl⟩
  refine ⟨o, st', (aExpr.size + vExpr.size + 1) + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr1, hr2, rfl⟩), ?_⟩
  simpa [show k + ((aExpr.size + vExpr.size + 1) + c₂ + 1) = (k + (aExpr.size + vExpr.size + 2)) + c₂ by omega] using hq

lemma runs_seq_triple_phi {w : ℕ} {p : Program} {ω : ℕ → Bool} {P : State → Prop}
    {s1 s2 : Stmt} {Q1 : State → Prop} {T1 : State → ℕ}
    {st : State} {k : ℕ} {Q : Outcome → State → ℕ → Prop}
    (hm : ∀ o st' a b, a ≤ b → Q o st' b → Q o st' a)
    (htr : Triple w p P s1 (normalPost Q1) T1) (hP : P st)
    (h : ∀ st₁, Q1 st₁ →
      ∃ o st' c₂, Runs w p ω s2 st₁ o st' c₂ ∧ Q o st' ((k + (T1 st + 1)) + c₂)) :
    ∃ o st' c, Runs w p ω (s1 ;; s2) st o st' c ∧ Q o st' (k + c) := by
  obtain ⟨o₁, st₁, c₁, hr1, hq1, hc1⟩ := htr st ω hP
  cases o₁ with
  | returned _ => exact False.elim hq1
  | normal =>
    obtain ⟨o, st', c₂, hr2, hq⟩ := h st₁ hq1
    refine ⟨o, st', c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr1, hr2, rfl⟩), ?_⟩
    exact hm o st' (k + (c₁ + c₂ + 1)) ((k + (T1 st + 1)) + c₂) (by omega) hq

lemma runs_cond_phi {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st : State} {v k : ℕ} {Q : Outcome → State → ℕ → Prop}
    (he : e.eval w st = some v)
    (hT : v ≠ 0 → ∃ o st' c, Runs w p ω s₁ st o st' c ∧ Q o st' ((k + e.size + 1) + c))
    (hF : v = 0 → ∃ o st' c, Runs w p ω s₂ st o st' c ∧ Q o st' ((k + e.size + 1) + c)) :
    ∃ o st' c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ Q o st' (k + c) := by
  by_cases hv : v = 0
  · obtain ⟨o, st', c, hr, hq⟩ := hF hv
    refine ⟨o, st', e.size + c + 1, runs_cond_iff.mpr ⟨v, c, he, by simpa [hv] using hr, rfl⟩, ?_⟩
    simpa [show k + (e.size + c + 1) = k + e.size + 1 + c by omega] using hq
  · obtain ⟨o, st', c, hr, hq⟩ := hT hv
    refine ⟨o, st', e.size + c + 1, runs_cond_iff.mpr ⟨v, c, he, by simpa [hv] using hr, rfl⟩, ?_⟩
    simpa [show k + (e.size + c + 1) = k + e.size + 1 + c by omega] using hq

end MinCostFlow.Expander.PathDSProg
