module

public import WordRAM.Logic
public import MinCostFlow.Expander.PathDSProg.BoundsLoopProg

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Parameter Evaluator Blocks: `phiOut` and `csExp`

This file holds the first part of the material of `BoundsProg.lean`, split off to keep files
small. `BoundsProg.lean` gives the overview.
-/

@[expose] public section

namespace MinCostFlow.Expander.PathDSProg

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Parameter Evaluation Blocks -/

/-- Block 1: computes `reg 7 := phiOutDenImpl Kγ c d M`, preserving `reg 0, 1, 2` and `mem`. -/
def phiOutBlock (Kγ c : ℕ) : Stmt :=
  if c = 0 then
    .cond (.bin .lt (.reg 0) (.const 2)) (.assign 7 (.const 2)) (.assign 7 (.reg 0))
  else
    .assign 15 (.bin .mul (.const 3) (.reg 1)) ;;
    csGammaExpBlock Kγ 15 16 3 4 5 6 ;;
    .assign 7 (.bin .mul (.const c) (.bin .shiftLeft (.const 1) (.reg 16))) ;;
    .cond (.bin .lt (.reg 7) (.reg 0)) (.assign 7 (.reg 0)) .nop ;;
    .cond (.bin .lt (.reg 7) (.const 2)) (.assign 7 (.const 2)) .nop

lemma phiOutBlock_noRand (Kγ c : ℕ) : (phiOutBlock Kγ c).NoRand := by
  unfold phiOutBlock
  split_ifs <;> simp [csGammaExpBlock_noRand, Stmt.NoRand]

theorem phiOutBlock_triple {w Kγ c K_int cw_cs d M : ℕ} {p : Program}
    (hd : 1 ≤ d)
    (hcw : max 24 (4 * cw_cs + 8) *
      (Nat.log 2 (d + M + gExpImpl Kγ c K_int d M + gDelImpl K_int d M + 2) + 1) ≤ w)
    (st₀ : State) (hr0 : st₀.regs 0 = d) (hr1 : st₀.regs 1 = M) :
    Triple w p (fun st => st = st₀) (phiOutBlock Kγ c)
      (normalPost fun st' =>
        st'.regs 0 = d ∧ st'.regs 1 = M ∧ st'.regs 2 = st₀.regs 2 ∧
        st'.regs 7 = phiOutDenImpl Kγ c d M ∧ st'.mem = st₀.mem ∧ st'.pos = st₀.pos)
      (fun _ => 35 * (Nat.log 2 (d + M + 2) + 1) + 180) := by
  have hwd := bounds_word_le (Kγ := Kγ) (c := c) (K_int := K_int) (cw_cs := cw_cs) (d := d) (M := M) (w := w) hd hcw
  rcases hwd with ⟨hX600, hX24, hKγ_c, _, hc_lt, _, _, _, hlog3, _, _, _⟩
  set X := d + M + gExpImpl Kγ c K_int d M + gDelImpl K_int d M + 2
  have hX8_lt : X ^ 8 < 2 ^ w := lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) (by decide)) hX24
  have hX_lt : X < 2 ^ w := lt_of_le_of_lt (Nat.le_self_pow (by decide) _) hX8_lt
  have h2w : 2 < 2 ^ w := by omega
  have h4w : 4 ≤ 2 ^ w := by omega
  have hd_lt : d < 2 ^ w := lt_trans (by dsimp [X]; omega : d < X) hX_lt
  have hM_lt : M < 2 ^ w := lt_trans (by dsimp [X]; omega : M < X) hX_lt
  intro st ω hst; subst hst
  unfold phiOutBlock
  by_cases hc0 : c = 0
  · subst hc0
    rw [ite_eq_left_iff.mpr fun h => absurd rfl h]
    have hphi_eq : phiOutDenImpl Kγ 0 d M = max 2 d := by
      unfold phiOutDenImpl; omega
    have hcond : (Expr.bin .lt (.reg 0) (.const 2)).eval w st = some (if d < 2 then 1 else 0) :=
      Expr.eval_lt_op (Expr.eval_reg_of_eq hr0) (Expr.eval_const h2w) (by omega)
    by_cases hlt : d < 2
    · let st' : State := { st with regs := Function.update st.regs 7 2 }
      have hr : Runs w p ω (.assign 7 (.const 2)) st .normal st' 2 :=
        runs_assign_iff.mpr ⟨2, Expr.eval_const h2w, rfl, rfl, by simp⟩
      refine ⟨.normal, st', 6, runs_cond_iff.mpr ⟨1, 2, by simpa [hlt] using hcond, by simpa using hr, by simp⟩,
        ⟨?_, ?_, ?_, ?_, rfl, rfl⟩, by dsimp only; omega⟩
      · dsimp [st']; rw [Function.update_of_ne (by decide), hr0]
      · dsimp [st']; rw [Function.update_of_ne (by decide), hr1]
      · dsimp [st']; rw [Function.update_of_ne (by decide)]
      · rw [hphi_eq]; dsimp [st']; rw [Function.update_self]; omega
    · let st' : State := { st with regs := Function.update st.regs 7 d }
      have hr : Runs w p ω (.assign 7 (.reg 0)) st .normal st' 2 :=
        runs_assign_iff.mpr ⟨d, Expr.eval_reg_of_eq hr0, rfl, rfl, by simp⟩
      refine ⟨.normal, st', 6, runs_cond_iff.mpr ⟨0, 2, by simpa [hlt] using hcond, by simpa using hr, by simp⟩,
        ⟨?_, ?_, ?_, ?_, rfl, rfl⟩, by dsimp only; omega⟩
      · dsimp [st']; rw [Function.update_of_ne (by decide), hr0]
      · dsimp [st']; rw [Function.update_of_ne (by decide), hr1]
      · dsimp [st']; rw [Function.update_of_ne (by decide)]
      · rw [hphi_eq]; dsimp [st']; rw [Function.update_self]; omega
  · rw [ite_eq_right_iff.mpr fun h => absurd h hc0]
    have hc1 : 1 ≤ c := Nat.pos_of_ne_zero hc0
    have hKγ_lt : Kγ < 2 ^ w := lt_trans (lt_trans (hKγ_c hc1) (by
      have := phiOutDenImpl_le_gExpImpl Kγ c K_int d M
      dsimp [X]; omega)) hX_lt
    have hc_2w : c < 2 ^ w := lt_trans hc_lt hX_lt
    have h3M_lt : 3 * M < 2 ^ w := by
      have hX2 : 600 * X ≤ X * X := Nat.mul_le_mul_right X hX600
      have hX2_8 : X * X ≤ X ^ 8 := by
        have : X * X = X ^ 2 := by ring
        rw [this]; exact Nat.pow_le_pow_right (by omega) (by decide)
      have h3M : 3 * M ≤ 3 * X := by dsimp [X]; omega
      omega
    have hcube_lt : (Nat.log 2 (3 * M) + 2) ^ 4 < 2 ^ w := lt_trans hlog3 hX8_lt
    have hgam : Cited.csGamma Kγ (3 * M) ≤ c * Cited.csGamma Kγ (3 * M) :=
      Nat.le_mul_of_pos_left _ hc1
    have hc_gam_le : c * Cited.csGamma Kγ (3 * M) ≤ phiOutDenImpl Kγ c d M := by
      unfold phiOutDenImpl; exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hphi_lt : phiOutDenImpl Kγ c d M < 2 ^ w := lt_trans (by
      have := phiOutDenImpl_le_gExpImpl Kγ c K_int d M
      dsimp [X]; omega) hX_lt
    have hcs_lt : csGammaExp Kγ (3 * M) < 2 ^ w := by
      have h1 : csGammaExp Kγ (3 * M) < Cited.csGamma Kγ (3 * M) :=
        Nat.lt_pow_self (by decide : 1 < 2)
      omega
    have hcm_lt : c * Cited.csGamma Kγ (3 * M) < 2 ^ w := lt_of_le_of_lt hc_gam_le hphi_lt
    have hgam_lt : Cited.csGamma Kγ (3 * M) < 2 ^ w := lt_of_le_of_lt hgam hcm_lt
    refine runs_start_le ?_
    let st1 : State := { st with regs := Function.update st.regs 15 (3 * M) }
    refine runs_seq_assign_le (v := 3 * M)
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr1) h3M_lt) ?_
    have hcs_tr := csGammaExpBlock_triple (w := w) (p := p) Kγ 15 16 3 4 5 6 (3 * M)
      (by decide) (by decide) hKγ_lt h3M_lt hcube_lt hcs_lt h4w st1 (by dsimp [st1]; rw [Function.update_self])
    refine runs_seq_triple_le hcs_tr rfl ?_
    intro st2 ⟨hr16, hm2, hp2, hf2⟩
    let cand := c * Cited.csGamma Kγ (3 * M)
    have hsh_eq : 1 <<< csGammaExp Kγ (3 * M) = Cited.csGamma Kγ (3 * M) := by
      rw [Nat.shiftLeft_eq, one_mul, csGamma_eq_two_pow]
    have he_phi : (Expr.bin .mul (.const c) (.bin .shiftLeft (.const 1) (.reg 16))).eval w st2 =
        some cand := by
      have hs := Expr.eval_shiftLeft (Expr.eval_const (by omega : 1 < 2 ^ w)) (Expr.eval_reg_of_eq hr16)
        (by rw [hsh_eq]; exact hgam_lt)
      have hm := Expr.eval_mul (Expr.eval_const hc_2w) hs (by rw [hsh_eq]; exact hcm_lt)
      simpa [cand, hsh_eq] using hm
    let st3 : State := { st2 with regs := Function.update st2.regs 7 cand }
    refine runs_seq_assign_le (v := cand) he_phi ?_
    have hst3_0 : st3.regs 0 = d := by
      dsimp [st3]; rw [Function.update_of_ne (by decide), hf2 0 (by decide) (by decide) (by decide) (by decide) (by decide)]
      dsimp [st1]; rw [Function.update_of_ne (by decide), hr0]
    have hst3_1 : st3.regs 1 = M := by
      dsimp [st3]; rw [Function.update_of_ne (by decide), hf2 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
      dsimp [st1]; rw [Function.update_of_ne (by decide), hr1]
    have hst3_2 : st3.regs 2 = st.regs 2 := by
      dsimp [st3]; rw [Function.update_of_ne (by decide), hf2 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
      dsimp [st1]; rw [Function.update_of_ne (by decide)]
    have hst3_7 : st3.regs 7 = cand := by dsimp [st3]; rw [Function.update_self]
    have hcond1_tr : Triple w p (fun s => s = st3)
        (.cond (.bin .lt (.reg 7) (.reg 0)) (.assign 7 (.reg 0)) .nop)
        (normalPost fun s' => s'.regs 0 = d ∧ s'.regs 1 = M ∧ s'.regs 2 = st.regs 2 ∧
          s'.regs 7 = max d cand ∧ s'.mem = st.mem ∧ s'.pos = st.pos)
        (fun _ => 7) := by
      intro s ω' hs; subst hs
      have hcnd : (Expr.bin .lt (.reg 7) (.reg 0)).eval w st3 =
          some (if cand < d then 1 else 0) :=
        Expr.eval_lt_op (Expr.eval_reg_of_eq hst3_7) (Expr.eval_reg_of_eq hst3_0) (by omega)
      by_cases hlt1 : cand < d
      · let st4' : State := { st3 with regs := Function.update st3.regs 7 d }
        have ha : Runs w p ω' (.assign 7 (.reg 0)) st3 .normal st4' 2 :=
          runs_assign_iff.mpr ⟨d, Expr.eval_reg_of_eq hst3_0, rfl, rfl, by simp⟩
        refine ⟨.normal, st4', 6, runs_cond_iff.mpr ⟨1, 2, by simpa [hlt1] using hcnd, by simpa using ha, by simp⟩,
          ⟨?_, ?_, ?_, ?_, by rw [hm2], by rw [hp2]⟩, by dsimp only; omega⟩
        · dsimp [st4']; rw [Function.update_of_ne (by decide), hst3_0]
        · dsimp [st4']; rw [Function.update_of_ne (by decide), hst3_1]
        · dsimp [st4']; rw [Function.update_of_ne (by decide), hst3_2]
        · dsimp [st4']; rw [Function.update_self]; omega
      · refine ⟨.normal, st3, 5, runs_cond_iff.mpr ⟨0, 1, by simpa [hlt1] using hcnd, by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp⟩,
          ⟨hst3_0, hst3_1, hst3_2, by rw [hst3_7]; omega, hm2, hp2⟩, by dsimp only; omega⟩
    refine runs_seq_triple_le hcond1_tr rfl ?_
    intro st4 ⟨hr4_0, hr4_1, hr4_2, hr4_7, hm4, hp4⟩
    have hcnd2 : (Expr.bin .lt (.reg 7) (.const 2)).eval w st4 =
        some (if max d cand < 2 then 1 else 0) :=
      Expr.eval_lt_op (Expr.eval_reg_of_eq hr4_7) (Expr.eval_const h2w) (by omega)
    have hlog_bd := log2_three_mul_le d M hd
    have h35 : 35 * Nat.log 2 (3 * M) ≤ 35 * (Nat.log 2 (d + M + 2) + 2) := Nat.mul_le_mul_left 35 hlog_bd
    by_cases hlt2 : max d cand < 2
    · let st5 : State := { st4 with regs := Function.update st4.regs 7 2 }
      have ha2 : Runs w p ω (.assign 7 (.const 2)) st4 .normal st5 2 :=
        runs_assign_iff.mpr ⟨2, Expr.eval_const h2w, rfl, rfl, by simp⟩
      refine ⟨.normal, st5, 6,
        runs_cond_iff.mpr ⟨1, 2, by simpa [hlt2] using hcnd2, by simpa using ha2, by simp⟩,
        ⟨?_, ?_, ?_, ?_, by rw [hm4], by rw [hp4]⟩, by simp only [Expr.size]; omega⟩
      · dsimp [st5]; rw [Function.update_of_ne (by decide), hr4_0]
      · dsimp [st5]; rw [Function.update_of_ne (by decide), hr4_1]
      · dsimp [st5]; rw [Function.update_of_ne (by decide), hr4_2]
      · dsimp [st5]; rw [Function.update_self]; simp only [phiOutDenImpl]; omega
    · refine ⟨.normal, st4, 5, runs_cond_iff.mpr ⟨0, 1, by simpa [hlt2] using hcnd2,
        by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp⟩,
        ⟨hr4_0, hr4_1, hr4_2, by rw [hr4_7]; unfold phiOutDenImpl; dsimp [cand]; omega, hm4, hp4⟩,
        by simp only [Expr.size]; omega⟩

/-- Block 2: computes `reg 9 := csExpFactor Kγ K_int M`, preserving `reg 0, 1, 2, 7` and `mem`. -/
def csExpBlock (Kγ K_int : ℕ) : Stmt :=
  .assign 3 (.bin .add (.reg 1) (.const 2)) ;;
  .assign 4 (.const 0) ;;
  .loop (.bin .lt (.const 1) (.reg 3))
    (.assign 3 (.bin .div (.reg 3) (.const 2)) ;;
     .assign 4 (.bin .add (.reg 4) (.const 1))) ;;
  .assign 5 (.reg 4) ;;
  .assign 8 (.const 0) ;;
  .assign 3 (.const 1) ;;
  kthRootLoop 8 3 5 (pow8Expr 3) ;;
  .assign 15 (.bin .add (.reg 8) (.const 1)) ;;
  .assign 15 (.bin .mul (.reg 15) (.reg 15)) ;;
  .assign 16 (.bin .mul (.reg 15) (.reg 15)) ;;
  .assign 15 (.bin .mul (.bin .mul (.reg 16) (.reg 15)) (.bin .add (.reg 8) (.const 1))) ;;
  .assign 15 (.bin .add (.reg 15) (.const 2)) ;;
  (if K_int = 0 then
    .assign 9 (.bin .add (.bin .shiftLeft (.const 1) (.reg 15)) (.const 1))
  else
    .assign 16 (.bin .mul (.const 4) (.reg 1)) ;;
    csGammaExpBlock Kγ 16 14 3 4 5 6 ;;
    .assign 9 (.bin .add
      (.bin .mul (.bin .mul (.reg 14) (.const K_int)) (.bin .add (.reg 8) (.const 2))) (.reg 15)) ;;
    .assign 9 (.bin .add (.bin .shiftLeft (.const 1) (.reg 9)) (.const 1)))

lemma csExpBlock_noRand (Kγ K_int : ℕ) : (csExpBlock Kγ K_int).NoRand := by
  unfold csExpBlock
  split_ifs <;> simp [kthRootLoop_noRand, csGammaExpBlock_noRand, Stmt.NoRand]

private lemma csExpZero_tail {w Kγ M d phiVal k : ℕ} {p : Program} (ω : ℕ → Bool)
    (st₀ st12 : State)
    (h1w : 1 < 2 ^ w) (hcs_lt : csExpFactor Kγ 0 M < 2 ^ w)
    (hr15 : st12.regs 15 = qExpPow M)
    (hinv : st12.regs 0 = d ∧ st12.regs 1 = M ∧ st12.regs 2 = st₀.regs 2 ∧ st12.regs 7 = phiVal)
    (hm : st12.mem = st₀.mem) (hp : st12.pos = st₀.pos)
    (hc : k + (Expr.bin .add (.bin .shiftLeft (.const 1) (.reg 15)) (.const 1)).size + 1 ≤
      80 * (Nat.log 2 (d + M + 2) + 1) + 230) :
    ∃ o st' c, Runs w p ω (.assign 9 (.bin .add (.bin .shiftLeft (.const 1) (.reg 15)) (.const 1))) st12 o st' c ∧
      normalPost (fun st' =>
        st'.regs 0 = d ∧ st'.regs 1 = M ∧ st'.regs 2 = st₀.regs 2 ∧ st'.regs 7 = phiVal ∧
        st'.regs 9 = csExpFactor Kγ 0 M ∧ st'.mem = st₀.mem ∧ st'.pos = st₀.pos) o st' ∧
      k + c ≤ 80 * (Nat.log 2 (d + M + 2) + 1) + 230 := by
  have hcs0 : csExpFactor Kγ 0 M = 2 ^ qExpPow M + 1 := by unfold csExpFactor; simp
  have hsh : 1 <<< qExpPow M = 2 ^ qExpPow M := by rw [Nat.shiftLeft_eq, one_mul]
  have hsh2w : 1 <<< qExpPow M < 2 ^ w := by rw [hsh]; omega
  have he_out : (Expr.bin .add (.bin .shiftLeft (.const 1) (.reg 15)) (.const 1)).eval w st12 =
      some (csExpFactor Kγ 0 M) := by
    have hs := Expr.eval_shiftLeft (Expr.eval_const h1w) (Expr.eval_reg_of_eq hr15) hsh2w
    have ha := Expr.eval_add hs (Expr.eval_const h1w) (by rw [hsh, ← hcs0]; exact hcs_lt)
    simpa [hsh, hcs0] using ha
  refine runs_assign_le (v := csExpFactor Kγ 0 M) he_out ?_ hc
  refine ⟨by simp [hinv.1], by simp [hinv.2.1], by simp [hinv.2.2.1], by simp [hinv.2.2.2], by simp, hm, hp⟩

private lemma csExpPos_tail {w Kγ K_int M d phiVal e_cs k : ℕ} {p : Program} (ω : ℕ → Bool)
    (st₀ st14 : State)
    (h1w : 1 < 2 ^ w) (hcs_lt : csExpFactor Kγ K_int M < 2 ^ w)
    (hcs_def : csExpFactor Kγ K_int M = 2 ^ e_cs + 1)
    (_he_cs_lt : e_cs < 2 ^ w)
    (hst14_0 : st14.regs 0 = d) (hst14_1 : st14.regs 1 = M)
    (hst14_2 : st14.regs 2 = st₀.regs 2) (hst14_7 : st14.regs 7 = phiVal)
    (hm14 : st14.mem = st₀.mem) (hp14 : st14.pos = st₀.pos)
    (he15 : (Expr.bin .add (.bin .mul (.bin .mul (.reg 14) (.const K_int))
        (.bin .add (.reg 8) (.const 2))) (.reg 15)).eval w st14 = some e_cs)
    (hc : k + (Expr.bin .add (.bin .mul (.bin .mul (.reg 14) (.const K_int))
          (.bin .add (.reg 8) (.const 2))) (.reg 15)).size + 2 +
        (Expr.bin .add (.bin .shiftLeft (.const 1) (.reg 9)) (.const 1)).size + 1 ≤
      80 * (Nat.log 2 (d + M + 2) + 1) + 230) :
    ∃ o st' c, Runs w p ω
      (.assign 9 (.bin .add (.bin .mul (.bin .mul (.reg 14) (.const K_int))
          (.bin .add (.reg 8) (.const 2))) (.reg 15)) ;;
       .assign 9 (.bin .add (.bin .shiftLeft (.const 1) (.reg 9)) (.const 1))) st14 o st' c ∧
      normalPost (fun st' =>
        st'.regs 0 = d ∧ st'.regs 1 = M ∧ st'.regs 2 = st₀.regs 2 ∧ st'.regs 7 = phiVal ∧
        st'.regs 9 = csExpFactor Kγ K_int M ∧ st'.mem = st₀.mem ∧ st'.pos = st₀.pos) o st' ∧
      k + c ≤ 80 * (Nat.log 2 (d + M + 2) + 1) + 230 := by
  let st15 : State := { st14 with regs := Function.update st14.regs 9 e_cs }
  have hr15_9 : st15.regs 9 = e_cs := by simp [st15]
  refine runs_seq_assign_le (v := e_cs) he15 ?_
  have hsh : 1 <<< e_cs = 2 ^ e_cs := by rw [Nat.shiftLeft_eq, one_mul]
  have hsh2w : 1 <<< e_cs < 2 ^ w := by rw [hsh]; rw [hcs_def] at hcs_lt; omega
  have he16 : (Expr.bin .add (.bin .shiftLeft (.const 1) (.reg 9)) (.const 1)).eval w st15 =
      some (csExpFactor Kγ K_int M) := by
    have hs := Expr.eval_shiftLeft (Expr.eval_const h1w) (Expr.eval_reg_of_eq hr15_9) hsh2w
    have ha := Expr.eval_add hs (Expr.eval_const h1w) (by rw [hsh, ← hcs_def]; exact hcs_lt)
    simpa [hsh, ← hcs_def] using ha
  refine runs_assign_le (v := csExpFactor Kγ K_int M) he16 ?_ hc
  refine ⟨by simp [hst14_0], by simp [hst14_1], by simp [hst14_2],
    by simp [hst14_7], by simp, hm14, hp14⟩

theorem csExpBlock_triple {w Kγ c K_int cw_cs d M phiVal : ℕ} {p : Program}
    (hd : 1 ≤ d)
    (hcw : max 24 (4 * cw_cs + 8) *
      (Nat.log 2 (d + M + gExpImpl Kγ c K_int d M + gDelImpl K_int d M + 2) + 1) ≤ w)
    (st₀ : State) (hr0 : st₀.regs 0 = d) (hr1 : st₀.regs 1 = M)
    (hr7 : st₀.regs 7 = phiVal) :
    Triple w p (fun st => st = st₀) (csExpBlock Kγ K_int)
      (normalPost fun st' =>
        st'.regs 0 = d ∧ st'.regs 1 = M ∧ st'.regs 2 = st₀.regs 2 ∧ st'.regs 7 = phiVal ∧
        st'.regs 9 = csExpFactor Kγ K_int M ∧ st'.mem = st₀.mem ∧ st'.pos = st₀.pos)
      (fun _ => 80 * (Nat.log 2 (d + M + 2) + 1) + 230) := by
  have hwd := bounds_word_le (Kγ := Kγ) (c := c) (K_int := K_int) (cw_cs := cw_cs) (d := d) (M := M) (w := w) hd hcw
  rcases hwd with ⟨hX600, hX24, _, hKγ_Kint, _, hKint_lt, _, _, _, hlog4, hlog8, _⟩
  set X := d + M + gExpImpl Kγ c K_int d M + gDelImpl K_int d M + 2
  have hX8_lt : X ^ 8 < 2 ^ w := lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) (by decide)) hX24
  have hX_lt : X < 2 ^ w := lt_of_le_of_lt (Nat.le_self_pow (by decide) _) hX8_lt
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h4w : 4 ≤ 2 ^ w := by omega
  have hM2_lt : M + 2 < 2 ^ w := lt_of_le_of_lt (by dsimp [X]; omega : M + 2 ≤ X) hX_lt
  have hlM2_lt : Nat.log 2 (M + 2) < 2 ^ w := lt_of_le_of_lt (le_of_lt (nat_log_lt_self_pos (by omega))) hM2_lt
  have hlt_q8 : (qRoot M + 1) ^ 8 < 2 ^ w := lt_trans hlog8 hX8_lt
  have hlogM2_1_lt : Nat.log 2 (M + 2) + 1 < 2 ^ w :=
    lt_of_le_of_lt (nat_log_lt_self_pos (by omega)) hM2_lt
  have hcs_lt : csExpFactor Kγ K_int M < 2 ^ w := lt_trans (by
    have := csExpFactor_le_gExpImpl Kγ c K_int d M
    dsimp [X]; omega) hX_lt
  have hqp_lt : qExpPow M < 2 ^ w := by
    have h1 : qExpPow M < 2 ^ qExpPow M := Nat.lt_pow_self (by decide : 1 < 2)
    have h2 : 2 ^ qExpPow M < csExpFactor Kγ K_int M := by
      unfold csExpFactor
      exact Nat.lt_succ_of_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
    omega
  have hq1_le_qp : (qRoot M + 1) ^ 7 ≤ qExpPow M := by unfold qExpPow; omega
  have hqpow_lt : ∀ (k : ℕ), k ≤ 7 → (qRoot M + 1) ^ k < 2 ^ w := fun k hk => by
    have : (qRoot M + 1) ^ k ≤ (qRoot M + 1) ^ 7 := Nat.pow_le_pow_right (by omega) hk
    omega
  have hqp_eq : (qRoot M + 1) ^ 7 + 2 = qExpPow M := by simp only [qExpPow]
  have hq2_lt : qRoot M + 2 < 2 ^ w := by
    have h1 := Nat.le_self_pow (by decide : 7 ≠ 0) (qRoot M + 1)
    omega
  intro st ω hst; subst hst
  refine runs_start_le ?_
  let st1 : State := { st with regs := Function.update st.regs 3 (M + 2) }
  refine runs_seq_assign_le (v := M + 2)
    (Expr.eval_add (Expr.eval_reg_of_eq hr1) (Expr.eval_const h2w) hM2_lt) ?_
  let st2 : State := { st1 with regs := Function.update st1.regs 4 0 }
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  have hr3_tr := log2Loop_triple (w := w) (p := p) 3 4 (M + 2) (by decide) hM2_lt h4w hlM2_lt st2
    (by dsimp [st2, st1]; rw [Function.update_of_ne (by decide), Function.update_self])
    (by simp [st2])
  refine runs_seq_triple_le hr3_tr rfl ?_
  intro st3 ⟨hr3_4, hm3, hp3, hreg3⟩
  let st4 : State := { st3 with regs := Function.update st3.regs 5 (Nat.log 2 (M + 2)) }
  refine runs_seq_assign_le (v := Nat.log 2 (M + 2)) (Expr.eval_reg_of_eq hr3_4) ?_
  let st5 : State := { st4 with regs := Function.update st4.regs 8 0 }
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  let st6 : State := { st5 with regs := Function.update st5.regs 3 1 }
  refine runs_seq_assign_le (v := 1) (Expr.eval_const h1w) ?_
  have h8ans : (qRoot M) ^ 8 ≤ Nat.log 2 (M + 2) ∧ Nat.log 2 (M + 2) < (qRoot M + 1) ^ 8 :=
    eighthRoot_iff.mp rfl
  have hq_tr := kthRootLoop_triple (w := w) (p := p) 8 3 5 8 (Nat.log 2 (M + 2)) (qRoot M)
    (pow8Expr 3) (by decide) (by decide) h8ans
    (fun s hs => pow8Expr_eval rfl (lt_of_le_of_lt (Nat.pow_le_pow_left hs 8) hlt_q8))
    hlogM2_1_lt hlt_q8 st6
    (by dsimp [st6, st5]; rw [Function.update_of_ne (by decide), Function.update_self])
    (by simp [st6])
    (by dsimp [st6, st5, st4]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self])
  refine runs_seq_triple_le hq_tr rfl ?_
  intro st7 ⟨hr7_8, hm7, hp7, hf7⟩
  set a := qRoot M + 1
  let st8 : State := { st7 with regs := Function.update st7.regs 15 a }
  refine runs_seq_assign_le (v := a)
    (Expr.eval_add (Expr.eval_reg_of_eq hr7_8) (Expr.eval_const h1w)
      (by simpa [a] using hqpow_lt 1 (by decide))) ?_
  let st9 : State := { st8 with regs := Function.update st8.regs 15 (a * a) }
  have hr8_15 : st8.regs 15 = a := by simp [st8]
  refine runs_seq_assign_le (v := a * a)
    (Expr.eval_mul (Expr.eval_reg_of_eq hr8_15)
      (Expr.eval_reg_of_eq hr8_15) (by simpa [sq] using hqpow_lt 2 (by decide))) ?_
  let st10 : State := { st9 with regs := Function.update st9.regs 16 (a * a * (a * a)) }
  have hr9_15 : st9.regs 15 = a * a := by simp [st9]
  refine runs_seq_assign_le (v := a * a * (a * a))
    (Expr.eval_mul (Expr.eval_reg_of_eq hr9_15)
      (Expr.eval_reg_of_eq hr9_15) (by
        have h4eq : a * a * (a * a) = a ^ 4 := by ring
        rw [h4eq]; exact hqpow_lt 4 (by decide))) ?_
  have hr10_8 : st10.regs 8 = qRoot M := by
    dsimp [st10, st9, st8]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), hr7_8]
  have hr10_15 : st10.regs 15 = a * a := by
    dsimp [st10, st9]; rw [Function.update_of_ne (by decide), Function.update_self]
  have ha6_eq : a * a * (a * a) * (a * a) = a ^ 6 := by ring
  have ha7_eq : a * a * (a * a) * (a * a) * a = a ^ 7 := by ring
  have hr10_16 : st10.regs 16 = a * a * (a * a) := by simp [st10]
  have he11 : (Expr.bin .mul (.bin .mul (.reg 16) (.reg 15)) (.bin .add (.reg 8) (.const 1))).eval w st10 =
      some (a ^ 7) := by
    have hm1 := Expr.eval_mul (Expr.eval_reg_of_eq hr10_16)
      (Expr.eval_reg_of_eq hr10_15) (by rw [ha6_eq]; exact hqpow_lt 6 (by decide))
    have ha1 := Expr.eval_add (Expr.eval_reg_of_eq hr10_8) (Expr.eval_const h1w)
      (by simpa only [pow_one] using hqpow_lt 1 (by decide))
    have hm2 := Expr.eval_mul hm1 ha1 (by rw [ha7_eq]; exact hqpow_lt 7 (by decide))
    rwa [ha7_eq] at hm2
  let st11 : State := { st10 with regs := Function.update st10.regs 15 (a ^ 7) }
  refine runs_seq_assign_le (v := a ^ 7) he11 ?_
  let st12 : State := { st11 with regs := Function.update st11.regs 15 (qExpPow M) }
  have hr11_15 : st11.regs 15 = a ^ 7 := by simp [st11]
  have hqp_a : a ^ 7 + 2 = qExpPow M := hqp_eq
  have he12 : (Expr.bin .add (.reg 15) (.const 2)).eval w st11 = some (qExpPow M) := by
    have ha2 := Expr.eval_add (Expr.eval_reg_of_eq hr11_15)
      (Expr.eval_const h2w) (by rw [hqp_a]; exact hqp_lt)
    rwa [hqp_a] at ha2
  refine runs_seq_assign_le (v := qExpPow M) he12 ?_
  have hst12_inv : st12.regs 0 = d ∧ st12.regs 1 = M ∧ st12.regs 2 = st.regs 2 ∧ st12.regs 7 = phiVal := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp [st12, st11, st10, st9, st8]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        hf7 0 (by decide) (by decide)]
      dsimp [st6, st5, st4]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        hreg3 0 (by decide) (by decide)]
      dsimp [st2, st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr0]
    · dsimp [st12, st11, st10, st9, st8]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        hf7 1 (by decide) (by decide)]
      dsimp [st6, st5, st4]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        hreg3 1 (by decide) (by decide)]
      dsimp [st2, st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr1]
    · dsimp [st12, st11, st10, st9, st8]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        hf7 2 (by decide) (by decide)]
      dsimp [st6, st5, st4]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        hreg3 2 (by decide) (by decide)]
      dsimp [st2, st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    · dsimp [st12, st11, st10, st9, st8]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        hf7 7 (by decide) (by decide)]
      dsimp [st6, st5, st4]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        hreg3 7 (by decide) (by decide)]
      dsimp [st2, st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr7]
  have hm12 : st12.mem = st.mem := by dsimp [st12, st11, st10, st9, st8]; rw [hm7, hm3]
  have hp12 : st12.pos = st.pos := by dsimp [st12, st11, st10, st9, st8]; rw [hp7, hp3]
  have hqroot_le_log : qRoot M ≤ Nat.log 2 (d + M + 2) := by
    have hq1 : qRoot M ≤ (qRoot M) ^ 8 := by
      rcases eq_or_ne (qRoot M) 0 with h0 | hne
      · omega
      · exact Nat.le_self_pow (by decide) _
    have hq2 := qRoot_pow_eight_le M
    have hl : Nat.log 2 (M + 2) ≤ Nat.log 2 (d + M + 2) := Nat.log_mono_right (by omega)
    omega
  have hlogM2_le : Nat.log 2 (M + 2) ≤ Nat.log 2 (d + M + 2) := Nat.log_mono_right (by omega)
  by_cases hk0 : K_int = 0
  · subst hk0
    rw [ite_eq_left_iff.mpr fun h => absurd rfl h]
    have hr12_15 : st12.regs 15 = qExpPow M := by simp [st12]
    have h29 : 29 * qRoot M ≤ 29 * Nat.log 2 (d + M + 2) := Nat.mul_le_mul_left 29 hqroot_le_log
    have h13 : 13 * Nat.log 2 (M + 2) ≤ 13 * Nat.log 2 (d + M + 2) := Nat.mul_le_mul_left 13 hlogM2_le
    exact csExpZero_tail ω st st12 h1w hcs_lt hr12_15 hst12_inv hm12 hp12 (by
      simp only [pow8Expr_size, Expr.size]; omega)
  · rw [ite_eq_right_iff.mpr fun h => absurd h hk0]
    have hk1 : 1 ≤ K_int := Nat.pos_of_ne_zero hk0
    have hKγ_lt : Kγ < 2 ^ w := lt_trans (lt_trans (hKγ_Kint hk1) (by
      have := csExpFactor_le_gExpImpl Kγ c K_int d M
      dsimp [X]; omega)) hX_lt
    have hKint_2w : K_int < 2 ^ w := lt_trans hKint_lt hX_lt
    have h4M_lt : 4 * M < 2 ^ w := by
      have hX2 : 600 * X ≤ X * X := Nat.mul_le_mul_right X hX600
      have hX2_8 : X * X ≤ X ^ 8 := by
        have : X * X = X ^ 2 := by ring
        rw [this]; exact Nat.pow_le_pow_right (by omega) (by decide)
      have h4M : 4 * M ≤ 4 * X := by dsimp [X]; omega
      omega
    have hcube4_lt : (Nat.log 2 (4 * M) + 2) ^ 4 < 2 ^ w := lt_trans hlog4 hX8_lt
    set e_cs := csGammaExp Kγ (4 * M) * K_int * qOf M + qExpPow M
    have hecs_lt : e_cs < 2 ^ w := by
      have h1 : e_cs < 2 ^ e_cs := Nat.lt_pow_self (by decide : 1 < 2)
      have h2 : csExpFactor Kγ K_int M = 2 ^ e_cs + 1 := by simp [csExpFactor, e_cs]
      omega
    have hcsgam_lt : csGammaExp Kγ (4 * M) < 2 ^ w := by
      have hq2 : 2 ≤ qOf M := qOf_ge_two M
      have hkm : 1 ≤ K_int * qOf M := Nat.mul_pos hk1 (by omega)
      have h1 : csGammaExp Kγ (4 * M) ≤ csGammaExp Kγ (4 * M) * (K_int * qOf M) :=
        Nat.le_mul_of_pos_right _ hkm
      have h2 : csGammaExp Kγ (4 * M) * (K_int * qOf M) ≤ e_cs := by
        dsimp [e_cs]; rw [← mul_assoc]; exact Nat.le_add_right _ _
      omega
    have hprod1_lt : csGammaExp Kγ (4 * M) * K_int < 2 ^ w := by
      have : csGammaExp Kγ (4 * M) * K_int ≤ csGammaExp Kγ (4 * M) * K_int * qOf M :=
        Nat.le_mul_of_pos_right _ (by have := qOf_ge_two M; omega)
      omega
    have hprod2_lt : csGammaExp Kγ (4 * M) * K_int * qOf M < 2 ^ w := by
      dsimp [e_cs] at hecs_lt; omega
    let st13 : State := { st12 with regs := Function.update st12.regs 16 (4 * M) }
    refine runs_seq_assign_le (v := 4 * M)
      (Expr.eval_mul (Expr.eval_const (by omega : 4 < 2 ^ w)) (Expr.eval_reg_of_eq hst12_inv.2.1) h4M_lt) ?_
    have hcs4_tr := csGammaExpBlock_triple (w := w) (p := p) Kγ 16 14 3 4 5 6 (4 * M)
      (by decide) (by decide) hKγ_lt h4M_lt hcube4_lt hcsgam_lt h4w st13 (by simp [st13])
    refine runs_seq_triple_le hcs4_tr rfl ?_
    intro st14 ⟨hr14_14, hm14, hp14, hf14⟩
    have hst14_0 : st14.regs 0 = d := by
      rw [hf14 0 (by decide) (by decide) (by decide) (by decide) (by decide)]
      dsimp [st13]; rw [Function.update_of_ne (by decide), hst12_inv.1]
    have hst14_1 : st14.regs 1 = M := by
      rw [hf14 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
      dsimp [st13]; rw [Function.update_of_ne (by decide), hst12_inv.2.1]
    have hst14_2 : st14.regs 2 = st.regs 2 := by
      rw [hf14 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
      dsimp [st13]; rw [Function.update_of_ne (by decide), hst12_inv.2.2.1]
    have hst14_7 : st14.regs 7 = phiVal := by
      rw [hf14 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
      dsimp [st13]; rw [Function.update_of_ne (by decide), hst12_inv.2.2.2]
    have hst14_8 : st14.regs 8 = qRoot M := by
      rw [hf14 8 (by decide) (by decide) (by decide) (by decide) (by decide)]
      dsimp [st13]; rw [Function.update_of_ne (by decide)]
      dsimp [st12, st11, st10, st9, st8]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr7_8]
    have hst14_15 : st14.regs 15 = qExpPow M := by
      rw [hf14 15 (by decide) (by decide) (by decide) (by decide) (by decide)]
      dsimp [st13]; rw [Function.update_of_ne (by decide)]; simp [st12]
    have he15 : (Expr.bin .add (.bin .mul (.bin .mul (.reg 14) (.const K_int))
        (.bin .add (.reg 8) (.const 2))) (.reg 15)).eval w st14 = some e_cs := by
      have hm1 := Expr.eval_mul (Expr.eval_reg_of_eq hr14_14) (Expr.eval_const hKint_2w) hprod1_lt
      have haq := Expr.eval_add (Expr.eval_reg_of_eq hst14_8) (Expr.eval_const h2w) hq2_lt
      have hprod2_lt' : csGammaExp Kγ (4 * M) * K_int * (qRoot M + 2) < 2 ^ w := by
        simpa only [qOf_eq_qRoot_add_two] using hprod2_lt
      have hecs_lt' : csGammaExp Kγ (4 * M) * K_int * (qRoot M + 2) + qExpPow M < 2 ^ w := by
        dsimp only [e_cs] at hecs_lt
        simpa only [qOf_eq_qRoot_add_two] using hecs_lt
      have hm2 := Expr.eval_mul hm1 haq hprod2_lt'
      have hae := Expr.eval_add hm2 (Expr.eval_reg_of_eq hst14_15) hecs_lt'
      have hecs_eq : csGammaExp Kγ (4 * M) * K_int * (qRoot M + 2) + qExpPow M = e_cs := by
        dsimp only [e_cs]; rw [qOf_eq_qRoot_add_two]
      rwa [hecs_eq] at hae
    have hcs_def : csExpFactor Kγ K_int M = 2 ^ e_cs + 1 := by simp [csExpFactor, e_cs]
    have hlog4M_le := log2_four_mul_le d M hd
    have h29 : 29 * qRoot M ≤ 29 * Nat.log 2 (d + M + 2) := Nat.mul_le_mul_left 29 hqroot_le_log
    have h13 : 13 * Nat.log 2 (M + 2) ≤ 13 * Nat.log 2 (d + M + 2) := Nat.mul_le_mul_left 13 hlogM2_le
    have h35 : 35 * Nat.log 2 (4 * M) ≤ 35 * (Nat.log 2 (d + M + 2) + 2) := Nat.mul_le_mul_left 35 hlog4M_le
    exact csExpPos_tail ω st st14 h1w hcs_lt hcs_def hecs_lt
      hst14_0 hst14_1 hst14_2 hst14_7 (by rw [hm14, hm12]) (by rw [hp14, hp12]) he15 (by
        simp only [pow8Expr_size, Expr.size]; omega)

end MinCostFlow.Expander.PathDSProg
