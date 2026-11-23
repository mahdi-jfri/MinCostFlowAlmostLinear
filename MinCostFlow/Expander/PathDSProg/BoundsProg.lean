module

public import WordRAM.Logic
public import MinCostFlow.Expander.PathDSProg.BoundsLoopProg

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
public import MinCostFlow.Expander.PathDSProg.BoundsProgBase

/-!
# Deterministic Parameter Evaluator (`boundsProcs`) for `PathDSImpl`

Implements `pathDSBoundsProcs Kγ c K_int : List WordRAM.Stmt` — a single deterministic
(`Stmt.NoRand`) Word-RAM procedure computing
`[phiOutDenImpl Kγ c d M, gExpImpl Kγ c K_int d M, gDelImpl K_int d M]` at `[h, h+1, h+2]`
and returning `h + 3`, satisfying `pathDSBoundsContract (pathDSParams Kγ c K_int cw_cs) w`
within cost `2000 * (Nat.log 2 (d + M + 2) + 1)` and space `3`.

Assembled from four sequential `Triple` blocks over `BoundsLoopProg`:
1. `phiOutBlock`: `reg 7 := phiOutDenImpl Kγ c d M`.
2. `csExpBlock`: `reg 9 := csExpFactor Kγ K_int M`.
3. `lenBlock`: `reg 17 := phiOutDenImpl Kγ c d M * lenFactor M`.
4. `storeRetBoundsBlock`: writes `[reg 7, reg 17 + reg 9, gDel]` at `[h, h+1, h+2]` and returns
   `h + 3`.
-/

@[expose] public section

namespace MinCostFlow.Expander.PathDSProg

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- Block 3: with `reg 7 = phiOutDenImpl Kγ c d M`, computes `reg 17 := phiOutDen · lenFactor M`.
It finds `log₂(6M + 2)` by halving. Preserves `0, 1, 2, 7, 9` and `mem`. -/
def lenBlock : Stmt :=
  .assign 3 (.bin .add (.bin .mul (.const 6) (.reg 1)) (.const 2)) ;;
  .assign 4 (.const 0) ;;
  .loop (.bin .lt (.const 1) (.reg 3))
    (.assign 3 (.bin .div (.reg 3) (.const 2)) ;;
     .assign 4 (.bin .add (.reg 4) (.const 1))) ;;
  .assign 17 (.bin .mul (.reg 7) (.bin .mul (.const 120) (.bin .add (.reg 4) (.const 1))))

lemma lenBlock_noRand : lenBlock.NoRand := by simp [lenBlock, Stmt.NoRand]

theorem lenBlock_triple {w Kγ c K_int cw_cs d M csVal : ℕ} {p : Program}
    (hd : 1 ≤ d)
    (hcw : max 24 (4 * cw_cs + 8) *
      (Nat.log 2 (d + M + gExpImpl Kγ c K_int d M + gDelImpl K_int d M + 2) + 1) ≤ w)
    (st₀ : State) (hr0 : st₀.regs 0 = d) (hr1 : st₀.regs 1 = M)
    (hr7 : st₀.regs 7 = phiOutDenImpl Kγ c d M) (hr9 : st₀.regs 9 = csVal) :
    Triple w p (fun st => st = st₀) lenBlock
      (normalPost fun st' =>
        st'.regs 0 = d ∧ st'.regs 1 = M ∧ st'.regs 2 = st₀.regs 2 ∧
        st'.regs 7 = phiOutDenImpl Kγ c d M ∧ st'.regs 9 = csVal ∧
        st'.regs 17 = phiOutDenImpl Kγ c d M * lenFactor M ∧
        st'.mem = st₀.mem ∧ st'.pos = st₀.pos)
      (fun _ => 13 * (Nat.log 2 (6 * M + 2) + 1) + 40) := by
  have hwd := bounds_word_le (Kγ := Kγ) (c := c) (K_int := K_int) (cw_cs := cw_cs) (d := d) (M := M) (w := w) hd hcw
  rcases hwd with ⟨hX600, hX24, _⟩
  set X := d + M + gExpImpl Kγ c K_int d M + gDelImpl K_int d M + 2
  have hX2_lt : X ^ 2 < 2 ^ w := lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) (by decide)) hX24
  have hXX : 600 * X ≤ X ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right X hX600
  have hM_X : M + 2 ≤ X := by dsimp [X]; omega
  have h6M_lt : 6 * M + 2 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have h4w : 4 ≤ 2 ^ w := by omega
  set lg := Nat.log 2 (6 * M + 2)
  have hlg_le : lg ≤ 6 * M + 2 := Nat.log_le_self 2 _
  have hlg_lt : lg < 2 ^ w := by omega
  have hlg1_lt : lg + 1 < 2 ^ w := by omega
  have hlen_eq : 120 * (lg + 1) = lenFactor M := rfl
  have hprod_le : phiOutDenImpl Kγ c d M * lenFactor M ≤ gExpImpl Kγ c K_int d M := by
    unfold gExpImpl; exact Nat.le_add_right _ _
  have hgX : gExpImpl Kγ c K_int d M < X := by dsimp [X]; omega
  have hlen_lt : 120 * (lg + 1) < 2 ^ w := by
    have hphi1 : 1 ≤ phiOutDenImpl Kγ c d M := by unfold phiOutDenImpl; omega
    have : lenFactor M ≤ phiOutDenImpl Kγ c d M * lenFactor M := Nat.le_mul_of_pos_left _ hphi1
    rw [hlen_eq]
    have hXsq : X ≤ X ^ 2 := by nlinarith
    omega
  have hprod_lt : phiOutDenImpl Kγ c d M * (120 * (lg + 1)) < 2 ^ w := by
    rw [hlen_eq]
    have : gExpImpl Kγ c K_int d M < X := by dsimp [X]; omega
    omega
  intro st ω hst; subst hst
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := 6 * M + 2)
    (Expr.eval_add (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr1) (by omega))
      (Expr.eval_const (by omega)) h6M_lt) ?_
  let st1 : State := { st with regs := Function.update st.regs 3 (6 * M + 2) }
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  let st2 : State := { st1 with regs := Function.update st1.regs 4 0 }
  have hr3_tr := log2Loop_triple (w := w) (p := p) 3 4 (6 * M + 2) (by decide) h6M_lt h4w hlg_lt st2
    (by dsimp [st2, st1]; rw [Function.update_of_ne (by decide), Function.update_self])
    (by simp [st2])
  refine runs_seq_triple_le hr3_tr rfl ?_
  intro st3 ⟨hr3_4, hm3, hp3, hreg3⟩
  have hkeep3 : ∀ r, r ≠ 3 → r ≠ 4 → st3.regs r = st.regs r := by
    intro r h3 h4
    rw [hreg3 r h3 h4]
    dsimp [st2, st1]; rw [Function.update_of_ne h4, Function.update_of_ne h3]
  have hr3_7 : st3.regs 7 = phiOutDenImpl Kγ c d M := by rw [hkeep3 7 (by decide) (by decide), hr7]
  have he17 : (Expr.bin .mul (.reg 7) (.bin .mul (.const 120) (.bin .add (.reg 4) (.const 1)))).eval w st3 =
      some (phiOutDenImpl Kγ c d M * lenFactor M) := by
    have ha := Expr.eval_add (Expr.eval_reg_of_eq hr3_4) (Expr.eval_const h1w) hlg1_lt
    have hm := Expr.eval_mul (Expr.eval_const (show 120 < 2 ^ w by omega)) ha hlen_lt
    have hm2 := Expr.eval_mul (Expr.eval_reg_of_eq hr3_7) hm hprod_lt
    rwa [hlen_eq] at hm2
  refine runs_assign_le (v := phiOutDenImpl Kγ c d M * lenFactor M) he17 ?_ ?_
  · have hk : ∀ r, r ≠ 3 → r ≠ 4 → r ≠ 17 →
        ({ st3 with regs := Function.update st3.regs 17 (phiOutDenImpl Kγ c d M * lenFactor M) } :
          State).regs r = st.regs r := by
      intro r h3 h4 h17
      dsimp only
      rw [Function.update_of_ne h17, hkeep3 r h3 h4]
    refine ⟨?_, ?_, ?_, ?_, ?_, by simp, hm3, hp3⟩
    · rw [hk 0 (by decide) (by decide) (by decide), hr0]
    · rw [hk 1 (by decide) (by decide) (by decide), hr1]
    · rw [hk 2 (by decide) (by decide) (by decide)]
    · rw [hk 7 (by decide) (by decide) (by decide), hr7]
    · rw [hk 9 (by decide) (by decide) (by decide), hr9]
  · simp only [Expr.size]
    omega

/-- Block 4: stores `[phiOutDen, gExp, gDel]` at `h, h+1, h+2` and returns `h + 3`. -/
def storeRetBoundsBlock (K_int : ℕ) : Stmt :=
  .store (.reg 2) (.reg 7) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.bin .add (.reg 17) (.reg 9)) ;;
  .store (.bin .add (.reg 2) (.const 2)) (.const (gDelImpl K_int 0 0)) ;;
  .ret (.bin .add (.reg 2) (.const 3))

lemma storeRetBoundsBlock_noRand (K_int : ℕ) : (storeRetBoundsBlock K_int).NoRand := by
  simp [storeRetBoundsBlock, Stmt.NoRand]

/-! ## 2. Full `boundsProcs` and `MeetsContract` Theorem -/

/-- Full deterministic Word-RAM parameter evaluator for `PathDSImpl.boundsProcs`. -/
def pathDSBoundsProc (Kγ c K_int : ℕ) : Stmt :=
  phiOutBlock Kγ c ;;
  csExpBlock Kγ K_int ;;
  lenBlock ;;
  storeRetBoundsBlock K_int

/-- Singleton `boundsProcs` procedure list for `PathDSImpl`. -/
def pathDSBoundsProcs (Kγ c K_int : ℕ) : List Stmt :=
  [pathDSBoundsProc Kγ c K_int]

lemma pathDSBoundsProcs_nonempty (Kγ c K_int : ℕ) :
    0 < (pathDSBoundsProcs Kγ c K_int).length := by
  simp [pathDSBoundsProcs]

lemma pathDSBoundsProcs_noRand (Kγ c K_int : ℕ) :
    ∀ s ∈ pathDSBoundsProcs Kγ c K_int, s.NoRand := by
  intro s hs
  simp only [pathDSBoundsProcs, List.mem_singleton] at hs
  subst hs
  simp [pathDSBoundsProc, phiOutBlock_noRand, csExpBlock_noRand, lenBlock_noRand,
    storeRetBoundsBlock_noRand, Stmt.NoRand]

/-- Main contract theorem for `pathDSBoundsProcs`: satisfies `pathDSBoundsContract (pathDSParams ...) w`
when `p.procs[bB]? = some (pathDSBoundsProc Kγ c K_int)`. -/
theorem pathDSBoundsProc_meetsContract {Kγ c K_int cw_cs w bB : ℕ} {p : Program}
    (hproc : p.procs[bB]? = some (pathDSBoundsProc Kγ c K_int)) :
    MeetsContract w p bB (pathDSBoundsContract (pathDSParams Kγ c K_int cw_cs) w) := by
  refine meetsContract_of_triple hproc fun args mem pos hwords hpre => ?_
  rcases hpre with ⟨⟨d, M, h, rfl, hd, hcw⟩, hzero, hsp⟩
  have hcw' : max 24 (4 * cw_cs + 8) *
      (Nat.log 2 (d + M + gExpImpl Kγ c K_int d M + gDelImpl K_int d M + 2) + 1) ≤ w := by
    simpa [pathDSParams] using hcw
  have hsp' : h + 3 < 2 ^ w := by
    simpa [heapArg, pathDSParams] using hsp
  have hwd := bounds_word_le (Kγ := Kγ) (c := c) (K_int := K_int) (cw_cs := cw_cs) (d := d) (M := M) (w := w) hd hcw'
  rcases hwd with ⟨hX1000, hX24, _, _, _, _, _, hgdel_lt, _, _, _, _⟩
  set X := d + M + gExpImpl Kγ c K_int d M + gDelImpl K_int d M + 2
  have hX8_lt : X ^ 8 < 2 ^ w := lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) (by decide)) hX24
  have hX_lt : X < 2 ^ w := lt_of_le_of_lt (Nat.le_self_pow (by decide) _) hX8_lt
  have hgexp_lt : gExpImpl Kγ c K_int d M < 2 ^ w := lt_trans (by
    have : gExpImpl Kγ c K_int d M < X := by dsimp [X]; omega
    exact this) hX_lt
  have hgdel_2w : gDelImpl K_int d M < 2 ^ w := lt_trans hgdel_lt hX_lt
  set st0 := startState [d, M, h] mem pos
  have hr0 : st0.regs 0 = d := rfl
  have hr1 : st0.regs 1 = M := rfl
  have hr2 : st0.regs 2 = h := rfl
  have hlog_ge : 2 ≤ Nat.log 2 (d + M + 2) + 1 := by
    have : 1 ≤ Nat.log 2 (d + M + 2) := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by omega)
    omega
  intro st ω hst; subst hst
  refine runs_start_le ?_
  refine runs_seq_triple_le (phiOutBlock_triple (Kγ := Kγ) (c := c) (K_int := K_int) (cw_cs := cw_cs) hd hcw' st0 hr0 hr1) rfl ?_
  intro st1 ⟨hr1_0, hr1_1, hr1_2, hr1_7, hm1, hp1⟩
  refine runs_seq_triple_le (csExpBlock_triple (Kγ := Kγ) (c := c) (K_int := K_int) (cw_cs := cw_cs) hd hcw' st1 hr1_0 hr1_1 hr1_7) rfl ?_
  intro st2 ⟨hr2_0, hr2_1, hr2_2, hr2_7, hr2_9, hm2, hp2⟩
  refine runs_seq_triple_le (lenBlock_triple (Kγ := Kγ) (c := c) (K_int := K_int) (cw_cs := cw_cs) hd hcw' st2 hr2_0 hr2_1 hr2_7 hr2_9) rfl ?_
  intro st4 ⟨_, _, hr4_2, hr4_7, hr4_9, hr4_17, hm4, hp4⟩
  have h2_eq : st4.regs 2 = h := by rw [hr4_2, hr2_2, hr1_2]; exact hr2
  have hm_eq : st4.mem = mem := by rw [hm4, hm2, hm1]; rfl
  refine runs_seq_store_le (Expr.eval_reg_of_eq h2_eq) (Expr.eval_reg_of_eq hr4_7) ?_
  have he_gexp : (Expr.bin .add (.reg 17) (.reg 9)).eval w
      { st4 with mem := Function.update st4.mem h (phiOutDenImpl Kγ c d M) } =
      some (gExpImpl Kγ c K_int d M) := by
    have hr7' : ({ st4 with mem := Function.update st4.mem h (phiOutDenImpl Kγ c d M) }).regs 7 = phiOutDenImpl Kγ c d M := hr4_7
    have hr9' : ({ st4 with mem := Function.update st4.mem h (phiOutDenImpl Kγ c d M) }).regs 9 = csExpFactor Kγ K_int M := hr4_9
    have hr17' : ({ st4 with mem := Function.update st4.mem h (phiOutDenImpl Kγ c d M) }).regs 17 =
        phiOutDenImpl Kγ c d M * lenFactor M := hr4_17
    have ha := Expr.eval_add (Expr.eval_reg_of_eq hr17') (Expr.eval_reg_of_eq hr9')
      (by simpa [gExpImpl] using hgexp_lt)
    simpa [gExpImpl] using ha
  refine runs_seq_store_le
    (Expr.eval_add (Expr.eval_reg_of_eq h2_eq) (Expr.eval_const (by omega)) (by omega))
    he_gexp ?_
  refine runs_seq_store_le
    (Expr.eval_add (Expr.eval_reg_of_eq h2_eq) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_const hgdel_2w) ?_
  have hheap : heapArg [d, M, h] = h := rfl
  refine runs_ret_le (Expr.eval_add (Expr.eval_reg_of_eq h2_eq) (Expr.eval_const (by omega)) hsp') ?_ ?_
  · refine ⟨⟨?_, le_rfl, ?_, ?_, d, M, h, rfl, ?_⟩, ?_⟩
    · dsimp only [Outcome.value]; rw [hheap]; omega
    · intro x hx
      rw [hheap] at hx
      dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), hm_eq]
    · intro x hx
      dsimp only [Outcome.value] at hx ⊢
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), hm_eq]
      exact hzero x (by rw [hheap]; omega)
    · intro i hi
      dsimp only [pathDSParams] at hi ⊢
      simp only [List.length_cons, List.length_nil] at hi
      interval_cases i
      · simp
      · simp
      · simp [gDelImpl]
    · dsimp only [Outcome.value]; rw [hheap]
  · have hlog3 : Nat.log 2 (6 * M + 2) ≤ Nat.log 2 (d + M + 2) + 3 := by
      have h1 : 6 * M + 2 ≤ (d + M + 2) * 2 * 2 * 2 := by omega
      have h2 : Nat.log 2 ((d + M + 2) * 2 * 2 * 2) = Nat.log 2 (d + M + 2) + 3 := by
        rw [Nat.log_mul_base (by decide) (by omega), Nat.log_mul_base (by decide) (by omega),
          Nat.log_mul_base (by decide) (by omega)]
      have := Nat.log_mono_right (b := 2) h1
      omega
    simp only [pathDSBoundsContract, heapContract, pathDSParams,
      List.getD_cons_zero, List.getD_cons_succ, Expr.size]
    linarith only [hlog_ge, hlog3]

end MinCostFlow.Expander.PathDSProg
