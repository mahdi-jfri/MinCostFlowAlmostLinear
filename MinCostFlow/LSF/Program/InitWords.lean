module

public import MinCostFlow.LSF.Program.InitSpace
import MinCostFlow.LSF.Program.InitArena
import MinCostFlow.LSF.Program.WstrThresh
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The word bounds of the init driver

The driver `main_wp` and its input `SegBIn` ask that many numbers are words: addresses of the
work arrays, widths, and a few counts. The data-structure contract gives only that the handle
plus the space bound `lsfInitSpace` is a word, and that the arguments are words. This file
derives every word bound from these two facts (`initWordBounds`).

The idea is simple. Every address the driver touches is at most `useEnd`, which is at most the
handle plus the space bound (`initUseEnd_le`). The widths are at most `L_sim`, which is at most
the scratch of the `[AN19]` call. The counts are at most the work term
`200 (n₀ + m₀ + 1) (L_w + L_sim + auxLogCap n₀ + 20)` of the space bound.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord
  InitDriver

@[expose] public section

/-- The space bound of the driver, in the numbers of `V`. -/
noncomputable def initSpaceV (Q_AN : Program) (K_AN : ℝ) (c_AN h : ℕ) (V : InitVals) : ℕ :=
  lsfStaticSize V.vCap V.eCap V.n0 V.n0 V.L_w + 2 * (V.eCap * V.L_w) +
    lsstSpace Q_AN K_AN V.n0 (2 * V.m0) (lsstLSimMin c_AN V.n0 (2 * V.m0) V.L_in h) h +
    200 * (V.n0 + V.m0 + 1) *
      (V.L_w + lsstLSimMin c_AN V.n0 (2 * V.m0) V.L_in h + auxLogCap V.n0 + 20) + 1000

/-- The word bounds that `main_wp` and `SegBIn` ask for. -/
structure InitWordBounds (w h : ℕ) (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (V : InitVals)
    (kk P_fp : ℕ) : Prop where
  hw : V.endA + 6 < 2 ^ w
  hU : ∀ H, H ≤ V.lsstHeap + lsstSpace Q_AN K_AN V.n0 (2 * V.m0)
    (lsstLSimMin c_AN 0 (2 * V.m0) V.L_in h) h → (V.withH H).useEnd < 2 ^ w
  hl20 : thBound V.n0 + 2 * V.n0 + 8 < 2 ^ w
  hDw : 2 * (hldDepthBound V.n0 + 1) < 2 ^ w
  hm0w : 2 * V.m0 < 2 ^ w
  hLBw : wstrLB V.n0 (hldDepthBound V.n0) V.L_w < 2 ^ w
  hkw : kk < 2 ^ w
  hLw : V.L_w < 2 ^ w
  hPw : P_fp < 2 ^ w
  hsp : V.lsstHeap + V.m0 * multQNatStepSpace V.K_w < 2 ^ w
  hec : V.eCap + (2 * V.m0 + V.n0) + V.eCap < 2 ^ w
  hl1 : 16 * (2 * V.m0) + 6 < 2 ^ w
  hl3 : c_AN < 2 ^ w
  hl4 : h < 2 ^ w
  hl5 : kWidthOf (2 * V.m0) V.L_in < 2 ^ w
  hl6 : Nat.log 2 (16 * (2 * V.m0) + 6) + kWidthOf (2 * V.m0) V.L_in * h + 3 < 2 ^ w
  hl7 : w'Max c_AN 0 (2 * V.m0) V.L_in h < 2 ^ w
  hspL : V.lsstHeap + lsstSpace Q_AN K_AN V.n0 (2 * V.m0)
    (lsstLSimMin c_AN 0 (2 * V.m0) V.L_in h) h < 2 ^ w
  hkw3 : 3 * (4 * kk * (hldDepthBound V.n0 + 1)) < 2 ^ w
  hwK : widthK V.m0 V.L_in < 2 ^ w

/-- Three times `L_sim` plus `7` fits in the scratch of the `[AN19]` call. -/
private lemma lsim_le_space (Q_AN : Program) (K_AN : ℝ) {n m0 Ls h : ℕ} :
    3 * Ls + 7 ≤ lsstSpace Q_AN K_AN n (2 * m0) Ls h := by
  have h1 : 13 * Ls ≤ weightsSpace (2 * m0) Ls := by unfold weightsSpace; omega
  have h2 : 5 ≤ simDecodeSpace Q_AN (2 * (2 * m0)) (4 * (2 * m0)) Ls h
      (anCostBound K_AN n (2 * m0) Ls h) := by dsimp only [simDecodeSpace]; omega
  unfold lsstSpace
  omega

/-- `log₂ n + 1 ≤ n + 1`. -/
private lemma log_succ_le (n : ℕ) : Nat.log 2 n + 1 ≤ n + 1 := by
  have := Nat.log_le_self 2 n
  omega

/-- The init driver's word bounds, from the handle plus the space bound being a word. -/
theorem initWordBounds (Q_AN : Program) {c_AN : ℕ} (K_AN : ℝ) {w h : ℕ} (V : InitVals)
    {kk P_fp : ℕ} (hc : 1 ≤ c_AN) (hhw : 3 * h + 2 ≤ w) (hn1 : 1 ≤ V.n0)
    (hLin : 1 ≤ V.L_in) (hKw : V.K_w = kWidthOf V.m0 V.L_in) (hKK : V.K = widthK V.m0 V.L_in)
    (hLBV : V.LB = wstrLB V.n0 (hldDepthBound V.n0) V.L_w)
    (hS : V.b + initSpaceV Q_AN K_AN c_AN h V < 2 ^ w)
    (hk3 : 3 * (4 * kk * (hldDepthBound V.n0 + 1)) < 2 ^ w)
    (hLw : V.L_w < 2 ^ w) (hPw : P_fp < 2 ^ w) :
    InitWordBounds w h Q_AN c_AN K_AN V kk P_fp := by
  set Ls := lsstLSimMin c_AN V.n0 (2 * V.m0) V.L_in h with hLs
  have hLs0 : lsstLSimMin c_AN 0 (2 * V.m0) V.L_in h = Ls := rfl
  set Sp := lsstSpace Q_AN K_AN V.n0 (2 * V.m0) Ls h with hSp
  set N := V.n0 + V.m0 + 1 with hN
  set Y := V.L_w + Ls + auxLogCap V.n0 + 20 with hY
  have hS' : V.b + (lsfStaticSize V.vCap V.eCap V.n0 V.n0 V.L_w + 2 * (V.eCap * V.L_w) + Sp +
      200 * (N * Y) + 1000) < 2 ^ w := by
    have e : 200 * N * Y = 200 * (N * Y) := by ring
    have := hS
    unfold initSpaceV at this
    rw [← hLs, ← hSp, ← hN, ← hY, e] at this
    exact this
  -- the useEnd bound
  have hUe : ∀ H, H ≤ V.lsstHeap + Sp → (V.withH H).useEnd < 2 ^ w := by
    intro H hH
    have := initUseEnd_le Q_AN K_AN V hc hKw hKK hLBV (H := H) (by rw [hLs0]; exact hH)
    unfold initSpaceV at hS
    omega
  have hHmax := hUe _ le_rfl
  have hH_le : V.lsstHeap + Sp ≤ (V.withH (V.lsstHeap + Sp)).useEnd := by
    obtain ⟨u1, -, u3, -⟩ := (V.withH (V.lsstHeap + Sp)).useEnd_ge
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, s17, s18, s19, s20, s21, s22, s23,
      s24, s25, -⟩ := (V.withH (V.lsstHeap + Sp)).scratch_order
    have : (V.withH (V.lsstHeap + Sp)).H = V.lsstHeap + Sp := rfl
    omega
  have hspL : V.lsstHeap + Sp < 2 ^ w := lt_of_le_of_lt hH_le hHmax
  have hY20 : 20 ≤ Y := by omega
  have hNY : N * 20 ≤ N * Y := Nat.mul_le_mul_left _ hY20
  have hY1 : Y ≤ N * Y := Nat.le_mul_of_pos_left _ (by omega)
  -- the widths
  have hkW : kWidthOf (2 * V.m0) V.L_in ≤ Ls := le_max_left _ _
  have hwM : w'Max c_AN V.n0 (2 * V.m0) V.L_in h ≤ Ls := le_max_right _ _
  have hLs3 := lsim_le_space Q_AN K_AN (n := V.n0) (m0 := V.m0) (Ls := Ls) (h := h)
  have hcw : c_AN ≤ w'Max c_AN V.n0 (2 * V.m0) V.L_in h :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hl6w : Nat.log 2 (16 * (2 * V.m0) + 6) + kWidthOf (2 * V.m0) V.L_in * h + 3 ≤
      w'Max c_AN V.n0 (2 * V.m0) V.L_in h := by
    unfold w'Max
    rw [show 16 * (2 * V.m0) + 6 = 6 + 16 * (2 * V.m0) by ring]
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hK : widthK V.m0 V.L_in ≤ 2 * Ls + 7 := widthK_le_lsim (h := h) hc
  -- the step space of the tree phase
  have hmq : V.m0 * multQNatStepSpace V.K_w ≤ Sp := by
    rcases Nat.eq_zero_or_pos V.m0 with hm0 | hm1
    · rw [hm0, Nat.zero_mul]; exact Nat.zero_le _
    have := div_arena_le_lsstSpace Q_AN c_AN K_AN
      ⟨V.b, V.vCap, V.eCap, V.n0, V.m0, V.L_in, V.L_w, Ls, h⟩ hm1 (by omega) hLin le_rfl
    simp only [InitArena.K_w, InitArena.K_q] at this
    rw [hKw]
    have e : V.m0 * multQNatStepSpace (kWidthOf V.m0 V.L_in) ≤
        V.m0 * (6 * kWidthOf V.m0 V.L_in + Num.integerDivideSpace (kWidthOf V.m0 V.L_in) +
          Num.integerDivideSpace (kWidthOf V.m0 V.L_in + 6) + 20) :=
      Nat.mul_le_mul_left _ (by unfold multQNatStepSpace; omega)
    omega
  -- the static part and the scratch below the heap
  have hend : V.endA + 6 ≤ V.lsstHeap := (V.useEnd_ge).2.2.2
  have hec : V.eCap + (2 * V.m0 + V.n0) + V.eCap < 2 ^ w := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, s12, s13, s14, s15, s16, -⟩ := V.scratch_order
    have hst : V.endA = V.b + lsfStaticSize V.vCap V.eCap V.n0 V.tM V.L_w := rfl
    have hdg : lsfStaticSize V.vCap V.eCap V.n0 V.tM V.L_w ≥ 2 * V.eCap := by
      simp only [lsfStaticSize, dynGraphSize]; omega
    have : V.endA ≤ V.usedBridge := by
      obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, -⟩ := V.scratch_order
      omega
    omega
  -- `thBound` and the depth bound
  have hth : thBound V.n0 ≤ N * Y := by
    unfold thBound
    have h1 := log_succ_le V.n0
    have h2 : Nat.log 2 V.n0 ≤ Nat.log 2 (V.n0 + 1) := Nat.log_mono_right (by omega)
    exact Nat.mul_le_mul (by omega) (by unfold auxLogCap at hY; omega)
  have hthD : hldDepthBound V.n0 = thBound V.n0 := rfl
  have hLB : wstrLB V.n0 (hldDepthBound V.n0) V.L_w ≤ 3 * Y := wstrLB_le V.n0 V.L_w Ls
  have hkk : kk ≤ 3 * (4 * kk * (hldDepthBound V.n0 + 1)) := by
    have : kk ≤ kk * (hldDepthBound V.n0 + 1) := Nat.le_mul_of_pos_right _ (by omega)
    nlinarith
  have hh2 : h < 2 ^ w :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
  exact
    { hw := by omega
      hU := fun H hH => hUe H (by rw [hLs0] at hH; exact hH)
      hl20 := by omega
      hDw := by omega
      hm0w := by omega
      hLBw := by omega
      hkw := by omega
      hLw := hLw
      hPw := hPw
      hsp := by omega
      hec := hec
      hl1 := by omega
      hl3 := by omega
      hl4 := hh2
      hl5 := by omega
      hl6 := by omega
      hl7 := by change w'Max c_AN V.n0 (2 * V.m0) V.L_in h < 2 ^ w; omega
      hspL := by rw [hLs0]; exact hspL
      hkw3 := hk3
      hwK := by omega }

/-- The constant `C` of the stretch threshold fits in `L_w` limbs. -/
theorem defaultC_lt {K_AN : ℝ} {n k h L_w L_in : ℕ} (hk : 1 ≤ k)
    (hθ : defaultThreshNat K_AN n k < 2 ^ (h * (L_w - L_in))) :
    defaultC_ceil K_AN < 2 ^ (h * L_w) := by
  rw [← threshProd_eq K_AN hk] at hθ
  have hle : defaultC_ceil K_AN ≤ threshProd (defaultC_ceil K_AN) n k := by
    unfold threshProd
    have a : 1 ≤ 9 * (hldDepthBound n + 1) * (hldDepthBound n + 1) := by
      nlinarith
    have b : 1 ≤ Nat.log 2 (n + 2) + 1 := by omega
    calc defaultC_ceil K_AN
        ≤ 9 * (hldDepthBound n + 1) * (hldDepthBound n + 1) * defaultC_ceil K_AN :=
          Nat.le_mul_of_pos_left _ a
      _ ≤ _ * (Nat.log 2 (n + 2) + 1) := Nat.le_mul_of_pos_right _ b
      _ ≤ _ * (Nat.log 2 (n + 2) + 1) := Nat.le_mul_of_pos_right _ b
      _ ≤ _ * k := Nat.le_mul_of_pos_right _ hk
  have hp : 2 ^ (h * (L_w - L_in)) ≤ 2 ^ (h * L_w) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  omega

end

end MinCostFlow.LSF.Program
