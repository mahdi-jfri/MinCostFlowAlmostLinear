module

public import MinCostFlow.LSF.Program.InitCost
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The space of the init driver

The driver uses the memory from the handle `b` up to `(V.withH H).useEnd`, where `H` is the
heap pointer after the `[AN19]` call. `initUseEnd_le` bounds this end by `b` plus the static
blocks, a scratch copy of the two stretch arrays (`2 eCap L_w` words), the scratch of the
`[AN19]` call, and `200 (n₀ + m₀ + 1) (L_w + L_sim + auxLogCap n₀ + 20) + 1000` words for the
other work arrays.

The work arrays hold products such as `n₀ K`, `m₀ K_w`, `m₀ L_in` and `n₀ LB`. The widths are
at most `L_sim` (`K_w`, `L_in`), `2 L_sim + 7` (`K`) and `3 (L_w + L_sim + auxLogCap n₀ + 20)`
(the limb count `LB` of the stretch work, `wstrLB_le`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord
  InitDriver

@[expose] public section

/-- `log₂ (hldDepthBound n + 2) ≤ 2 auxLogCap n + 2`. -/
lemma log_hldDepth_le (n : ℕ) : Nat.log 2 (hldDepthBound n + 2) ≤ 2 * auxLogCap n + 2 := by
  set a := Nat.log 2 n
  have ha : a ≤ Nat.log 2 (n + 1) := Nat.log_mono_right (by omega)
  have h1 : hldDepthBound n + 2 ≤ 2 * (a + 2) ^ 2 := by
    simp only [hldDepthBound]
    nlinarith
  have h2 : a + 2 < 2 ^ (a + 2) := Nat.lt_two_pow_self
  have h3 : (a + 2) ^ 2 < (2 ^ (a + 2)) ^ 2 := Nat.pow_lt_pow_left h2 (by norm_num)
  have h4 : hldDepthBound n + 2 < 2 ^ (2 * a + 5) := by
    have : (2 : ℕ) ^ (2 * a + 5) = 2 * (2 ^ (a + 2)) ^ 2 := by ring
    omega
  have := Nat.log_lt_of_lt_pow (by omega) h4
  simp only [auxLogCap]
  omega

/-- The limb count of the stretch work is at most `3 (L_w + Ls + auxLogCap n + 20)`. -/
lemma wstrLB_le (n L_w Ls : ℕ) :
    wstrLB n (hldDepthBound n) L_w ≤ 3 * (L_w + Ls + auxLogCap n + 20) := by
  have := log_hldDepth_le n
  simp only [wstrLB]
  simp only [auxLogCap] at this ⊢
  omega

private lemma mul_le_P {a x N Y c d : ℕ} (ha : a ≤ c * N) (hx : x ≤ d * Y) :
    a * x ≤ (c * d) * (N * Y) := by
  calc a * x ≤ (c * N) * (d * Y) := Nat.mul_le_mul ha hx
    _ = (c * d) * (N * Y) := by ring

/-- The end of the memory that the driver uses. -/
theorem initUseEnd_le (Q_AN : Program) {c_AN : ℕ} (K_AN : ℝ) {h : ℕ} (V : InitVals) {H : ℕ}
    (hc : 1 ≤ c_AN) (hKw : V.K_w = kWidthOf V.m0 V.L_in) (hKK : V.K = widthK V.m0 V.L_in)
    (hLBV : V.LB = wstrLB V.n0 (hldDepthBound V.n0) V.L_w)
    (hH : H ≤ V.lsstHeap + lsstSpace Q_AN K_AN V.n0 (2 * V.m0)
      (lsstLSimMin c_AN 0 (2 * V.m0) V.L_in h) h) :
    (V.withH H).useEnd ≤ V.b + (lsfStaticSize V.vCap V.eCap V.n0 V.n0 V.L_w +
      2 * (V.eCap * V.L_w) +
      lsstSpace Q_AN K_AN V.n0 (2 * V.m0) (lsstLSimMin c_AN V.n0 (2 * V.m0) V.L_in h) h +
      200 * (V.n0 + V.m0 + 1) *
        (V.L_w + lsstLSimMin c_AN V.n0 (2 * V.m0) V.L_in h + auxLogCap V.n0 + 20) + 1000) := by
  set Ls := lsstLSimMin c_AN V.n0 (2 * V.m0) V.L_in h with hLs
  have hLs0 : lsstLSimMin c_AN 0 (2 * V.m0) V.L_in h = Ls := rfl
  rw [hLs0] at hH
  set lc := auxLogCap V.n0
  set N := V.n0 + V.m0 + 1
  set Y := V.L_w + Ls + lc + 20
  set S := lsstSpace Q_AN K_AN V.n0 (2 * V.m0) Ls h
  -- the widths
  have hKs : kWidthOf (2 * V.m0) V.L_in ≤ Ls := le_max_left _ _
  have hKw2 : V.K_w ≤ Ls := by
    rw [hKw]; exact (kWidthOf_mono (by omega : V.m0 ≤ 2 * V.m0)).trans hKs
  have hLin : V.L_in ≤ Ls := le_trans (by unfold kWidthOf; omega) hKs
  have hK : V.K ≤ 2 * Ls + 7 :=
    hKK.trans_le (widthK_le_lsim (h := h) (m0 := V.m0) (L_in := V.L_in) hc)
  have hLB : V.LB ≤ 3 * Y := by rw [hLBV]; exact wstrLB_le V.n0 V.L_w Ls
  -- the products, against `P = N * Y`
  have hnN : V.n0 ≤ 1 * N := by omega
  have hmN : V.m0 ≤ 1 * N := by omega
  have p1 : V.n0 * V.K ≤ (1 * 2) * (N * Y) := mul_le_P hnN (by omega)
  have p2 : V.m0 * (V.K_w + 6) ≤ (1 * 1) * (N * Y) := mul_le_P hmN (by omega)
  have p3 : V.m0 * V.L_in ≤ (1 * 1) * (N * Y) := mul_le_P hmN (by omega)
  have p4 : V.n0 * V.LB ≤ (1 * 3) * (N * Y) := mul_le_P hnN hLB
  have p5 : V.m0 * V.LB ≤ (1 * 3) * (N * Y) := mul_le_P hmN hLB
  have p6 : V.tM * V.LB ≤ (1 * 3) * (N * Y) :=
    mul_le_P (show V.tM ≤ 1 * N by simp only [InitVals.tM]; omega) hLB
  have p7 : V.n0 * (3 * auxLogCap V.n0) ≤ (1 * 3) * (N * Y) := mul_le_P hnN (by omega)
  have p8 : 1 * Y ≤ 1 * (N * Y) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  have hY : 20 ≤ Y := by omega
  have hNY : N ≤ N * Y := Nat.le_mul_of_pos_right _ (by omega)
  have e1 : 2 * V.m0 * V.L_in = 2 * (V.m0 * V.L_in) := by ring
  have e2 : 200 * N * Y = 200 * (N * Y) := by ring
  rw [e2]
  simp only [InitVals.useEnd, InitVals.wBase, wsPt, wsStep, InitVals.idPtr, InitVals.numS,
    InitVals.inR, InitVals.hiCopy, InitVals.dBase, InitVals.thBase, InitVals.scratchPtr,
    InitVals.arrPtr, InitVals.tmpPtr, InitVals.dPtr, InitVals.ev, InitVals.eu, InitVals.sPtr,
    InitVals.rtOut, InitVals.withH, wWorkSize]
  simp only [InitVals.lsstHeap, InitVals.tHead, InitVals.tTail, InitVals.tOrig,
    InitVals.usedBridge, InitVals.outHdr, InitVals.outBridge, InitVals.outOrig, InitVals.copySub,
    InitVals.copyOrig, InitVals.copyWt, InitVals.copyLen, InitVals.copyHead, InitVals.copyTail,
    InitVals.mult, InitVals.qNat, InitVals.Kq, InitVals.endA, lsfEndAddr] at hH
  have hst : lsfStaticSize V.vCap V.eCap V.n0 V.tM V.L_w ≤
      lsfStaticSize V.vCap V.eCap V.n0 V.n0 V.L_w := by
    simp only [lsfStaticSize, tBlockSize, dynGraphSize, InitVals.tM]
    omega
  rw [e1] at hH
  have htM : V.tM ≤ V.n0 := Nat.sub_le _ _
  have htMH : (V.withH H).tM = V.tM := rfl
  simp only [InitVals.withH] at htMH
  rw [htMH]
  omega

end

end MinCostFlow.LSF.Program
