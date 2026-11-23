module

public import MinCostFlow.LSF.Program.InitDriver

/-!
# The init driver, steps `0 … 18`

The first segment reads the sizes `n₀, m₀` of `G₀` from its header, computes `log₂ (n₀ + 1)` and
`log₂ n₀` with two calls, and from them the sizes and places of the static blocks
(`InitPlaces.lean`). `segA_wp` says: if the rest of the steps runs from registers that hold these
numbers, then the whole sequence runs.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program InitDriver

@[expose] public section

/-- The cost of the first segment. -/
def segACost (n0 : ℕ) : ℕ := 40 * Nat.log 2 (n0 + 1) + 600

/-- The numbers in registers `10 … 28` after the first segment. -/
def segAVals (V : InitVals) : List ℕ :=
  [V.n0, V.m0, V.tM, Nat.log 2 (V.n0 + 1), Nat.log 2 V.n0, auxLogCap V.n0, hldDepthBound V.n0,
    auxSize V.vCap V.n0, dynGraphSize V.vCap V.eCap, tBlockSize V.vCap V.eCap V.tM, V.gPtr,
    V.tPtr, V.fPtr, V.fAncPtr, V.wPtr, V.auxPtr, V.numSt, V.denSt, V.endA]

/-- Evaluate an expression of the driver, with its word bounds from the context. -/
macro "ev" : tactic => `(tactic| (
  show Expr.eval _ _ _ = _
  try simp only [Nat.reduceAdd, Nat.zero_add]
  dsimp only [rG0, rLen, rWt, rLin, rPfp, rKn, rLw, rVc, rEc, rB, rN, rM, rTM, rLg1, rLg0, rLog, rD, rAuxSz, rDyn, rTB, rGP, rTP, rFP, rFA, rWP, rAux, rNumSt, rDenSt, rEnd, rCnt, rKw, rK, rQ, rMult, rCT, rCH, rCL, rCW, rCO, rCS, rOO, rOB, rOH, rUB, rTO, rTT, rTH, rLH, rH, rNO, rVI, rVL, rAP, rMin, rThD, rS, rEu, rEv, rDP, rTmp, rArr, rScr, rThB, rTh, rLB, rDB, rHi, rInR, rNumS, rId, rWB]
  eval_expr
  all_goals (try simp only [dgNOff, dgMOff, dgVCapOff, dgECapOff, auxHdrSize, tHdrSize,
    lsfHdrSize, fAncHdrSize, wHdrSize] at *)
  all_goals omega))

set_option maxHeartbeats 2000000 in
theorem segA_wp {w : ℕ} {p : Program} {I : InitIdx} {P : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop}
    (hP : UpClosed P) {rest : List DStep} {regs mem : ℕ → ℕ} {B : ℕ} {G₀ : MGraph}
    {g0Ptr vCap0 eCap0 : ℕ} (V : InitVals)
    (hlog : MeetsContract w p I.log2 log2Contract)
    (r0 : regs rG0 = g0Ptr) (r6 : regs rLw = V.L_w) (r7 : regs rVc = V.vCap)
    (r8 : regs rEc = V.eCap) (r9 : regs rB = V.b)
    (hdg : DynGraphAt mem g0Ptr vCap0 eCap0 G₀) (hn : G₀.n = V.n0) (hm : G₀.E.card = V.m0)
    (hg0 : g0Ptr + dynGraphSize vCap0 eCap0 ≤ V.b) (hm0 : V.m0 ≤ V.eCap) (hn0 : V.n0 ≤ V.vCap)
    (hn1 : 1 ≤ V.n0) (hw : V.endA + 6 < 2 ^ w) (hB : segACost V.n0 ≤ B)
    (hnext : ∀ regs', (∀ j < 10, regs' j = regs j) →
      (∀ j < 19, regs' (10 + j) = (segAVals V).getD j 0) →
      SeqWPR w p 10 P 19 rest regs' mem (B - segACost V.n0)) :
    SeqWPR w p 10 P 0 (segA I ++ rest) regs mem B := by
  have hN : mem (g0Ptr + dgNOff) = V.n0 := by rw [← hn]; exact hdg.2.2.2.2.2.1
  have hM : mem (g0Ptr + dgMOff) = V.m0 := by rw [← hm]; exact hdg.2.2.2.2.2.2.1
  have hlg : Nat.log 2 V.n0 ≤ Nat.log 2 (V.n0 + 1) := Nat.log_mono_right (by omega)
  have hlgn : Nat.log 2 (V.n0 + 1) < V.n0 + 1 := Nat.log_lt_self 2 (by omega)
  have hlgn0 : Nat.log 2 V.n0 < V.n0 := Nat.log_lt_self 2 (by omega)
  have hE := V.aux_order
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := hE
  have hdgs : dynGraphSize V.vCap V.eCap = 4 + 7 * V.vCap + 9 * V.eCap := rfl
  have htb : tBlockSize V.vCap V.eCap V.tM = 8 + (4 + 7 * V.vCap + 9 * (2 * V.tM + 1)) +
      4 * V.tM + V.eCap + (4 + 2 * V.tM) := rfl
  have hfa : fAncSize V.vCap = 6 + 5 * V.vCap := rfl
  have hwb : wBlockSize V.n0 = 7 + (V.n0 + 1) + 2 * V.n0 + (V.n0 + 1) + V.n0 := rfl
  have has : auxSize V.vCap V.n0 = 20 + 7 * V.vCap + 5 * V.n0 +
      2 * (V.n0 * (Nat.log 2 (V.n0 + 1) + 1)) + ((Nat.log 2 V.n0 + 1) * (Nat.log 2 V.n0 + 2) + 2) +
      (4 + V.n0) := rfl
  have htM : V.tM = V.n0 - 1 := rfl
  have hD : (Nat.log 2 V.n0 + 1) * (Nat.log 2 V.n0 + 2) ≤ auxSize V.vCap V.n0 := by
    rw [has]; omega
  have hNL : V.n0 * (Nat.log 2 (V.n0 + 1) + 1) ≤ auxSize V.vCap V.n0 := by rw [has]; omega
  have h1 : Nat.log 2 (V.n0 + 1) + 1 ≤ V.n0 * (Nat.log 2 (V.n0 + 1) + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have h2 : Nat.log 2 V.n0 + 2 ≤ (Nat.log 2 V.n0 + 1) * (Nat.log 2 V.n0 + 2) :=
    Nat.le_mul_of_pos_left _ (by omega)
  unfold segACost at hB
  simp only [segA, List.cons_append, List.nil_append]
  refine SeqWPR.assign hP V.n0 _ (by ev) le_rfl (by simp only [Expr.size, ld, add, mul, sub, r, k]; omega) ?_
  refine SeqWPR.assign hP V.m0 _ (by ev) le_rfl (by simp only [Expr.size, ld, add, mul, sub, r, k]; omega) ?_
  refine SeqWPR.assign hP (V.n0 - 1) _ (by ev) le_rfl
    (by simp only [Expr.size, ld, add, mul, sub, r, k]; omega) ?_
  refine SeqWPR.call hP log2Contract [V.n0 + 1] (20 * Nat.log 2 (V.n0 + 1) + 30) hlog
    (by show evalArgs _ _ _ = _; eval_expr) (by simp; omega) ⟨_, rfl, by omega⟩
    (by simp [log2Contract, argsSize, Expr.size, add, r, k]) (by simp only [Expr.size, ld, add, mul, sub, r, k]; omega) ?_
  rintro v₁ mem₁ ⟨x₁, hx₁, rfl, rfl⟩
  simp only [List.cons.injEq, and_true] at hx₁
  subst hx₁
  refine SeqWPR.call hP log2Contract [V.n0] (20 * Nat.log 2 V.n0 + 30) hlog
    (by show evalArgs _ _ _ = _; eval_expr) (by simp; omega) ⟨_, rfl, by omega⟩
    (by simp [log2Contract, argsSize, Expr.size, add, r, k]) (by simp only [Expr.size, ld, add, mul, sub, r, k]; omega) ?_
  rintro v₂ mem₂ ⟨x₂, hx₂, rfl, rfl⟩
  simp only [List.cons.injEq, and_true] at hx₂
  subst hx₂
  refine SeqWPR.assign hP _ _ (by ev) le_rfl (by simp only [Expr.size, ld, add, mul, sub, r, k]; omega) ?_
  refine SeqWPR.assign hP _ _ (by ev) le_rfl (by simp only [Expr.size, ld, add, mul, sub, r, k]; omega) ?_
  refine SeqWPR.assign hP _ _ (by ev) le_rfl (by simp only [Expr.size, ld, add, mul, sub, r, k]; omega) ?_
  refine SeqWPR.assign hP _ _ (by ev) le_rfl (by simp only [Expr.size, ld, add, mul, sub, r, k]; omega) ?_
  refine SeqWPR.assign hP _ _ (by ev) le_rfl (by simp only [Expr.size, ld, add, mul, sub, r, k]; omega) ?_
  refine SeqWPR.assign hP _ _ (by ev) le_rfl (by simp only [Expr.size, ld, add, mul, sub, r, k]; omega) ?_
  refine SeqWPR.assign hP _ _ (by ev) le_rfl (by simp only [Expr.size, ld, add, mul, sub, r, k]; omega) ?_
  refine SeqWPR.assign hP _ _ (by ev) le_rfl (by simp only [Expr.size, ld, add, mul, sub, r, k]; omega) ?_
  refine SeqWPR.assign hP _ _ (by
    have hdgF : dynGraphSize V.vCap (fECap V.eCap V.n0) = 4 + 7 * V.vCap + 9 * (3 * V.eCap + V.n0) :=
      rfl
    ev) le_rfl (by simp only [Expr.size, ld, add, mul, sub, r, k]; omega) ?_
  refine SeqWPR.assign hP _ _ (by ev) le_rfl (by simp only [Expr.size, ld, add, mul, sub, r, k]; omega) ?_
  refine SeqWPR.assign hP _ _ (by ev) le_rfl (by simp only [Expr.size, ld, add, mul, sub, r, k]; omega) ?_
  refine SeqWPR.assign hP _ _ (by ev) le_rfl (by simp only [Expr.size, ld, add, mul, sub, r, k]; omega) ?_
  refine SeqWPR.assign hP _ _ (by ev) le_rfl (by simp only [Expr.size, ld, add, mul, sub, r, k]; omega) ?_
  refine SeqWPR.assign hP _ _ (by ev) le_rfl (by simp only [Expr.size, ld, add, mul, sub, r, k]; omega) ?_
  refine SeqWPR.mono hP (hnext _ (fun j hj => ?_) (fun j hj => ?_)) ?_
  · repeat rw [Function.update_of_ne (by omega)]
  · have hdgF : dynGraphSize V.vCap (fECap V.eCap V.n0) =
        4 + 7 * V.vCap + 9 * (3 * V.eCap + V.n0) := rfl
    interval_cases j <;>
      (repeat (first | rw [Function.update_of_ne (by omega)] |
        rw [Function.update_apply, if_pos (by omega)])) <;>
      simp only [segAVals, List.getD_cons_zero, List.getD_cons_succ] <;>
      first | rfl | omega
  · simp only [Expr.size, ld, add, mul, sub, r, k, eDyn, segACost]
    omega

end

end MinCostFlow.LSF.Program
