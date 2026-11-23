module

public import MinCostFlow.LSF.Program.InitOrderIn

/-!
# The init driver, steps `40 … 54`

The third segment reads the number `nOrig` of original edges of `T₀` that the tree phase wrote,
computes the places of the aux arrays and of the scratch areas of the order phase, and runs the
order phase. `segC_wp` takes `OrderPhaseIn` at the places `OrderLayout.ofVals V nOrig` (which
`orderIn_of_segB` gives) and says: if the rest of the steps runs from every outcome of the order
phase, then the whole sequence runs.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord
  InitDriver

@[expose] public section

/-- Steps `40 … 53`: `nOrig` and the places of the order phase. -/
def segCMid : List DStep :=
  [ .assign (ld (r rOH)),
    .assign (add (r rAux) (k auxHdrSize)),
    .assign (add (r rVI) (r rVc)),
    .assign (add (r rVL) (r rN)),
    .assign (add (add (r rAP) (mul (k 3) (r rN))) (mul (r rN) (r rLog))),
    .assign (add (r rMin) (mul (r rN) (r rLog))),
    .assign (add (r rH) (mul (k 3) (r rN))),
    .assign (add (add (r rS) (mul (k 4) (r rN))) (mul (k 2) (r rTM))),
    .assign (add (r rEu) (r rM)),
    .assign (add (r rEv) (r rM)),
    .assign (add (r rDP) (mul (r rN) (r rK))),
    .assign (add (r rTmp) (r rK)),
    .assign (add (r rArr) (r rN)),
    .assign (add (r rScr) (r rN))]

lemma segC_split (I : InitIdx) : segC I = segCMid ++ [.call I.order orderArgs] := rfl

/-- The numbers in registers `50 … 63` after `segCMid`. -/
def segCVals (V : InitVals) (nOrig : ℕ) : List ℕ :=
  [nOrig, V.vIdx, V.vListPtr, V.auxPar, V.minPtr, V.thDst, V.sPtr, V.eu, V.ev, V.dPtr, V.tmpPtr,
    V.arrPtr, V.scratchPtr, V.thBase]

/-- The places that the third segment computes, in terms of the earlier ones. -/
lemma InitVals.segC_eqs (V : InitVals) (hH : V.lsstHeap ≤ V.H) :
    V.vIdx = V.auxPtr + auxHdrSize ∧ V.vIdx + V.vCap = V.vListPtr ∧
    V.vListPtr + V.n0 = V.auxPar ∧
    V.minPtr = V.auxPar + 3 * V.n0 + V.n0 * auxLogCap V.n0 ∧
    V.minPtr + V.n0 * auxLogCap V.n0 = V.thDst ∧ V.thDst ≤ V.rtOut := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, -⟩ :=
    V.scratch_order
  refine ⟨rfl, e2, e3, V.minPtr_eq, e4, ?_⟩
  omega

macro "evc" : tactic => `(tactic| (
  show Expr.eval _ _ _ = _
  try simp only [Nat.reduceAdd, Nat.zero_add]
  dsimp only [rOH, rAux, rVI, rVc, rVL, rN, rAP, rLog, rMin, rH, rS, rTM, rEu, rM, rEv, rDP, rK,
    rTmp, rArr, rScr]
  eval_expr
  all_goals omega))

set_option maxHeartbeats 2000000 in
theorem segCMid_wp {w : ℕ} {p : Program} {P : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop}
    (hP : UpClosed P) {rest : List DStep} {regs mem : ℕ → ℕ} {B nOrig : ℕ} (V : InitVals)
    (a7 : regs 7 = V.vCap) (a10 : regs 10 = V.n0) (a11 : regs 11 = V.m0) (a12 : regs 12 = V.tM)
    (a15 : regs 15 = auxLogCap V.n0) (a25 : regs 25 = V.auxPtr) (a32 : regs 32 = V.K)
    (a43 : regs 43 = V.outHdr) (a49 : regs 49 = V.rtOut) (hO : mem V.outHdr = nOrig)
    (hH : V.lsstHeap ≤ V.H) (hW : V.thBase + 8 * V.n0 < 2 ^ w) (hw16 : 16 ≤ 2 ^ w)
    (hB : 400 ≤ B)
    (hnext : ∀ regs', (∀ j < 50, regs' j = regs j) →
      (∀ j < 14, regs' (50 + j) = (segCVals V nOrig).getD j 0) →
      SeqWPR w p 10 P 54 rest regs' mem (B - 400)) :
    SeqWPR w p 10 P 40 (segCMid ++ rest) regs mem B := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := V.segC_eqs hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, s17, s18, s19, s20, s21, s22, s23, s24,
    s25, -⟩ := V.scratch_order
  simp only [segCMid, List.cons_append, List.nil_append]
  refine SeqWPR.assign hP nOrig _ (by evc) le_rfl (by simp only [Expr.size, ld, r]; omega) ?_
  refine SeqWPR.assign hP V.vIdx _ (by rw [c1]; evc) le_rfl
    (by simp only [Expr.size, add, r, k]; omega) ?_
  refine SeqWPR.assign hP V.vListPtr _ (by rw [← c2]; evc) le_rfl
    (by simp only [Expr.size, add, r]; omega) ?_
  refine SeqWPR.assign hP V.auxPar _ (by rw [← c3]; evc) le_rfl
    (by simp only [Expr.size, add, r]; omega) ?_
  refine SeqWPR.assign hP V.minPtr _ (by rw [c4]; evc) le_rfl
    (by simp only [Expr.size, add, mul, r, k]; omega) ?_
  refine SeqWPR.assign hP V.thDst _ (by rw [← c5]; evc) le_rfl
    (by simp only [Expr.size, add, mul, r]; omega) ?_
  refine SeqWPR.assign hP V.sPtr _ (by rw [← s18]; evc) le_rfl
    (by simp only [Expr.size, add, mul, r, k]; omega) ?_
  refine SeqWPR.assign hP V.eu _ (by rw [← s19]; evc) le_rfl
    (by simp only [Expr.size, add, mul, r, k]; omega) ?_
  refine SeqWPR.assign hP V.ev _ (by rw [← s20]; evc) le_rfl
    (by simp only [Expr.size, add, r]; omega) ?_
  refine SeqWPR.assign hP V.dPtr _ (by rw [← s21]; evc) le_rfl
    (by simp only [Expr.size, add, r]; omega) ?_
  refine SeqWPR.assign hP V.tmpPtr _ (by rw [← s22]; evc) le_rfl
    (by simp only [Expr.size, add, mul, r]; omega) ?_
  refine SeqWPR.assign hP V.arrPtr _ (by rw [← s23]; evc) le_rfl
    (by simp only [Expr.size, add, r]; omega) ?_
  refine SeqWPR.assign hP V.scratchPtr _ (by rw [← s24]; evc) le_rfl
    (by simp only [Expr.size, add, r]; omega) ?_
  refine SeqWPR.assign hP V.thBase _ (by rw [← s25]; evc) le_rfl
    (by simp only [Expr.size, add, r]; omega) ?_
  refine SeqWPR.mono hP (hnext _ (fun j hj => ?_) (fun j hj => ?_)) ?_
  · repeat rw [Function.update_of_ne (by omega)]
  · interval_cases j <;>
      (repeat (first | rw [Function.update_of_ne (by omega)] |
        rw [Function.update_apply, if_pos (by omega)])) <;>
      simp only [segCVals, List.getD_cons_zero, List.getD_cons_succ]
  · simp only [Expr.size, ld, add, mul, r, k]
    omega

/-- The cost of the order phase does not drop when `nOrig` grows. -/
lemma orderPhaseCost_mono (V : InitVals) {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) (m₁ m₂ : ℕ → ℕ) :
    orderPhaseCost (OrderLayout.ofVals V n₁).args m₁ ≤
      orderPhaseCost (OrderLayout.ofVals V n₂).args m₂ := by
  simp only [orderPhaseCost, OrderLayout.args, List.getD_cons_succ, List.getD_cons_zero,
    OrderLayout.ofVals]
  omega

/-- The cost of the third segment. -/
def segCCost (V : InitVals) : ℕ :=
  orderPhaseCost (OrderLayout.ofVals V V.tM).args (fun _ => 0) + 800

set_option maxHeartbeats 4000000 in
theorem segC_wp {w h : ℕ} {p : Program} {I : InitIdx} {P : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop}
    (hP : UpClosed P) {rest : List DStep} {regs mem : ℕ → ℕ} {B : ℕ}
    {G₀ T₀ : MGraph} {vList eList : List ℕ} {bRoot bStore bOrder bT bTH cnt nOrig : ℕ}
    (V : InitVals)
    (hord : MeetsContract w p I.order
      (orderPhaseContract w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH))
    (I₀ : OrderPhaseIn w h G₀ T₀ vList eList (OrderLayout.ofVals V nOrig) mem)
    (r7 : regs rVc = V.vCap) (r8 : regs rEc = V.eCap)
    (hA : ∀ j < 19, regs (10 + j) = (segAVals V).getD j 0)
    (hBv : ∀ j < 20, regs (29 + j) = (segBVals V cnt).getD j 0) (a49 : regs 49 = V.rtOut)
    (hO : mem V.outHdr = nOrig) (hH : V.lsstHeap ≤ V.H) (hB : segCCost V ≤ B)
    (hnext : ∀ regs' v mem',
      (orderPhaseContract w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH).post
        (OrderLayout.ofVals V nOrig).args mem v mem' →
      (∀ j < 50, regs' j = regs j) → (∀ j < 14, regs' (50 + j) = (segCVals V nOrig).getD j 0) →
      regs' 64 = v →
      SeqWPR w p 10 P 55 rest regs' mem' (B - segCCost V)) :
    SeqWPR w p 10 P 40 (segC I ++ rest) regs mem B := by
  have a10 : regs 10 = V.n0 := hA 0 (by omega)
  have a11 : regs 11 = V.m0 := hA 1 (by omega)
  have a12 : regs 12 = V.tM := hA 2 (by omega)
  have a15 : regs 15 = auxLogCap V.n0 := hA 5 (by omega)
  have a20 : regs 20 = V.gPtr := hA 10 (by omega)
  have a21 : regs 21 = V.tPtr := hA 11 (by omega)
  have a25 : regs 25 = V.auxPtr := hA 15 (by omega)
  have b31 : regs 31 = V.K_w := hBv 2 (by omega)
  have b32 : regs 32 = V.K := hBv 3 (by omega)
  have b33 : regs 33 = V.qNat := hBv 4 (by omega)
  have b43 : regs 43 = V.outHdr := hBv 14 (by omega)
  have b45 : regs 45 = V.tOrig := hBv 16 (by omega)
  have b46 : regs 46 = V.tTail := hBv 17 (by omega)
  have b47 : regs 47 = V.tHead := hBv 18 (by omega)
  have hW : V.thBase + 8 * V.n0 < 2 ^ w := I₀.l19
  have hw16 : 16 ≤ 2 ^ w := I₀.hw16
  have hnO : nOrig ≤ V.tM := I₀.hnO
  have hall : ∀ x ∈ (OrderLayout.ofVals V nOrig).args, x < 2 ^ w := fun x hx => by
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    have := I₀.args_lt j
    rwa [List.getD_eq_getElem _ _ hj] at this
  have hc := orderPhaseCost_mono V hnO mem (fun _ => 0)
  have hsz : argsSize orderArgs ≤ 150 := by
    simp only [orderArgs, eTOrigId, eDyn, argsSize, Expr.size, add, mul, r, k]
    omega
  unfold segCCost at hB
  rw [segC_split, List.append_assoc]
  refine segCMid_wp hP V r7 a10 a11 a12 a15 a25 b32 b43 a49 hO hH hW hw16 (by omega) ?_
  intro regs₂ hr2a hr2b
  have d : ∀ j < 50, regs₂ j = regs j := hr2a
  have d50 : regs₂ 50 = nOrig := hr2b 0 (by omega)
  have d51 : regs₂ 51 = V.vIdx := hr2b 1 (by omega)
  have d52 : regs₂ 52 = V.vListPtr := hr2b 2 (by omega)
  have d53 : regs₂ 53 = V.auxPar := hr2b 3 (by omega)
  have d54 : regs₂ 54 = V.minPtr := hr2b 4 (by omega)
  have d55 : regs₂ 55 = V.thDst := hr2b 5 (by omega)
  have d56 : regs₂ 56 = V.sPtr := hr2b 6 (by omega)
  have d57 : regs₂ 57 = V.eu := hr2b 7 (by omega)
  have d58 : regs₂ 58 = V.ev := hr2b 8 (by omega)
  have d59 : regs₂ 59 = V.dPtr := hr2b 9 (by omega)
  have d60 : regs₂ 60 = V.tmpPtr := hr2b 10 (by omega)
  have d61 : regs₂ 61 = V.arrPtr := hr2b 11 (by omega)
  have d62 : regs₂ 62 = V.scratchPtr := hr2b 12 (by omega)
  have d63 : regs₂ 63 = V.thBase := hr2b 13 (by omega)
  have q7 := (d 7 (by omega)).trans r7
  have q8 := (d 8 (by omega)).trans r8
  have q10 := (d 10 (by omega)).trans a10
  have q11 := (d 11 (by omega)).trans a11
  have q12 := (d 12 (by omega)).trans a12
  have q15 := (d 15 (by omega)).trans a15
  have q20 := (d 20 (by omega)).trans a20
  have q21 := (d 21 (by omega)).trans a21
  have q31 := (d 31 (by omega)).trans b31
  have q32 := (d 32 (by omega)).trans b32
  have q33 := (d 33 (by omega)).trans b33
  have q45 := (d 45 (by omega)).trans b45
  have q46 := (d 46 (by omega)).trans b46
  have q47 := (d 47 (by omega)).trans b47
  have q49 := (d 49 (by omega)).trans a49
  have hgo := hall
  simp only [OrderLayout.args, OrderLayout.ofVals, OrderLayout.qOrd, InitVals.Kq, dgEListBase,
    dgETailSlotBase, dgEHeadSlotBase, dgIntToExtBase, tPiBase, tOrigIdBase, tDgTPtr,
    dynGraphSize, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hgo
  refine SeqWPR.call hP (orderPhaseContract w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH)
    (OrderLayout.ofVals V nOrig).args
    (orderPhaseCost (OrderLayout.ofVals V V.tM).args (fun _ => 0) + 200) hord
    (by
      simp only [OrderLayout.args, OrderLayout.ofVals, OrderLayout.qOrd, InitVals.Kq,
        dgEListBase, dgETailSlotBase, dgEHeadSlotBase, dgIntToExtBase, tPiBase, tOrigIdBase,
        tDgTPtr, dynGraphSize]
      show evalArgs _ _ _ = _
      dsimp only [orderArgs, eTOrigId, eDyn, rN, rTM, rTT, rTH, rH, rS, rAP, rLog, rM, rGP, rVc,
        rEc, rVI, rEu, rEv, rQ, rKw, rDP, rK, rTmp, rArr, rScr, rMin, rTP, rVL, rTO, rNO, rThB,
        rThD]
      eval_expr
      all_goals omega)
    hall (orderPhase_seqPre I₀ bRoot bStore bOrder bT bTH)
    (by show orderPhaseCost _ mem + _ + 2 ≤ _; omega)
    (by omega) ?_
  intro v mem' hpost
  refine SeqWPR.mono hP (hnext _ v mem' hpost (fun j hj => ?_) (fun j hj => ?_) ?_) ?_
  · rw [Function.update_of_ne (by omega)]; exact d j hj
  · rw [Function.update_of_ne (by omega)]; exact hr2b j hj
  · simp
  · unfold segCCost
    omega

end

end MinCostFlow.LSF.Program
