module

public import MinCostFlow.LSF.Program.InitSegA
public import MinCostFlow.LSF.Program.InitTreePhasePre
public import MinCostFlow.LSF.Program.PrepStage
public import MinCostFlow.LSF.Program.WidthsProc

/-!
# The init driver, steps `19 … 39`

The second segment copies `G₀` into the state and builds the vertex list (`prepStage`), computes
the widths `K_w` and `K` (`widths`), computes the places of the tree arena, and runs the tree
phase. `segB_wp` says: if the rest of the steps runs from every outcome of the three calls, with
registers that hold the places, then the whole sequence runs.

The cost of the tree phase depends on the edge list that `prepStage` writes, through the number of
copies. So `segB_wp` takes a bound `Bt` on it for every edge list of `G₀`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord
  InitDriver

@[expose] public section

/-- The arguments of the call of `prepStage`. -/
def prepArgsV (V : InitVals) (g0Ptr vCap0 eCap0 kk : ℕ) : List ℕ :=
  [g0Ptr, V.vCap, V.eCap, kk, V.auxPtr, V.gPtr, V.endA, V.n0, V.m0,
    dgEListBase g0Ptr vCap0 eCap0, auxVListBase V.auxPtr V.vCap]

/-- The numbers in registers `29 … 48` after the second segment. Register `49` holds the heap
pointer that the tree phase returns. -/
def segBVals (V : InitVals) (cnt : ℕ) : List ℕ :=
  [cnt, 0, V.K_w, V.K, V.qNat, V.mult, V.copyTail, V.copyHead, V.copyLen, V.copyWt, V.copyOrig,
    V.copySub, V.outOrig, V.outBridge, V.outHdr, V.usedBridge, V.tOrig, V.tTail, V.tHead,
    V.lsstHeap]

/-- The cost of the tree phase for the vertex list `vList` and the edge list `eList`. -/
noncomputable def treeCostOf (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (w h : ℕ) (G₀ : MGraph)
    (v ℓ₀ : ℕ → ℝ) (P_fp : ℕ) (V : InitVals) (lenArr wtArr : ℕ) (vList eList : List ℕ) : ℕ :=
  (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList).cost
    (treeArgsV V lenArr wtArr) (fun _ => 0)

/-- The cost of the second segment, for a bound `Bt` on the cost of the tree phase. -/
def segBCost (n0 m0 Bt : ℕ) : ℕ :=
  20 * Nat.log 2 n0 + 20 * Nat.log 2 (n0 + 1) + 640 * n0 + 920 * m0 +
    20 * Nat.log 2 (4 * m0 + 2) + 20 * Nat.log 2 (m0 + 1) + Bt + 1300

/-- A number in base `2 ^ h` keeps its value where the memory does not change. -/
lemma num_congr {mem mem' : ℕ → ℕ} {a h L P : ℕ} {x : ℝ}
    (hv : Num.Valid mem a h L ∧ Num.fixVal mem a h L P = x ∧ 0 < x)
    (heq : ∀ i < L, mem' (a + i) = mem (a + i)) :
    Num.Valid mem' a h L ∧ Num.fixVal mem' a h L P = x ∧ 0 < x := by
  refine ⟨numValid_congr (fun i hi => (heq i hi).symm) hv.1, ?_, hv.2.2⟩
  rw [← hv.2.1]
  simp only [Num.fixVal, intVal_congr_range heq]

lemma aux_ge (a vCap n x : ℕ) :
    a ≤ auxVIdxBase a + x ∧ a ≤ auxIsOrigVertBase a vCap n + x ∧ a ≤ auxVisBBase a vCap n + x ∧
      a ≤ auxVisABase a vCap n + x := by
  simp only [auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase, auxIsOrigVertBase,
    auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
    auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The places that the second segment uses, in order. -/
lemma InitVals.segB_le (V : InitVals) :
    V.b + lsfHdrSize = V.gPtr ∧ V.gPtr + dynGraphSize V.vCap V.eCap ≤ V.auxPtr ∧
    V.vIdx = V.auxPtr + auxHdrSize ∧ V.vIdx + V.vCap = V.vListPtr ∧
    V.vListPtr + V.n0 ≤ V.auxPtr + auxSize V.vCap V.n0 ∧
    V.auxPtr + auxSize V.vCap V.n0 ≤ V.endA ∧ V.endA + 6 ≤ V.lsstHeap := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, -⟩ :=
    V.scratch_order
  have hmin := V.minPtr_eq
  refine ⟨e15, ?_, rfl, e2, ?_, ?_, ?_⟩ <;> omega

/-- Steps `21 … 38`: the two widths and the places of the tree arena. -/
def segBMid : List DStep :=
  [ .assign (ld (add (r rEnd) (k 3))),
    .assign (ld (add (r rEnd) (k 5))),
    .assign (add (r rEnd) (k 6)),
    .assign (add (r rQ) (mul (r rM) (add (r rKw) (k 6)))),
    .assign (add (add (add (r rMult) (r rM)) (mul (k 5) (r rKw))) (mul (k 2) (add (r rKw) (k 6)))),
    .assign (add (r rCT) (mul (k 2) (r rM))),
    .assign (add (r rCH) (mul (k 2) (r rM))),
    .assign (add (r rCL) (mul (mul (k 2) (r rM)) (r rLin))),
    .assign (add (r rCW) (mul (mul (k 2) (r rM)) (r rLin))),
    .assign (add (r rCO) (mul (k 2) (r rM))),
    .assign (add (r rCS) (mul (k 2) (r rM))),
    .assign (add (r rOO) (r rN)),
    .assign (add (r rOB) (mul (k 2) (r rN))),
    .assign (add (r rOH) (k 2)),
    .assign (add (r rUB) (add (mul (k 2) (r rM)) (r rN))),
    .assign (add (r rTO) (r rN)),
    .assign (add (r rTT) (r rN)),
    .assign (add (r rTH) (r rN))]

lemma segB_split (I : InitIdx) : segB I = .call I.prep [r rG0, r rVc, r rEc, r rKn, r rAux,
      r rGP, r rEnd, r rN, r rM,
      add (add (add (r rG0) (k 4)) (mul (k 7) (ld (add (r rG0) (k dgVCapOff)))))
        (ld (add (r rG0) (k dgECapOff))),
      add (add (r rAux) (k auxHdrSize)) (r rVc)] ::
    .call I.widths [r rM, r rLin, add (r rEnd) (k 3)] :: (segBMid ++ [.call I.tree treeArgs]) :=
  rfl

/-- The numbers in registers `31 … 48` after `segBMid`. -/
def segBMidVals (V : InitVals) : List ℕ := (segBVals V 0).drop 2

macro "evm" : tactic => `(tactic| (
  show Expr.eval _ _ _ = _
  try simp only [Nat.reduceAdd, Nat.zero_add]
  dsimp only [rEnd, rQ, rM, rKw, rMult, rCT, rCH, rCL, rLin, rCW, rCO, rCS, rOO, rN, rOB, rOH,
    rUB, rTO, rTT, rTH]
  eval_expr
  all_goals omega))

set_option maxHeartbeats 2000000 in
theorem segBMid_wp {w : ℕ} {p : Program} {P : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop}
    (hP : UpClosed P) {rest : List DStep} {regs mem : ℕ → ℕ} {B : ℕ} (V : InitVals)
    (a10 : regs 10 = V.n0) (a11 : regs 11 = V.m0) (r3 : regs 3 = V.L_in)
    (a28 : regs 28 = V.endA) (hK1 : mem (V.endA + 3) = V.K_w) (hK3 : mem (V.endA + 5) = V.K)
    (hW : V.lsstHeap < 2 ^ w) (hB : 400 ≤ B)
    (hnext : ∀ regs', (∀ j < 31, regs' j = regs j) →
      (∀ j < 18, regs' (31 + j) = (segBMidVals V).getD j 0) →
      SeqWPR w p 10 P 39 rest regs' mem (B - 400)) :
    SeqWPR w p 10 P 21 (segBMid ++ rest) regs mem B := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, -⟩ :=
    V.scratch_order
  simp only [InitVals.Kq] at s2 s3
  simp only [segBMid, List.cons_append, List.nil_append]
  refine SeqWPR.assign hP V.K_w _ (by evm) le_rfl
    (by simp only [Expr.size, ld, add, mul, r, k]; omega) ?_
  refine SeqWPR.assign hP V.K _ (by evm) le_rfl
    (by simp only [Expr.size, ld, add, mul, r, k]; omega) ?_
  refine SeqWPR.assign hP V.qNat _ (by rw [← s1]; evm) le_rfl
    (by simp only [Expr.size, ld, add, mul, r, k]; omega) ?_
  refine SeqWPR.assign hP V.mult _ (by rw [← s2]; evm) le_rfl
    (by simp only [Expr.size, ld, add, mul, r, k]; omega) ?_
  refine SeqWPR.assign hP V.copyTail _ (by rw [← s3]; evm) le_rfl
    (by simp only [Expr.size, ld, add, mul, r, k]; omega) ?_
  refine SeqWPR.assign hP V.copyHead _ (by rw [← s4]; evm) le_rfl
    (by simp only [Expr.size, ld, add, mul, r, k]; omega) ?_
  refine SeqWPR.assign hP V.copyLen _ (by rw [← s5]; evm) le_rfl
    (by simp only [Expr.size, ld, add, mul, r, k]; omega) ?_
  refine SeqWPR.assign hP V.copyWt _ (by rw [← s6]; evm) le_rfl
    (by simp only [Expr.size, ld, add, mul, r, k]; omega) ?_
  refine SeqWPR.assign hP V.copyOrig _ (by rw [← s7]; evm) le_rfl
    (by simp only [Expr.size, ld, add, mul, r, k]; omega) ?_
  refine SeqWPR.assign hP V.copySub _ (by rw [← s8]; evm) le_rfl
    (by simp only [Expr.size, ld, add, mul, r, k]; omega) ?_
  refine SeqWPR.assign hP V.outOrig _ (by rw [← s9]; evm) le_rfl
    (by simp only [Expr.size, ld, add, mul, r, k]; omega) ?_
  refine SeqWPR.assign hP V.outBridge _ (by rw [← s10]; evm) le_rfl
    (by simp only [Expr.size, ld, add, mul, r, k]; omega) ?_
  refine SeqWPR.assign hP V.outHdr _ (by rw [← s11]; evm) le_rfl
    (by simp only [Expr.size, ld, add, mul, r, k]; omega) ?_
  refine SeqWPR.assign hP V.usedBridge _ (by rw [← s12]; evm) le_rfl
    (by simp only [Expr.size, ld, add, mul, r, k]; omega) ?_
  refine SeqWPR.assign hP V.tOrig _ (by rw [← s13]; evm) le_rfl
    (by simp only [Expr.size, ld, add, mul, r, k]; omega) ?_
  refine SeqWPR.assign hP V.tTail _ (by rw [← s14]; evm) le_rfl
    (by simp only [Expr.size, ld, add, mul, r, k]; omega) ?_
  refine SeqWPR.assign hP V.tHead _ (by rw [← s15]; evm) le_rfl
    (by simp only [Expr.size, ld, add, mul, r, k]; omega) ?_
  refine SeqWPR.assign hP V.lsstHeap _ (by rw [← s16]; evm) le_rfl
    (by simp only [Expr.size, ld, add, mul, r, k]; omega) ?_
  refine SeqWPR.mono hP (hnext _ (fun j hj => ?_) (fun j hj => ?_)) ?_
  · repeat rw [Function.update_of_ne (by omega)]
  · interval_cases j <;>
      (repeat (first | rw [Function.update_of_ne (by omega)] |
        rw [Function.update_apply, if_pos (by omega)])) <;>
      simp only [segBMidVals, segBVals, List.drop_succ_cons, List.drop_zero,
        List.getD_cons_zero, List.getD_cons_succ]
  · simp only [Expr.size, ld, add, mul, r, k]
    omega

/-- The arguments of the tree phase are words. -/
lemma treeArgsV_lt {w : ℕ} (V : InitVals) {lenArr wtArr : ℕ} (hW : V.lsstHeap < 2 ^ w)
    (hl : lenArr < 2 ^ w) (hw : wtArr < 2 ^ w) (hL : V.L_in < 2 ^ w) : ∀ x ∈ treeArgsV V lenArr wtArr, x < 2 ^ w := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := V.segB_le
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, -⟩ :=
    V.scratch_order
  have hdgs : dynGraphSize V.vCap V.eCap = 4 + 7 * V.vCap + 9 * V.eCap := rfl
  simp only [treeArgsV, treeCopyArgsV, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, dgEListBase]
  rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega

/-- The facts about the input that the tree phase needs, bundled so that they stay out of the
way of `omega`. -/
structure SegBIn (w h : ℕ) (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (G₀ : MGraph)
    (v ℓ₀ : ℕ → ℝ) (P_fp : ℕ) (V : InitVals) (lenArr wtArr kk : ℕ) (mem : ℕ → ℕ) : Prop where
  hh : 1 ≤ h
  hhw : 3 * h + 2 ≤ w
  hLin : 1 ≤ V.L_in
  h2L : 2 ≤ h * V.L_in
  hPd : h ∣ P_fp
  hlenB : ∀ e ∈ G₀.E, lenArr + e * V.L_in + V.L_in ≤ V.b
  hwtB : ∀ e ∈ G₀.E, wtArr + e * V.L_in + V.L_in ≤ V.b
  hlv : ∀ e ∈ G₀.E, Num.Valid mem (lenArr + e * V.L_in) h V.L_in ∧
    Num.fixVal mem (lenArr + e * V.L_in) h V.L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e
  hwv : ∀ e ∈ G₀.E, Num.Valid mem (wtArr + e * V.L_in) h V.L_in ∧
    Num.fixVal mem (wtArr + e * V.L_in) h V.L_in P_fp = v e ∧ 0 < v e
  hsp : V.lsstHeap + V.m0 * multQNatStepSpace V.K_w < 2 ^ w
  hec : V.eCap + (2 * V.m0 + V.n0) + V.eCap < 2 ^ w
  hc : 1 ≤ c_AN
  hl1 : 16 * (2 * V.m0) + 6 < 2 ^ w
  hl3 : c_AN < 2 ^ w
  hl4 : h < 2 ^ w
  hl5 : kWidthOf (2 * V.m0) V.L_in < 2 ^ w
  hl6 : Nat.log 2 (16 * (2 * V.m0) + 6) + kWidthOf (2 * V.m0) V.L_in * h + 3 < 2 ^ w
  hl7 : w'Max c_AN 0 (2 * V.m0) V.L_in h < 2 ^ w
  hspL : V.lsstHeap + lsstSpace Q_AN K_AN V.n0 (2 * V.m0)
    (lsstLSimMin c_AN 0 (2 * V.m0) V.L_in h) h < 2 ^ w
  hk : 1 ≤ kk
  hkw : 3 * (4 * kk * (hldDepthBound V.n0 + 1)) < 2 ^ w
  hwK : widthK V.m0 V.L_in < 2 ^ w
  hlenw : lenArr < 2 ^ w
  hwtw : wtArr < 2 ^ w

set_option maxHeartbeats 4000000 in
theorem segB_wp {w h : ℕ} {p : Program} {I : InitIdx} {P : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop}
    (hP : UpClosed P) {rest : List DStep} {regs mem : ℕ → ℕ} {B : ℕ}
    {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ : MGraph} {v ℓ₀ : ℕ → ℝ} {P_fp : ℕ}
    {g0Ptr vCap0 eCap0 lenArr wtArr kk Bt : ℕ} (V : InitVals)
    (hprep : MeetsContract w p I.prep (prepStageContract w G₀))
    (hwid : MeetsContract w p I.widths (widthsContract w))
    (htree : ∀ vList eList, MeetsContract w p I.tree
      (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList))
    (r0 : regs rG0 = g0Ptr) (r1 : regs rLen = lenArr) (r2 : regs rWt = wtArr)
    (r3 : regs rLin = V.L_in) (r5 : regs rKn = kk) (r7 : regs rVc = V.vCap)
    (r8 : regs rEc = V.eCap) (hA : ∀ j < 19, regs (10 + j) = (segAVals V).getD j 0)
    (S : SegBIn w h Q_AN c_AN K_AN G₀ v ℓ₀ P_fp V lenArr wtArr kk mem)
    (hdg0 : DynGraphAt mem g0Ptr vCap0 eCap0 G₀) (hg0 : g0Ptr + dynGraphSize vCap0 eCap0 ≤ V.b)
    (hvc : vCap0 ≤ V.vCap) (hec0 : eCap0 ≤ V.eCap) (hzb : ZeroFrom mem V.b)
    (hKw : V.K_w = kWidthOf V.m0 V.L_in) (hKK : V.K = widthK V.m0 V.L_in)
    (hm : G₀.E.card = V.m0) (hn : G₀.n = V.n0) (hn1 : 1 ≤ V.n0)
    (hBt : ∀ vList eList, eList.length = V.m0 → eList.Nodup → (∀ e, e ∈ eList ↔ e ∈ G₀.E) →
      treeCostOf Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp V lenArr wtArr vList eList ≤ Bt)
    (hB : segBCost V.n0 V.m0 Bt ≤ B)
    (hnext : ∀ regs' cnt mem₁ mem₂ vList eList H mem₃,
      (prepStageContract w G₀).post (prepArgsV V g0Ptr vCap0 eCap0 kk) mem cnt mem₁ →
      (widthsContract w).post [V.m0, V.L_in, V.endA + 3] mem₁ 0 mem₂ →
      vList.length = V.n0 → ListAt mem₂ V.vListPtr vList →
      eList.length = V.m0 → eList.Nodup → (∀ e, e ∈ eList ↔ e ∈ G₀.E) →
      ListAt mem₂ (dgEListBase V.gPtr V.vCap V.eCap) eList →
      (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList).post
        (treeArgsV V lenArr wtArr) mem₂ H mem₃ →
      (∀ j < 10, regs' j = regs j) → (∀ j < 19, regs' (10 + j) = (segAVals V).getD j 0) →
      (∀ j < 20, regs' (29 + j) = (segBVals V cnt).getD j 0) → regs' 49 = H →
      SeqWPR w p 10 P 40 rest regs' mem₃ (B - segBCost V.n0 V.m0 Bt)) :
    SeqWPR w p 10 P 19 (segB I ++ rest) regs mem B := by
  have a10 : regs 10 = V.n0 := hA 0 (by omega)
  have a11 : regs 11 = V.m0 := hA 1 (by omega)
  have a20 : regs 20 = V.gPtr := hA 10 (by omega)
  have a25 : regs 25 = V.auxPtr := hA 15 (by omega)
  have a28 : regs 28 = V.endA := hA 18 (by omega)
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := V.segB_le
  have hdgs : dynGraphSize V.vCap V.eCap = 4 + 7 * V.vCap + 9 * V.eCap := rfl
  have hdgs0 : dynGraphSize vCap0 eCap0 = 4 + 7 * vCap0 + 9 * eCap0 := rfl
  have hW : V.lsstHeap < 2 ^ w := by have := S.hspL; omega
  have hw32 : 32 ≤ 2 ^ w := by
    have : 5 ≤ w := by have := S.hhw; have := S.hh; omega
    exact le_trans (by decide : 32 ≤ 2 ^ 5) (Nat.pow_le_pow_right (by norm_num) this)
  have hw16 : 16 ≤ 2 ^ w := by omega
  have hkk : kk < 2 ^ w := by
    have := S.hkw
    have : 4 * kk ≤ 4 * kk * (hldDepthBound V.n0 + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hvc0 : mem (g0Ptr + dgVCapOff) = vCap0 := hdg0.2.2.2.1
  have hec0' : mem (g0Ptr + dgECapOff) = eCap0 := hdg0.2.2.2.2.1
  have hne : G₀.V.Nonempty := by
    rw [← Finset.card_pos]; change 0 < G₀.n; omega
  have hmw : V.m0 < 2 ^ w := by have := S.hec; omega
  have hm16 : 16 * (2 * V.m0) + 6 < 2 ^ w := S.hl1
  have hLw : V.L_in < 2 ^ w := by have := S.hl5; unfold kWidthOf at this; omega
  have hlsf : lsfHdrSize = 24 := rfl
  have hah : auxHdrSize = 20 := rfl
  unfold segBCost at hB
  rw [segB_split]
  -- 1. the copy of `G₀`
  refine SeqWPR.call hP (prepStageContract w G₀) (prepArgsV V g0Ptr vCap0 eCap0 kk)
    (20 * Nat.log 2 V.n0 + 20 * Nat.log 2 (V.n0 + 1) + 640 * V.n0 + 920 * V.m0 + 700) hprep
    (by
      show evalArgs _ _ _ = some [g0Ptr, V.vCap, V.eCap, kk, V.auxPtr, V.gPtr, V.endA, V.n0,
        V.m0, g0Ptr + 4 + 7 * vCap0 + eCap0, V.auxPtr + auxHdrSize + V.vCap]
      dsimp only [rG0, rVc, rEc, rKn, rAux, rGP, rEnd, rN, rM]
      eval_expr
      all_goals (try simp only [dgVCapOff, dgECapOff] at *)
      all_goals omega)
    (by
      simp only [prepArgsV, List.mem_cons, List.not_mem_nil, or_false]
      simp only [dgEListBase, auxVListBase, auxVIdxBase]
      rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega)
    ⟨g0Ptr, V.vCap, V.eCap, kk, V.auxPtr, V.gPtr, V.endA, vCap0, eCap0,
      by rw [hn, hm]; rfl, hw16, hne, S.hk, hdg0, hvc, hec0, by omega, l2, by rw [hn]; omega,
      by omega, by rw [hn]; exact S.hkw,
      fun i _ => hzb _ (by omega),
      fun x _ => hzb _ (by have := (aux_ge V.auxPtr V.vCap G₀.n x).1; omega),
      fun x _ => hzb _ (by have := (aux_ge V.auxPtr V.vCap G₀.n x).2.1; omega),
      fun x _ => ⟨hzb _ (by have := (aux_ge V.auxPtr V.vCap G₀.n x).2.2.2; omega),
        hzb _ (by have := (aux_ge V.auxPtr V.vCap G₀.n x).2.2.1; omega)⟩⟩
    (by simp only [prepStageContract, prepArgsV, List.getD_cons_succ, List.getD_cons_zero,
      argsSize, Expr.size, add, mul, ld, r, k]; omega)
    (by omega) ?_
  intro cnt mem₁ hpost₁
  have hpost₁' := hpost₁
  obtain ⟨g0', vc', ec', k', ax', gp', po', vc0', ec0', vList, repList, heq, -, -, -,
    hdg₁, hvLen, hvNd, hvV, hvL, hvI, -, -, -, -, -, -, -, -, -, -, -, hfr₁⟩ := hpost₁
  simp only [prepArgsV, List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, -, -, -⟩ := heq
  rw [hn] at hvLen
  -- 2. the widths
  refine SeqWPR.call hP (widthsContract w) [V.m0, V.L_in, V.endA + 3]
    (20 * Nat.log 2 (4 * V.m0 + 2) + 20 * Nat.log 2 (V.m0 + 1) + 110) hwid
    (by
      show evalArgs _ _ _ = _
      dsimp only [rLin, rEnd, rM]
      eval_expr
      all_goals (try rw [Function.update_of_ne (by omega)])
      all_goals omega)
    (by
      have := S.hLin; have := S.h2L
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl) <;> omega)
    ⟨V.m0, V.L_in, V.endA + 3, rfl, hw16, by omega, by omega, S.hwK⟩
    (by simp only [widthsContract, List.getD_cons_succ, List.getD_cons_zero, argsSize, Expr.size,
      add, r, k]; omega)
    (by omega) ?_
  rintro z mem₂ hpost₂
  have hpost₂' := hpost₂
  obtain ⟨m', L', o', heq₂, rfl, hK1, hK2, hK3, hfr₂⟩ := hpost₂
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl⟩ := heq₂
  have hK1' : mem₂ (V.endA + 3) = V.K_w := hK1.trans hKw.symm
  have hK3' : mem₂ (V.endA + 5) = V.K := by rw [hKK]; exact hK3
  -- the facts on `mem₂` that the tree phase needs
  have hdg₂ : DynGraphAt mem₂ V.gPtr V.vCap V.eCap G₀ :=
    hdg₁.of_agree fun a _ ha => hfr₂ a (Or.inl (by omega))
  obtain ⟨eList, heLen, heNd, heE, heL, -⟩ := hdg₂.2.2.2.2.2.2.2.2.2.2.2.2.1
  have heLen' : eList.length = V.m0 := heLen.trans hm
  have hvL₂ : ListAt mem₂ V.vListPtr vList := fun i hi => by
    rw [hfr₂ _ (Or.inl (by omega))]; exact hvL i hi
  have hvI₂ : ∀ i (hi : i < vList.length), mem₂ (V.vIdx + vList[i]) = i + 1 := fun i hi => by
    have := hdg₁.2.1 _ ((hvV _).mp (List.getElem_mem hi))
    rw [hfr₂ _ (Or.inl (by omega))]; exact hvI i hi
  have hlv₂ : ∀ e ∈ G₀.E, Num.Valid mem₂ (lenArr + e * V.L_in) h V.L_in ∧
      Num.fixVal mem₂ (lenArr + e * V.L_in) h V.L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e :=
    fun e he => num_congr (S.hlv e he) fun i hi => by
      have := S.hlenB e he
      rw [hfr₂ _ (Or.inl (by omega)), hfr₁ _ (Or.inl (by omega)) (Or.inl (by omega))
        (Or.inl (by omega))]
  have hwv₂ : ∀ e ∈ G₀.E, Num.Valid mem₂ (wtArr + e * V.L_in) h V.L_in ∧
      Num.fixVal mem₂ (wtArr + e * V.L_in) h V.L_in P_fp = v e ∧ 0 < v e :=
    fun e he => num_congr (S.hwv e he) fun i hi => by
      have := S.hwtB e he
      rw [hfr₂ _ (Or.inl (by omega)), hfr₁ _ (Or.inl (by omega)) (Or.inl (by omega))
        (Or.inl (by omega))]
  have hz₂ : ZeroFrom mem₂ V.lsstHeap := fun a ha => by
    rw [hfr₂ a (Or.inr (by omega)), hfr₁ a (Or.inr (by omega)) (Or.inr (by rw [hn]; omega))
      (Or.inr (by omega))]
    exact hzb a (by omega)
  have htp := treePhase_pre_of (Q_AN := Q_AN) (c_AN := c_AN) (K_AN := K_AN) V S.hh S.hhw S.hLin
    S.h2L S.hPd hdg0.1 hm hn hn1 hKw hdg₂ heLen' heNd heE heL hvLen hvNd hvV hvI₂ S.hlenB
    S.hwtB hlv₂ hwv₂ hz₂ S.hsp S.hec S.hc S.hl1 (by omega) S.hl3 S.hl4 S.hl5 S.hl6 S.hl7 S.hspL
  have hlenw : lenArr < 2 ^ w := S.hlenw
  have hwtw : wtArr < 2 ^ w := S.hwtw
  have hTw := treeArgsV_lt V hW hlenw hwtw hLw
  have hcT : (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList).cost
      (treeArgsV V lenArr wtArr) mem₂ ≤ Bt := hBt vList eList heLen' heNd heE
  have hEL : V.gPtr + 4 + 7 * V.vCap + V.eCap < 2 ^ w := by omega
  have hAX : V.auxPtr + auxHdrSize < 2 ^ w := by omega
  clear hfr₁ hfr₂ hlv₂ hwv₂ hz₂ hvI hvI₂ hvL hdg₁ hdg₂ hdg0
  -- 3. the places of the tree arena
  rw [show (segBMid ++ [DStep.call I.tree treeArgs]).append rest =
    segBMid ++ ([DStep.call I.tree treeArgs] ++ rest) from List.append_assoc _ _ _]
  refine segBMid_wp hP V
    (by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact a10)
    (by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact a11)
    (by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact r3)
    (by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact a28)
    hK1' hK3' hW (by omega) ?_
  intro regs₃ hr3a hr3b
  have hlow : ∀ j < 29, regs₃ j = regs j := fun j hj => by
    rw [hr3a j (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have b1 : regs₃ 1 = lenArr := (hlow 1 (by omega)).trans r1
  have b2 : regs₃ 2 = wtArr := (hlow 2 (by omega)).trans r2
  have b3 : regs₃ 3 = V.L_in := (hlow 3 (by omega)).trans r3
  have b7 : regs₃ 7 = V.vCap := (hlow 7 (by omega)).trans r7
  have b8 : regs₃ 8 = V.eCap := (hlow 8 (by omega)).trans r8
  have b10 : regs₃ 10 = V.n0 := (hlow 10 (by omega)).trans a10
  have b11 : regs₃ 11 = V.m0 := (hlow 11 (by omega)).trans a11
  have b20 : regs₃ 20 = V.gPtr := (hlow 20 (by omega)).trans a20
  have b25 : regs₃ 25 = V.auxPtr := (hlow 25 (by omega)).trans a25
  have c31 : regs₃ 31 = V.K_w := hr3b 0 (by omega)
  have c33 : regs₃ 33 = V.qNat := hr3b 2 (by omega)
  have c34 : regs₃ 34 = V.mult := hr3b 3 (by omega)
  have c35 : regs₃ 35 = V.copyTail := hr3b 4 (by omega)
  have c36 : regs₃ 36 = V.copyHead := hr3b 5 (by omega)
  have c37 : regs₃ 37 = V.copyLen := hr3b 6 (by omega)
  have c38 : regs₃ 38 = V.copyWt := hr3b 7 (by omega)
  have c39 : regs₃ 39 = V.copyOrig := hr3b 8 (by omega)
  have c40 : regs₃ 40 = V.copySub := hr3b 9 (by omega)
  have c41 : regs₃ 41 = V.outOrig := hr3b 10 (by omega)
  have c42 : regs₃ 42 = V.outBridge := hr3b 11 (by omega)
  have c43 : regs₃ 43 = V.outHdr := hr3b 12 (by omega)
  have c44 : regs₃ 44 = V.usedBridge := hr3b 13 (by omega)
  have c45 : regs₃ 45 = V.tOrig := hr3b 14 (by omega)
  have c46 : regs₃ 46 = V.tTail := hr3b 15 (by omega)
  have c47 : regs₃ 47 = V.tHead := hr3b 16 (by omega)
  have c48 : regs₃ 48 = V.lsstHeap := hr3b 17 (by omega)
  -- 4. the tree phase
  refine SeqWPR.call hP (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList)
    (treeArgsV V lenArr wtArr) (Bt + 60) (htree vList eList)
    (by
      rw [show treeArgsV V lenArr wtArr = [V.gPtr, V.gPtr + 4 + 7 * V.vCap + V.eCap, lenArr,
        wtArr, V.L_in, V.m0, V.K_w, V.qNat, V.lsstHeap, V.auxPtr + auxHdrSize, V.n0, V.eCap,
        V.mult, V.copyTail, V.copyHead, V.copyLen, V.copyWt, V.copyOrig, V.copySub,
        V.usedBridge, V.outOrig, V.outBridge, V.outHdr, V.tOrig, V.tTail, V.tHead] from rfl]
      show evalArgs _ _ _ = _
      dsimp only [treeArgs, rGP, rVc, rEc, rLen, rWt, rLin, rM, rKw, rQ, rLH, rAux, rN, rMult,
        rCT, rCH, rCL, rCW, rCO, rCS, rUB, rOO, rOB, rOH, rTO, rTT, rTH]
      eval_expr
      all_goals omega)
    hTw htp
    (by simp only [treeArgs, argsSize, Expr.size, add, mul, r, k]; omega)
    (by omega) ?_
  intro H mem₃ hpost₃
  refine SeqWPR.mono hP (hnext _ cnt mem₁ mem₂ vList eList H mem₃ hpost₁' hpost₂' hvLen hvL₂
    heLen' heNd heE heL hpost₃ (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_) ?_) ?_
  · rw [Function.update_of_ne (by omega), hlow j (by omega)]
  · rw [Function.update_of_ne (by omega), hlow (10 + j) (by omega)]; exact hA j hj
  · rw [Function.update_of_ne (by omega)]
    rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with rfl | rfl | hj2
    · show regs₃ 29 = cnt
      rw [hr3a 29 (by omega), Function.update_of_ne (by omega), Function.update_apply,
        if_pos (by omega)]
    · show regs₃ 30 = 0
      rw [hr3a 30 (by omega), Function.update_apply, if_pos (by omega)]
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
      rw [show 29 + (i + 2) = 31 + i by omega, hr3b i (by omega)]
      simp only [segBMidVals, segBVals, List.drop_succ_cons, List.drop_zero,
        List.getD_cons_succ]
  · simp
  · unfold segBCost
    omega

end

end MinCostFlow.LSF.Program
