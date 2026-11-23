module

public import MinCostFlow.LSF.Program.InitSegC

/-!
# The init driver, steps `55 … 62`

The fourth segment loads the threshold `θ` that `prepStage` wrote at `endA + 2`, computes the
block width `LB` of the stretch pass with `wstrLBProc`, computes the scratch places of the
decomposition phase, and runs the decomposition phase. `segD_wp` takes `DecompPhaseIn` at the
places `DecompLayout.ofVals V nOrig θ D k lenArr cnt` and says: if the rest of the steps runs from
every outcome of the decomposition phase, then the whole sequence runs.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord
  InitDriver

@[expose] public section

/-- Steps `57 … 61`: the scratch places of the decomposition phase. -/
def segDMid : List DStep :=
  [ .assign (add (r rThB) (mul (k 8) (r rN))),
    .assign (add (r rDB) (mul (k 12) (r rN))),
    .assign (add (r rHi) (r rM)),
    .assign (add (add (r rInR) (mul (k 3) (r rN))) (r rTM)),
    .assign (add (r rNumS) (mul (k 2) (mul (r rEc) (r rLw))))]

lemma segD_split (I : InitIdx) :
    segD I = [.assign (ld (add (r rEnd) (k 2))), .call I.lb [r rN, r rD, r rLw]] ++
      (segDMid ++ [.call I.decomp decompArgs]) := rfl

/-- The numbers in registers `65 … 71` after `segDMid`. -/
def segDVals (V : InitVals) (θ : ℕ) : List ℕ :=
  [θ, V.LB, V.dBase, V.hiCopy, V.inR, V.numS, V.idPtr]

macro "evd" : tactic => `(tactic| (
  show Expr.eval _ _ _ = _
  try simp only [Nat.reduceAdd, Nat.zero_add]
  dsimp only [rThB, rN, rDB, rHi, rM, rInR, rTM, rNumS, rEc, rLw, rEnd]
  eval_expr
  all_goals omega))

set_option maxHeartbeats 2000000 in
theorem segDMid_wp {w : ℕ} {p : Program} {P : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop}
    (hP : UpClosed P) {rest : List DStep} {regs mem : ℕ → ℕ} {B : ℕ} (V : InitVals)
    (r6 : regs 6 = V.L_w) (r8 : regs 8 = V.eCap) (a10 : regs 10 = V.n0) (a11 : regs 11 = V.m0)
    (a12 : regs 12 = V.tM) (a63 : regs 63 = V.thBase) (hW : V.idPtr < 2 ^ w) (hw16 : 16 ≤ 2 ^ w)
    (hB : 200 ≤ B)
    (hnext : ∀ regs', (∀ j < 67, regs' j = regs j) →
      (∀ j < 5, regs' (67 + j) = (segDVals V 0).getD (j + 2) 0) →
      SeqWPR w p 10 P 62 rest regs' mem (B - 200)) :
    SeqWPR w p 10 P 57 (segDMid ++ rest) regs mem B := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, s26, s27, s28,
    s29, s30, -⟩ := V.scratch_order
  simp only [segDMid, List.cons_append, List.nil_append]
  refine SeqWPR.assign hP V.dBase _ (by rw [← s26]; evd) le_rfl
    (by simp only [Expr.size]; omega) ?_
  refine SeqWPR.assign hP V.hiCopy _ (by rw [← s27]; evd) le_rfl
    (by simp only [Expr.size]; omega) ?_
  refine SeqWPR.assign hP V.inR _ (by rw [← s28]; evd) le_rfl
    (by simp only [Expr.size]; omega) ?_
  refine SeqWPR.assign hP V.numS _ (by rw [← s29]; evd) le_rfl
    (by simp only [Expr.size]; omega) ?_
  refine SeqWPR.assign hP V.idPtr _ (by rw [← s30]; evd) le_rfl
    (by simp only [Expr.size]; omega) ?_
  refine SeqWPR.mono hP (hnext _ (fun j hj => ?_) (fun j hj => ?_)) ?_
  · repeat rw [Function.update_of_ne (by omega)]
  · interval_cases j <;>
      (repeat (first | rw [Function.update_of_ne (by omega)] |
        rw [Function.update_apply, if_pos (by omega)])) <;>
      simp only [segDVals, List.getD_cons_zero, List.getD_cons_succ]
  · simp only [Expr.size]
    omega

/-- The `40` arguments of the decomposition phase, at the places of the driver. -/
lemma decompArgs_ofVals (V : InitVals) (nOrig θ D kk lenArr cnt : ℕ) :
    (DecompLayout.ofVals V nOrig θ D kk lenArr cnt).args =
      [V.n0, V.m0, V.eu, V.ev, V.sPtr + V.n0 + 2 * V.tM + V.n0, V.auxPar, 0, θ, V.dBase, D,
        V.L_w, V.tM, kk, V.L_in, nOrig, auxLogCap V.n0, lenArr, tOrigIdBase V.tPtr V.vCap V.tM,
        V.auxPar + V.n0, tPiBase V.tPtr V.vCap V.tM, V.thBase + 7 * V.n0, V.auxPar + 3 * V.n0,
        V.auxPar + V.n0 + V.n0, dgEListBase V.gPtr V.vCap V.eCap, V.numS,
        V.numS + V.eCap * V.L_w, V.idPtr, V.hiCopy, cnt, V.dBase + 11 * V.n0, V.repPtr, V.vIdx,
        V.inR, V.thDst, V.inR + V.n0, V.inR + V.n0 + V.n0, V.inR + V.n0 + V.n0 + V.tM, V.numSt,
        V.denSt, V.eCap * V.L_w] := rfl

lemma InitVals.repPtr_eq (V : InitVals) : V.repPtr = V.thDst + (V.n0 + 3 * V.vCap) := by
  simp only [InitVals.repPtr, InitVals.thDst, auxQBufBBase, auxQBufABase, auxIsOrigVertBase,
    auxOrigVertBase]
  omega

lemma InitVals.endA_le (V : InitVals) (hH : V.lsstHeap ≤ V.H) : V.endA + 6 ≤ V.thBase := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
    s20, s21, s22, s23, s24, s25, -⟩ := V.scratch_order
  omega

/-- The cost of the decomposition phase depends only on the sizes and on `cnt`. -/
lemma decompPhaseCost_ofVals (V : InitVals) (nOrig θ D kk lenArr cnt : ℕ) (mem : ℕ → ℕ) :
    decompPhaseCost (DecompLayout.ofVals V nOrig θ D kk lenArr cnt).args mem =
      decompPhaseCost (DecompLayout.ofVals V 0 0 D 0 0 cnt).args (fun _ => 0) := rfl

/-- The cost of the fourth segment. -/
def segDCost (V : InitVals) (cnt : ℕ) : ℕ :=
  decompPhaseCost (DecompLayout.ofVals V 0 0 (hldDepthBound V.n0) 0 0 cnt).args (fun _ => 0) +
    20 * Nat.log 2 (V.n0 + 1) + 20 * Nat.log 2 (hldDepthBound V.n0 + 2) + 1000

set_option maxHeartbeats 4000000 in
theorem segD_wp {w h C : ℕ} {p : Program} {I : InitIdx} {P : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop}
    (hP : UpClosed P) {rest : List DStep} {regs mem : ℕ → ℕ} {B : ℕ}
    {T₀ : MGraph} {vList : List ℕ} {bWT bLB bW bCopy bFlag bRoots nOrig θ kk lenArr cnt : ℕ}
    (V : InitVals)
    (hlb : MeetsContract w p I.lb (wstrLBContract w))
    (hdec : MeetsContract w p I.decomp
      (decompPhaseContract w h C bWT bLB bW bCopy bFlag bRoots decompPhaseCost))
    (I₀ : DecompPhaseIn w h C T₀ vList
      (DecompLayout.ofVals V nOrig θ (hldDepthBound V.n0) kk lenArr cnt) mem)
    (hLB : V.LB = wstrLB V.n0 (hldDepthBound V.n0) V.L_w)
    (r1 : regs rLen = lenArr) (r3 : regs rLin = V.L_in) (r5 : regs rKn = kk)
    (r6 : regs rLw = V.L_w) (r7 : regs rVc = V.vCap) (r8 : regs rEc = V.eCap)
    (hA : ∀ j < 19, regs (10 + j) = (segAVals V).getD j 0)
    (hBv : ∀ j < 20, regs (29 + j) = (segBVals V cnt).getD j 0)
    (hCv : ∀ j < 14, regs (50 + j) = (segCVals V nOrig).getD j 0)
    (hθ : mem (V.endA + 2) = θ) (hH : V.lsstHeap ≤ V.H) (hB : segDCost V cnt ≤ B)
    (hnext : ∀ regs' v mem',
      (decompPhaseContract w h C bWT bLB bW bCopy bFlag bRoots decompPhaseCost).post
        (DecompLayout.ofVals V nOrig θ (hldDepthBound V.n0) kk lenArr cnt).args mem v mem' →
      (∀ j < 65, regs' j = regs j) → (∀ j < 7, regs' (65 + j) = (segDVals V θ).getD j 0) →
      regs' 72 = v →
      SeqWPR w p 10 P 63 rest regs' mem' (B - segDCost V cnt)) :
    SeqWPR w p 10 P 55 (segD I ++ rest) regs mem B := by
  have a10 : regs 10 = V.n0 := hA 0 (by omega)
  have a11 : regs 11 = V.m0 := hA 1 (by omega)
  have a12 : regs 12 = V.tM := hA 2 (by omega)
  have a15 : regs 15 = auxLogCap V.n0 := hA 5 (by omega)
  have a16 : regs 16 = hldDepthBound V.n0 := hA 6 (by omega)
  have a20 : regs 20 = V.gPtr := hA 10 (by omega)
  have a21 : regs 21 = V.tPtr := hA 11 (by omega)
  have a26 : regs 26 = V.numSt := hA 16 (by omega)
  have a27 : regs 27 = V.denSt := hA 17 (by omega)
  have a28 : regs 28 = V.endA := hA 18 (by omega)
  have b29 : regs 29 = cnt := hBv 0 (by omega)
  have c50 : regs 50 = nOrig := hCv 0 (by omega)
  have c51 : regs 51 = V.vIdx := hCv 1 (by omega)
  have c53 : regs 53 = V.auxPar := hCv 3 (by omega)
  have c55 : regs 55 = V.thDst := hCv 5 (by omega)
  have c56 : regs 56 = V.sPtr := hCv 6 (by omega)
  have c57 : regs 57 = V.eu := hCv 7 (by omega)
  have c58 : regs 58 = V.ev := hCv 8 (by omega)
  have c63 : regs 63 = V.thBase := hCv 13 (by omega)
  have hgd := I₀.args_lt
  have hall : ∀ x ∈ (DecompLayout.ofVals V nOrig θ (hldDepthBound V.n0) kk lenArr cnt).args,
      x < 2 ^ w := fun x hx => by
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    have := hgd j
    rwa [List.getD_eq_getElem _ _ hj] at this
  have hw16 : 16 ≤ 2 ^ w := I₀.hw16
  have hLBw : wstrLB V.n0 (hldDepthBound V.n0) V.L_w < 2 ^ w := I₀.hLB
  have hDw : 2 * (hldDepthBound V.n0 + 1) < 2 ^ w := I₀.hDw
  have hθw : 3 * θ < 2 ^ w := I₀.hθw
  have hgo := hall
  rw [decompArgs_ofVals] at hgo
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hgo
  obtain ⟨g0, g1, g2, g3, g4, g5, -, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18,
    g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37,
    g38, g39⟩ := hgo
  have hsz : argsSize decompArgs ≤ 150 := by
    simp only [decompArgs, eTOrigId, eDyn, argsSize, Expr.size, add, mul, r, k]
    omega
  have hE := V.endA_le hH
  have hc := decompPhaseCost_ofVals V nOrig θ (hldDepthBound V.n0) kk lenArr cnt mem
  have hsz1 : (ld (add (r rEnd) (k 2))).size ≤ 10 := by simp [Expr.size]
  unfold segDCost at hB
  rw [segD_split, List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
  -- step 55: the threshold
  refine SeqWPR.assign hP θ _ (by evd) le_rfl (by simp only [Expr.size]; omega) ?_
  -- step 56: the block width of the stretch pass
  refine SeqWPR.call hP (wstrLBContract w) [V.n0, hldDepthBound V.n0, V.L_w]
    (20 * Nat.log 2 (V.n0 + 1) + 20 * Nat.log 2 (hldDepthBound V.n0 + 2) + 110) hlb
    (by
      show evalArgs _ _ _ = _
      dsimp only [rN, rD, rLw]
      eval_expr
      all_goals (try rw [Function.update_of_ne (by omega)])
      all_goals omega)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl) <;> omega)
    ⟨V.n0, hldDepthBound V.n0, V.L_w, rfl, hw16, by omega, by omega, hLBw⟩
    (by
      simp only [wstrLBContract, List.getD_cons_succ, List.getD_cons_zero, argsSize, Expr.size]
      omega)
    (by omega) ?_
  rintro z mem₂ hpost₂
  obtain ⟨n', D', Lw', heq₂, rfl, hm₂⟩ := hpost₂
  subst mem₂
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl⟩ := heq₂
  rw [← hLB]
  -- steps 57 … 61
  refine segDMid_wp hP V
    (by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact r6)
    (by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact r8)
    (by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact a10)
    (by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact a11)
    (by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact a12)
    (by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact c63)
    g26 hw16 (by omega) ?_
  intro regs₂ hr2a hr2b
  have d : ∀ j < 65, regs₂ j = regs j := fun j hj => by
    rw [hr2a j (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have d65 : regs₂ 65 = θ := by
    rw [hr2a 65 (by omega), Function.update_of_ne (by omega), Function.update_apply, if_pos rfl]
  have d66 : regs₂ 66 = V.LB := by
    rw [hr2a 66 (by omega), Function.update_apply, if_pos rfl]
  have d67 : regs₂ 67 = V.dBase := hr2b 0 (by omega)
  have d68 : regs₂ 68 = V.hiCopy := hr2b 1 (by omega)
  have d69 : regs₂ 69 = V.inR := hr2b 2 (by omega)
  have d70 : regs₂ 70 = V.numS := hr2b 3 (by omega)
  have d71 : regs₂ 71 = V.idPtr := hr2b 4 (by omega)
  have q1 := (d 1 (by omega)).trans r1
  have q3 := (d 3 (by omega)).trans r3
  have q5 := (d 5 (by omega)).trans r5
  have q6 := (d 6 (by omega)).trans r6
  have q7 := (d 7 (by omega)).trans r7
  have q8 := (d 8 (by omega)).trans r8
  have q10 := (d 10 (by omega)).trans a10
  have q11 := (d 11 (by omega)).trans a11
  have q12 := (d 12 (by omega)).trans a12
  have q15 := (d 15 (by omega)).trans a15
  have q16 := (d 16 (by omega)).trans a16
  have q20 := (d 20 (by omega)).trans a20
  have q21 := (d 21 (by omega)).trans a21
  have q26 := (d 26 (by omega)).trans a26
  have q27 := (d 27 (by omega)).trans a27
  have q29 := (d 29 (by omega)).trans b29
  have q50 := (d 50 (by omega)).trans c50
  have q51 := (d 51 (by omega)).trans c51
  have q53 := (d 53 (by omega)).trans c53
  have q55 := (d 55 (by omega)).trans c55
  have q56 := (d 56 (by omega)).trans c56
  have q57 := (d 57 (by omega)).trans c57
  have q58 := (d 58 (by omega)).trans c58
  have q63 := (d 63 (by omega)).trans c63
  have hrep := V.repPtr_eq
  -- step 62: the decomposition phase
  refine SeqWPR.call hP (decompPhaseContract w h C bWT bLB bW bCopy bFlag bRoots decompPhaseCost)
    (DecompLayout.ofVals V nOrig θ (hldDepthBound V.n0) kk lenArr cnt).args
    (decompPhaseCost (DecompLayout.ofVals V 0 0 (hldDepthBound V.n0) 0 0 cnt).args
      (fun _ => 0) + 200) hdec
    (by
      rw [decompArgs_ofVals, hrep]
      simp only [tPiBase, tOrigIdBase, tDgTPtr, dynGraphSize, dgEListBase] at g17 g19 g23 ⊢
      rw [hrep] at g30
      show evalArgs _ _ _ = _
      dsimp only [decompArgs, eTOrigId, eDyn, rN, rM, rEu, rEv, rS, rTM, rAP, rTh, rDB, rD, rLw,
        rKn, rLin, rNO, rLog, rLen, rTP, rVc, rThB, rGP, rEc, rNumS, rId, rHi, rCnt, rThD, rVI,
        rInR, rNumSt, rDenSt]
      eval_expr
      all_goals omega)
    hall (decompPhase_seqPre I₀ bWT bLB bW bCopy bFlag bRoots)
    (by show decompPhaseCost _ mem + _ + 2 ≤ _; omega)
    (by omega) ?_
  intro v mem' hpost
  refine SeqWPR.mono hP (hnext _ v mem' hpost (fun j hj => ?_) (fun j hj => ?_) ?_) ?_
  · rw [Function.update_of_ne (by omega)]; exact d j hj
  · rw [Function.update_of_ne (by omega)]
    interval_cases j
    · exact d65
    · exact d66
    · exact d67
    · exact d68
    · exact d69
    · exact d70
    · exact d71
  · simp
  · unfold segDCost
    omega

end

end MinCostFlow.LSF.Program
