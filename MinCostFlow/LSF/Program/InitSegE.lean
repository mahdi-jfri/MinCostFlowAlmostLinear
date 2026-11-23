module

public import MinCostFlow.LSF.Program.InitSegD

/-!
# The init driver, steps `63, 64`

The fifth segment computes the work area `wBase` of the forest phase, which lies after the
scratch area of the stretch pass (its place depends on the block width `LB`), and runs the forest
phase. `segE_wp` takes `FPhaseIn` at the places `FLayout.ofVals V nOrig θ D k lenArr cnt` and
says: if the rest of the steps runs from every outcome of the forest phase, then the whole
sequence runs.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord
  InitDriver

@[expose] public section

/-- One step of the scratch places of the stretch pass, as an expression in the registers. -/
lemma eWsStep_eval {w : ℕ} {regs mem : ℕ → ℕ} {n tM m0 LB : ℕ}
    (a10 : regs 10 = n) (a11 : regs 11 = m0) (a12 : regs 12 = tM) (a66 : regs 66 = LB)
    (hn : n < 2 ^ w) (htM : tM < 2 ^ w) (hm : m0 < 2 ^ w) (hLB : LB < 2 ^ w) :
    ∀ j, wsStep n tM m0 LB j < 2 ^ w →
      evalAt w regs mem (eWsStep (r rN) (r rTM) (r rM) (r rLB) j) = some (wsStep n tM m0 LB j)
  | 0, _ => by show Expr.eval _ _ (Expr.reg 10) = some n; eval_expr
  | 1, h => by
    replace h : tM * LB < 2 ^ w := h
    show Expr.eval _ _ (Expr.bin .mul (Expr.reg 12) (Expr.reg 66)) = some (tM * LB)
    eval_expr
  | 2, h => by
    replace h : n * LB < 2 ^ w := h
    show Expr.eval _ _ (Expr.bin .mul (Expr.reg 10) (Expr.reg 66)) = some (n * LB)
    eval_expr
  | 3, h => by
    replace h : m0 * LB < 2 ^ w := h
    show Expr.eval _ _ (Expr.bin .mul (Expr.reg 11) (Expr.reg 66)) = some (m0 * LB)
    eval_expr
  | 4, _ => by show Expr.eval _ _ (Expr.reg 10) = some n; eval_expr
  | 5, _ => by show Expr.eval _ _ (Expr.reg 10) = some n; eval_expr
  | 6, _ => by show Expr.eval _ _ (Expr.reg 12) = some tM; eval_expr
  | 7, _ => by show Expr.eval _ _ (Expr.reg 10) = some n; eval_expr
  | 8, h => by
    replace h : n * LB < 2 ^ w := h
    show Expr.eval _ _ (Expr.bin .mul (Expr.reg 10) (Expr.reg 66)) = some (n * LB)
    eval_expr
  | 9, h => by
    replace h : m0 * LB < 2 ^ w := h
    show Expr.eval _ _ (Expr.bin .mul (Expr.reg 11) (Expr.reg 66)) = some (m0 * LB)
    eval_expr
  | 10, h => by
    replace h : m0 * LB < 2 ^ w := h
    show Expr.eval _ _ (Expr.bin .mul (Expr.reg 11) (Expr.reg 66)) = some (m0 * LB)
    eval_expr
  | j + 11, _ => by
    show Expr.eval _ _ (Expr.reg 66) = some LB
    eval_expr

/-- The scratch places of the stretch pass, as expressions in the registers. -/
lemma eWsPt_eval {w : ℕ} {regs mem : ℕ → ℕ} {idPtr n tM m0 LB : ℕ}
    (a10 : regs 10 = n) (a11 : regs 11 = m0) (a12 : regs 12 = tM) (a66 : regs 66 = LB)
    (a71 : regs 71 = idPtr)
    (hn : n < 2 ^ w) (htM : tM < 2 ^ w) (hm : m0 < 2 ^ w) (hLB : LB < 2 ^ w) :
    ∀ j, wsPt idPtr n tM m0 LB j < 2 ^ w →
      evalAt w regs mem (eWsPt (r rId) (r rN) (r rTM) (r rM) (r rLB) j) =
        some (wsPt idPtr n tM m0 LB j)
  | 0, _ => by show Expr.eval _ _ (Expr.reg 71) = some idPtr; eval_expr
  | j + 1, h => by
    have h' : wsPt idPtr n tM m0 LB j + wsStep n tM m0 LB j < 2 ^ w := h
    exact Expr.eval_add (eWsPt_eval a10 a11 a12 a66 a71 hn htM hm hLB j (by omega))
      (eWsStep_eval a10 a11 a12 a66 hn htM hm hLB j (by omega)) h'

/-- Step `63` computes `wBase`. -/
lemma segE_wBase_eval {w : ℕ} {regs mem : ℕ → ℕ} (V : InitVals)
    (a10 : regs 10 = V.n0) (a11 : regs 11 = V.m0) (a12 : regs 12 = V.tM)
    (a66 : regs 66 = V.LB) (a71 : regs 71 = V.idPtr) (hW : V.wBase < 2 ^ w) :
    evalAt w regs mem (add (eWsPt (r rId) (r rN) (r rTM) (r rM) (r rLB) 18) (r rM)) =
      some V.wBase := by
  have s32 : wsPt V.idPtr V.n0 V.tM V.m0 V.LB 18 + V.m0 = V.wBase := rfl
  have p1 := wsPt_mono V.idPtr V.n0 V.tM V.m0 V.LB (show 1 ≤ 18 by omega)
  have p7 := wsPt_mono V.idPtr V.n0 V.tM V.m0 V.LB (show 7 ≤ 18 by omega)
  have p12 := wsPt_mono V.idPtr V.n0 V.tM V.m0 V.LB (show 12 ≤ 18 by omega)
  have e1 : wsPt V.idPtr V.n0 V.tM V.m0 V.LB 1 = V.idPtr + V.n0 := rfl
  have e7 : wsPt V.idPtr V.n0 V.tM V.m0 V.LB 7 = wsPt V.idPtr V.n0 V.tM V.m0 V.LB 6 + V.tM := rfl
  have e12 : wsPt V.idPtr V.n0 V.tM V.m0 V.LB 12 =
    wsPt V.idPtr V.n0 V.tM V.m0 V.LB 11 + V.LB := rfl
  rw [← s32]
  exact Expr.eval_add (eWsPt_eval a10 a11 a12 a66 a71 (by omega) (by omega) (by omega)
    (by omega) 18 (by omega)) (Expr.eval_reg_of_eq a11) (by omega)

/-- The `21` arguments of the forest phase, at the places of the driver. -/
lemma forestArgs_ofVals (V : InitVals) (nOrig θ D kk lenArr cnt : ℕ) :
    (FLayout.ofVals V nOrig θ D kk lenArr cnt).args =
      [V.fPtr, V.vCap, fECap V.eCap V.n0, V.n0, V.vListPtr, V.tM, V.tTail, V.tHead,
        tOrigIdBase V.tPtr V.vCap V.tM, V.inR + V.n0 + V.n0, V.fAncPtr, V.inR,
        V.inR + V.n0 + V.n0 + V.tM, 0, V.auxPar + V.n0, V.dBase + 6 * V.n0, V.dBase + 7 * V.n0,
        auxLogCap V.n0, V.wBase, V.auxPar, V.wPtr] := rfl

/-- Every argument of the forest phase is a word. -/
lemma FPhaseIn.args_lt {w h : ℕ} {X : FLayout} {mem : ℕ → ℕ} (I : FPhaseIn w h X mem) :
    ∀ x ∈ X.args, x < 2 ^ w := by
  have hn := I.hn; have hL := I.hL
  have l1 := I.l1; have l2 := I.l2; have l3 := I.l3; have l4 := I.l4; have l5 := I.l5
  have l6 := I.l6; have l7 := I.l7; have l8 := I.l8; have l9 := I.l9; have l10 := I.l10
  have l11 := I.l11; have l12 := I.l12; have l13 := I.l13; have l14 := I.l14
  have l15 := I.l15; have l16 := I.l16; have l17 := I.l17; have l18 := I.l18
  have l19 := I.l19; have l20 := I.l20
  have hnL : X.logCap ≤ X.n * (3 * X.logCap) :=
    le_trans (by omega) (Nat.le_mul_of_pos_left _ hn)
  simp only [dynGraphSize, fAncSize, wBlockSize] at l2 l3 l4 l5 l6 l7 l8 l9 l10 l11
  simp only [wWorkSize] at l20
  simp only [FLayout.args, List.mem_cons, List.not_mem_nil, or_false]
  rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega

/-- The cost of the forest phase depends only on the sizes. -/
lemma fPhaseCost_ofVals (V : InitVals) (nOrig θ D kk lenArr cnt : ℕ) (mem : ℕ → ℕ) :
    fPhaseCost (FLayout.ofVals V nOrig θ D kk lenArr cnt).args mem =
      fPhaseCost (FLayout.ofVals V 0 0 0 0 0 0).args (fun _ => 0) := rfl

/-- The cost of the fifth segment. -/
def segECost (V : InitVals) : ℕ :=
  fPhaseCost (FLayout.ofVals V 0 0 0 0 0 0).args (fun _ => 0) + 600

set_option maxHeartbeats 4000000 in
theorem segE_wp {w h : ℕ} {p : Program} {I : InitIdx} {P : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop}
    (hP : UpClosed P) {rest : List DStep} {regs mem : ℕ → ℕ} {B : ℕ}
    {bG bA bW nOrig θ D kk lenArr cnt : ℕ} (V : InitVals)
    (hf : MeetsContract w p I.forest (fPhaseContract w h bG bA bW))
    (I₀ : FPhaseIn w h (FLayout.ofVals V nOrig θ D kk lenArr cnt) mem)
    (r7 : regs rVc = V.vCap) (r8 : regs rEc = V.eCap)
    (hA : ∀ j < 19, regs (10 + j) = (segAVals V).getD j 0)
    (hBv : ∀ j < 20, regs (29 + j) = (segBVals V cnt).getD j 0)
    (hCv : ∀ j < 14, regs (50 + j) = (segCVals V nOrig).getD j 0)
    (hDv : ∀ j < 7, regs (65 + j) = (segDVals V θ).getD j 0)
    (hB : segECost V ≤ B)
    (hnext : ∀ regs' v mem',
      (fPhaseContract w h bG bA bW).post (FLayout.ofVals V nOrig θ D kk lenArr cnt).args mem v
        mem' →
      (∀ j < 73, regs' j = regs j) → regs' 73 = V.wBase → regs' 74 = v →
      SeqWPR w p 10 P 65 rest regs' mem' (B - segECost V)) :
    SeqWPR w p 10 P 63 (segE I ++ rest) regs mem B := by
  have a10 : regs 10 = V.n0 := hA 0 (by omega)
  have a11 : regs 11 = V.m0 := hA 1 (by omega)
  have a12 : regs 12 = V.tM := hA 2 (by omega)
  have a15 : regs 15 = auxLogCap V.n0 := hA 5 (by omega)
  have a21 : regs 21 = V.tPtr := hA 11 (by omega)
  have a22 : regs 22 = V.fPtr := hA 12 (by omega)
  have a23 : regs 23 = V.fAncPtr := hA 13 (by omega)
  have a24 : regs 24 = V.wPtr := hA 14 (by omega)
  have b46 : regs 46 = V.tTail := hBv 17 (by omega)
  have b47 : regs 47 = V.tHead := hBv 18 (by omega)
  have c52 : regs 52 = V.vListPtr := hCv 2 (by omega)
  have c53 : regs 53 = V.auxPar := hCv 3 (by omega)
  have d66 : regs 66 = V.LB := hDv 1 (by omega)
  have d67 : regs 67 = V.dBase := hDv 2 (by omega)
  have d69 : regs 69 = V.inR := hDv 4 (by omega)
  have d71 : regs 71 = V.idPtr := hDv 6 (by omega)
  have hall := I₀.args_lt
  have hgo := hall
  rw [forestArgs_ofVals] at hgo
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hgo
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, -, g14, g15, g16, g17, g18,
    g19, g20⟩ := hgo
  have hsz : argsSize forestArgs ≤ 150 := by
    simp only [forestArgs, eTOrigId, eDyn, argsSize, Expr.size]
    omega
  have hsz1 : (add (eWsPt (r rId) (r rN) (r rTM) (r rM) (r rLB) 18) (r rM)).size ≤ 150 := by
    simp [Expr.size, eWsPt, eWsStep]
  have hc := fPhaseCost_ofVals V nOrig θ D kk lenArr cnt mem
  unfold segECost at hB
  simp only [segE, List.cons_append, List.nil_append]
  -- step 63: the work area of the forest phase
  refine SeqWPR.assign hP V.wBase _ (segE_wBase_eval V a10 a11 a12 d66 d71 g18) le_rfl
    (by omega) ?_
  have e : ∀ j < 73, Function.update regs (10 + 63) V.wBase j = regs j := fun j hj => by
    rw [Function.update_of_ne (by omega)]
  have e73 : Function.update regs (10 + 63) V.wBase 73 = V.wBase := by
    rw [Function.update_apply, if_pos rfl]
  -- step 64: the forest phase
  refine SeqWPR.call hP (fPhaseContract w h bG bA bW)
    (FLayout.ofVals V nOrig θ D kk lenArr cnt).args
    (fPhaseCost (FLayout.ofVals V 0 0 0 0 0 0).args (fun _ => 0) + 200) hf
    (by
      rw [forestArgs_ofVals]
      simp only [tOrigIdBase, tDgTPtr, dynGraphSize, fECap] at g2 g8 ⊢
      have q7 := (e 7 (by omega)).trans r7
      have q8 := (e 8 (by omega)).trans r8
      have q10 := (e 10 (by omega)).trans a10
      have q12 := (e 12 (by omega)).trans a12
      have q15 := (e 15 (by omega)).trans a15
      have q21 := (e 21 (by omega)).trans a21
      have q22 := (e 22 (by omega)).trans a22
      have q23 := (e 23 (by omega)).trans a23
      have q24 := (e 24 (by omega)).trans a24
      have q46 := (e 46 (by omega)).trans b46
      have q47 := (e 47 (by omega)).trans b47
      have q52 := (e 52 (by omega)).trans c52
      have q53 := (e 53 (by omega)).trans c53
      have q67 := (e 67 (by omega)).trans d67
      have q69 := (e 69 (by omega)).trans d69
      show evalArgs _ _ _ = _
      dsimp only [forestArgs, eTOrigId, eDyn, rFP, rVc, rEc, rN, rVL, rTM, rTT, rTH, rInR, rFA,
        rAP, rDB, rLog, rWB, rWP, rTP]
      eval_expr
      all_goals omega)
    hall (fPhase_seqPre I₀ bG bA bW)
    (by show fPhaseCost _ mem + _ + 2 ≤ _; omega)
    (by omega) ?_
  intro v mem' hpost
  refine SeqWPR.mono hP (hnext _ v mem' hpost (fun j hj => ?_) ?_ ?_) ?_
  · rw [Function.update_of_ne (by omega)]; exact e j hj
  · rw [Function.update_of_ne (by omega)]; exact e73
  · simp
  · unfold segECost
    omega

end

end MinCostFlow.LSF.Program
