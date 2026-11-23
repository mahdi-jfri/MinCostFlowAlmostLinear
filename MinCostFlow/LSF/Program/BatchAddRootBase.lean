module

public import MinCostFlow.LSF.Program.BatchAddRootClimb
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Pop-Step Register Invariant and Statement Prefixes (`BatchAddRootBase`)

Defines `PopRegsOk` and verifies the straight-line register/memory prefixes of one pop step in
`addOrigRootProc` (`addOrigRootPopRead_seq_le`, `addOrigRootPopUpdate_seq_le`,
`addOrigRootPopCut_seq_le`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Register invariant shared across all iterations of the pop loop in `addOrigRootProc`. -/
def PopRegsOk (b : ℕ) (x : LSFConcrete) (regs : ℕ → ℕ) : Prop :=
  let vCap := x.vCap; let eCap := x.eCap; let n0 := x.n0; let tM := x.tM; let L_w := x.L_w
  let eCapF := fECap eCap n0
  let tPtr := lsfTBlockPtr b vCap eCap
  let dgFPtr := lsfDgFPtr b vCap eCap tM
  let fAncPtr := lsfFAncPtr b vCap eCap n0 tM
  let auxPtr := lsfAuxPtr b vCap eCap n0 tM L_w
  regs 0 = b ∧ regs 2 = vCap ∧ regs 4 = n0 ∧ regs 5 = tM ∧ regs 6 = tPtr ∧
  regs 7 = dgFPtr ∧ regs 8 = fAncPtr ∧ regs 9 = auxPtr ∧
  regs 10 = fIsRootBase fAncPtr ∧
  regs 11 = auxVIdxBase auxPtr ∧
  regs 12 = auxVListBase auxPtr vCap ∧
  regs 14 = auxThStackBase auxPtr vCap n0 ∧
  regs 15 = auxOrigVertBase auxPtr vCap n0 ∧
  regs 16 = fRListBase fAncPtr vCap ∧
  regs 17 = fCompIdBase fAncPtr vCap ∧
  regs 18 = fCompRootBase fAncPtr vCap ∧
  regs 19 = fCompSizeBase fAncPtr vCap ∧
  regs 20 = eCapF ∧
  regs 21 = dgIntToExtBase dgFPtr vCap ∧
  regs 36 = dgETailSlotBase dgFPtr vCap eCapF ∧
  regs 37 = dgEHeadSlotBase dgFPtr vCap eCapF

/-- Executes the 8 setup loads (`r23..r30`) at the start of `addOrigRootPopStepStmt`. -/
lemma addOrigRootPopRead_seq_le
    {w auxPtr fAncPtr vCap n0 thStackBase restLen zIdx z oldCid rC oldSize rOrig rOrigIdx k B : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {tail : Stmt} {Q : Outcome → State → Prop}
    (hw16 : 16 ≤ 2 ^ w)
    (hrest_ltw : restLen < 2 ^ w) (hrOrigIdx_ltw : rOrigIdx < 2 ^ w)
    (hstk_ltw : thStackBase + restLen < 2 ^ w)
    (hvl_ltw : auxVListBase auxPtr vCap + zIdx < 2 ^ w)
    (hcid_ltw : fCompIdBase fAncPtr vCap + z < 2 ^ w)
    (hcr_ltw : fCompRootBase fAncPtr vCap + oldCid < 2 ^ w)
    (hcs_ltw : fCompSizeBase fAncPtr vCap + oldCid < 2 ^ w)
    (horig_ltw : auxOrigVertBase auxPtr vCap n0 + rC < 2 ^ w)
    (hvidx_ltw : auxVIdxBase auxPtr + rOrig < 2 ^ w)
    (hr11 : st.regs 11 = auxVIdxBase auxPtr) (hr12 : st.regs 12 = auxVListBase auxPtr vCap)
    (hr14 : st.regs 14 = thStackBase) (hr15 : st.regs 15 = auxOrigVertBase auxPtr vCap n0)
    (hr17 : st.regs 17 = fCompIdBase fAncPtr vCap) (hr18 : st.regs 18 = fCompRootBase fAncPtr vCap)
    (hr19 : st.regs 19 = fCompSizeBase fAncPtr vCap) (hr23 : st.regs 23 = restLen + 1)
    (hm_stk : st.mem (thStackBase + restLen) = zIdx)
    (hm_vl : st.mem (auxVListBase auxPtr vCap + zIdx) = z)
    (hm_cid : st.mem (fCompIdBase fAncPtr vCap + z) = oldCid)
    (hm_cr : st.mem (fCompRootBase fAncPtr vCap + oldCid) = rC)
    (hm_cs : st.mem (fCompSizeBase fAncPtr vCap + oldCid) = oldSize)
    (hm_orig : st.mem (auxOrigVertBase auxPtr vCap n0 + rC) = rOrig)
    (hm_vidx : st.mem (auxVIdxBase auxPtr + rOrig) = rOrigIdx + 1)
    (hcont : ∃ o st' c, Runs w p ω tail
      { mem := st.mem,
        regs := Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update (Function.update st.regs
            23 restLen) 24 zIdx) 25 z) 26 oldCid) 27 rC) 28 oldSize) 29 rOrig) 30 rOrigIdx,
        pos := st.pos } o st' c ∧
      Q o st' ∧ k + 60 + c ≤ B) :
    ∃ o st' c, Runs w p ω
      (.assign 23 (.bin .sub (.reg 23) (.const 1)) ;;
       .assign 24 (.load (.bin .add (.reg 14) (.reg 23))) ;;
       .assign 25 (.load (.bin .add (.reg 12) (.reg 24))) ;;
       .assign 26 (.load (.bin .add (.reg 17) (.reg 25))) ;;
       .assign 27 (.load (.bin .add (.reg 18) (.reg 26))) ;;
       .assign 28 (.load (.bin .add (.reg 19) (.reg 26))) ;;
       .assign 29 (.load (.bin .add (.reg 15) (.reg 27))) ;;
       .assign 30 (.bin .sub (.load (.bin .add (.reg 11) (.reg 29))) (.const 1)) ;;
       tail) st o st' c ∧ Q o st' ∧ k + c ≤ B := by
  refine runs_seq_assign_le (v := restLen) ?_ ?_
  · rw [show some restLen = some (BinOp.sub.eval (restLen + 1) 1) from rfl]
    exact Expr.eval_bin (hr23 ▸ Expr.eval_reg (w := w) 23 st) (Expr.eval_const (by omega))
      (by dsimp [BinOp.eval]; omega)
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := zIdx) (by eval_expr) hm_stk) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := z) (by eval_expr) hm_vl) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := oldCid) (by eval_expr) hm_cid) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := rC) (by eval_expr) hm_cr) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := oldSize) (by eval_expr) hm_cs) ?_; dsimp only
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := rOrig) (by eval_expr) hm_orig) ?_; dsimp only
  refine runs_seq_assign_le (v := rOrigIdx) ?_ ?_
  · rw [show some rOrigIdx = some (BinOp.sub.eval (rOrigIdx + 1) 1) from rfl]
    exact Expr.eval_bin (Expr.eval_load_of_eq (by eval_expr) hm_vidx)
      (Expr.eval_const (by omega)) (by dsimp [BinOp.eval]; omega)
  dsimp only
  obtain ⟨o, st', c, hr, hq, hc⟩ := hcont
  refine ⟨o, st', c, hr, hq, ?_⟩
  dsimp only [Expr.size] at *; omega

/-- Executes the 5 root-marking writes in `addOrigRootPopStepStmt` before an arbitrary `tail`. -/
lemma addOrigRootPopUpdate_seq_le {w b fAncPtr vCap z rCnt k B : ℕ} {p : Program}
    {ω : ℕ → Bool} {st : State} {tail : Stmt} {Q : Outcome → State → Prop}
    (_hw16 : 16 ≤ 2 ^ w) (h24_ltw : 24 < 2 ^ w)
    (hisr_z_ltw : fIsRootBase fAncPtr + z < 2 ^ w)
    (hf_rcnt_ltw : fAncPtr + fOffRCount < 2 ^ w)
    (hrL_cnt_ltw : fRListBase fAncPtr vCap + rCnt < 2 ^ w)
    (hb_rcnt_ltw : b + lsfOffRCount < 2 ^ w)
    (hrcnt1_ltw : rCnt + 1 < 2 ^ w)
    (hr0 : st.regs 0 = b) (hr8 : st.regs 8 = fAncPtr)
    (hr10 : st.regs 10 = fIsRootBase fAncPtr) (hr16 : st.regs 16 = fRListBase fAncPtr vCap)
    (hr25 : st.regs 25 = z)
    (hmem1_rcnt : st.mem (fAncPtr + fOffRCount) = rCnt)
    (hcont : ∃ o st' c, Runs w p ω tail
      { mem := Function.update (Function.update (Function.update
          (Function.update st.mem (fIsRootBase fAncPtr + z) 1)
          (fRListBase fAncPtr vCap + rCnt) z)
          (fAncPtr + fOffRCount) (rCnt + 1))
          (b + lsfOffRCount) (rCnt + 1),
        regs := Function.update st.regs 35 rCnt,
        pos := st.pos } o st' c ∧
      Q o st' ∧ k + 45 + c ≤ B) :
    ∃ o st' c, Runs w p ω
      (.store (.bin .add (.reg 10) (.reg 25)) (.const 1) ;;
       .assign 35 (.load (.bin .add (.reg 8) (.const fOffRCount))) ;;
       .store (.bin .add (.reg 16) (.reg 35)) (.reg 25) ;;
       .store (.bin .add (.reg 8) (.const fOffRCount)) (.bin .add (.reg 35) (.const 1)) ;;
       .store (.bin .add (.reg 0) (.const lsfOffRCount)) (.bin .add (.reg 35) (.const 1)) ;;
       tail) st o st' c ∧ Q o st' ∧ k + c ≤ B := by
  have hmem1a : Function.update st.mem (fIsRootBase fAncPtr + z) 1 (fAncPtr + fOffRCount) = rCnt := by
    rw [Function.update_of_ne (by dsimp [fIsRootBase, fOffRCount, fAncHdrSize]; omega)]; exact hmem1_rcnt
  refine runs_seq_store_le (x := fIsRootBase fAncPtr + z) (v := 1)
    (Expr.eval_bin (hr10 ▸ Expr.eval_reg (w := w) 10 st) (hr25 ▸ Expr.eval_reg (w := w) 25 st)
      (by dsimp [BinOp.eval]; exact hisr_z_ltw))
    (Expr.eval_const (by omega)) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := rCnt)
    (Expr.eval_bin (hr8 ▸ Expr.eval_reg (w := w) 8 _)
      (Expr.eval_const (by dsimp [fOffRCount]; omega))
      (by dsimp [BinOp.eval]; exact hf_rcnt_ltw)) hmem1a) ?_; dsimp only
  refine runs_seq_store_le (x := fRListBase fAncPtr vCap + rCnt) (v := z)
    (Expr.eval_bin (by simp only [Expr.eval, Function.update_of_ne (by decide : (16 : ℕ) ≠ 35), hr16])
      (by simp only [Expr.eval, Function.update_self])
      (by dsimp [BinOp.eval]; exact hrL_cnt_ltw))
    (by simp only [Expr.eval, Function.update_of_ne (by decide : (25 : ℕ) ≠ 35), hr25]) ?_; dsimp only
  refine runs_seq_store_le (x := fAncPtr + fOffRCount) (v := rCnt + 1)
    (Expr.eval_bin (by simp only [Expr.eval, Function.update_of_ne (by decide : (8 : ℕ) ≠ 35), hr8])
      (Expr.eval_const (by dsimp [fOffRCount]; omega))
      (by dsimp [BinOp.eval]; exact hf_rcnt_ltw))
    (Expr.eval_bin (by simp only [Expr.eval, Function.update_self])
      (Expr.eval_const (by omega))
      (by dsimp [BinOp.eval]; exact hrcnt1_ltw)) ?_; dsimp only
  refine runs_seq_store_le (x := b + lsfOffRCount) (v := rCnt + 1)
    (Expr.eval_bin (by simp only [Expr.eval, Function.update_of_ne (by decide : (0 : ℕ) ≠ 35), hr0])
      (Expr.eval_const (by dsimp [lsfOffRCount]; omega))
      (by dsimp [BinOp.eval]; exact hb_rcnt_ltw))
    (Expr.eval_bin (by simp only [Expr.eval, Function.update_self])
      (Expr.eval_const (by omega))
      (by dsimp [BinOp.eval]; exact hrcnt1_ltw)) ?_; dsimp only
  obtain ⟨o, st', c, hr, hq, hc⟩ := hcont
  refine ⟨o, st', c, hr, hq, ?_⟩
  dsimp only [Expr.size] at *; omega

/-- Executes `minEdgeUp`, endpoint reads, `dgDeleteEdge`, and the 5 root-marking writes before an
arbitrary `tail`, abstracting the resulting register file into a clean `regs2` variable. -/
lemma addOrigRootPopCut_seq_le
    {w b idxMinUp idxDgDel auxPtr tPtr dgFPtr fAncPtr vCap eCapF n0 tM
     restLen zIdx z oldCid rC oldSize rOrig rOrigIdx cutE a b' rCnt k B : ℕ}
    {p : Program} {ω : ℕ → Bool} {S : LSFState} {vList tOrigList : List ℕ}
    {st : State} {tail : Stmt} {Q : Outcome → State → Prop}
    (hw16 : 16 ≤ 2 ^ w) (h24_ltw : 24 < 2 ^ w)
    (h_dgF_fAnc : dgFPtr + dynGraphSize vCap eCapF ≤ fAncPtr)
    (haux_ltw : auxPtr + auxSize vCap n0 < 2 ^ w) (ht_ltw : tPtr + tBlockSize vCap 0 tM < 2 ^ w ∨ tPtr < 2 ^ w)
    (hdgF_ltw : dgFPtr + dynGraphSize vCap eCapF < 2 ^ w)
    (hvCap_ltw : vCap < 2 ^ w) (hn0_le : n0 ≤ vCap) (htM_le : tM ≤ n0)
    (hzIdx_lt : zIdx < n0) (hrOrigIdx_lt : rOrigIdx < n0) (hcut_lt : cutE < eCapF)
    (hETail_ltw : dgETailSlotBase dgFPtr vCap eCapF + cutE < 2 ^ w)
    (hEHead_ltw : dgEHeadSlotBase dgFPtr vCap eCapF + cutE < 2 ^ w)
    (hIntA_ltw : dgIntToExtBase dgFPtr vCap + st.mem (dgETailSlotBase dgFPtr vCap eCapF + cutE) < 2 ^ w)
    (hIntB_ltw : dgIntToExtBase dgFPtr vCap + st.mem (dgEHeadSlotBase dgFPtr vCap eCapF + cutE) < 2 ^ w)
    (hisr_z_ltw : fIsRootBase fAncPtr + z < 2 ^ w)
    (hf_rcnt_ltw : fAncPtr + fOffRCount < 2 ^ w)
    (hrL_cnt_ltw : fRListBase fAncPtr vCap + rCnt < 2 ^ w)
    (hb_rcnt_ltw : b + lsfOffRCount < 2 ^ w)
    (hrcnt1_ltw : rCnt + 1 < 2 ^ w)
    (hr0 : st.regs 0 = b) (hr2 : st.regs 2 = vCap) (hr4 : st.regs 4 = n0) (hr5 : st.regs 5 = tM)
    (hr6 : st.regs 6 = tPtr) (hr7 : st.regs 7 = dgFPtr) (hr8 : st.regs 8 = fAncPtr)
    (hr9 : st.regs 9 = auxPtr) (hr10 : st.regs 10 = fIsRootBase fAncPtr)
    (hr16 : st.regs 16 = fRListBase fAncPtr vCap)
    (hr21 : st.regs 21 = dgIntToExtBase dgFPtr vCap)
    (hr36 : st.regs 36 = dgETailSlotBase dgFPtr vCap eCapF)
    (hr37 : st.regs 37 = dgEHeadSlotBase dgFPtr vCap eCapF)
    (ha_read : st.mem (dgIntToExtBase dgFPtr vCap + st.mem (dgETailSlotBase dgFPtr vCap eCapF + cutE)) = a)
    (hb_read : st.mem (dgIntToExtBase dgFPtr vCap + st.mem (dgEHeadSlotBase dgFPtr vCap eCapF + cutE)) = b')
    (hRcnt_mem : st.mem (fAncPtr + fOffRCount) = rCnt)
    (hcut_def : minEdgeOn S.π (walkEdges (S.T₀.forestPath (vList[zIdx]!) (vList[rOrigIdx]!))) = cutE)
    (hMinUp : MeetsContract w p idxMinUp (minEdgeUpContract w S vList tOrigList))
    (hpre_min : (minEdgeUpContract w S vList tOrigList).pre [auxPtr, tPtr, vCap, n0, tM, zIdx, rOrigIdx] st.mem)
    (hDgDel : MeetsContract w p idxDgDel (dgDeleteEdgeContract w vCap eCapF S.RF.F))
    (hpre_del : (dgDeleteEdgeContract w vCap eCapF S.RF.F).pre [dgFPtr, cutE] st.mem)
    (hcont : ∀ (mem1 : ℕ → ℕ) (pos1 : ℕ) (regs2 : ℕ → ℕ),
      DynGraphAt mem1 dgFPtr vCap eCapF
        (if cutE ∈ S.RF.F.E then S.RF.F.applyUpdate (.delete cutE) else S.RF.F) →
      (∀ addr, addr < dgFPtr ∨ dgFPtr + dynGraphSize vCap eCapF ≤ addr → mem1 addr = st.mem addr) →
      (∀ r, r ≤ 21 ∨ r = 36 ∨ r = 37 → regs2 r = st.regs r) →
      regs2 23 = restLen → regs2 25 = z → regs2 26 = oldCid → regs2 27 = rC →
      regs2 28 = oldSize → regs2 32 = a → regs2 33 = b' →
      ∃ o st' c, Runs w p ω tail
        { mem := Function.update (Function.update (Function.update
            (Function.update mem1 (fIsRootBase fAncPtr + z) 1)
            (fRListBase fAncPtr vCap + rCnt) z)
            (fAncPtr + fOffRCount) (rCnt + 1))
            (b + lsfOffRCount) (rCnt + 1),
          regs := regs2, pos := pos1 } o st' c ∧
        Q o st' ∧ k + (120 * auxLogCap n0 + 660) + c ≤ B) :
    ∃ o st' c, Runs w p ω
      (.call 31 idxMinUp [.reg 9, .reg 6, .reg 2, .reg 4, .reg 5, .reg 24, .reg 30] ;;
       .assign 32 (.load (.bin .add (.reg 21) (.load (.bin .add (.reg 36) (.reg 31))))) ;;
       .assign 33 (.load (.bin .add (.reg 21) (.load (.bin .add (.reg 37) (.reg 31))))) ;;
       .call 34 idxDgDel [.reg 7, .reg 31] ;;
       .store (.bin .add (.reg 10) (.reg 25)) (.const 1) ;;
       .assign 35 (.load (.bin .add (.reg 8) (.const fOffRCount))) ;;
       .store (.bin .add (.reg 16) (.reg 35)) (.reg 25) ;;
       .store (.bin .add (.reg 8) (.const fOffRCount)) (.bin .add (.reg 35) (.const 1)) ;;
       .store (.bin .add (.reg 0) (.const lsfOffRCount)) (.bin .add (.reg 35) (.const 1)) ;;
       tail)
      { mem := st.mem,
        regs := Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update (Function.update st.regs
            23 restLen) 24 zIdx) 25 z) 26 oldCid) 27 rC) 28 oldSize) 29 rOrig) 30 rOrigIdx,
        pos := st.pos } o st' c ∧ Q o st' ∧ k + c ≤ B := by
  have hdgF_sz : dynGraphSize vCap eCapF = 4 + 7 * vCap + 9 * eCapF := rfl
  have ht_ltw' : tPtr < 2 ^ w := by rcases ht_ltw with h | h <;> omega
  refine runs_seq_call_le hMinUp (by eval_expr)
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    hpre_min ?_
  intro ret_min mem_min pos_min hpost_min
  rcases hpost_min with ⟨_, _, _, _, _, _, _, hargs_m, rfl, hret_min⟩
  simp only [List.cons.injEq, and_true] at hargs_m
  rcases hargs_m with ⟨-, -, -, -, -, hz_m, hr_m⟩
  rw [← hz_m, ← hr_m, hcut_def] at hret_min
  subst ret_min
  refine runs_seq_assign_le (v := a) ?_ ?_
  · refine Expr.eval_load_of_eq ?_ ha_read
    exact Expr.eval_bin (by eval_expr) (Expr.eval_load_of_eq (by eval_expr) rfl)
      (by dsimp [BinOp.eval]; omega)
  dsimp only
  refine runs_seq_assign_le (v := b') ?_ ?_
  · refine Expr.eval_load_of_eq ?_ hb_read
    exact Expr.eval_bin (by eval_expr) (Expr.eval_load_of_eq (by eval_expr) rfl)
      (by dsimp [BinOp.eval]; omega)
  dsimp only
  refine runs_seq_call_le hDgDel (by eval_expr)
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl <;> omega)
    hpre_del ?_
  intro v_del mem1 pos1 hpost_del
  rcases hpost_del with ⟨_, _, hargs_d, _, hdgF1_raw, hfr1⟩
  simp only [List.cons.injEq, and_true] at hargs_d
  rcases hargs_d with ⟨rfl, rfl⟩
  have hmem1_rcnt : mem1 (fAncPtr + fOffRCount) = rCnt :=
    (hfr1 _ (Or.inr (by omega))).trans hRcnt_mem
  let regs1 : ℕ → ℕ := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update st.regs
        23 restLen) 24 zIdx) 25 z) 26 oldCid) 27 rC) 28 oldSize) 29 rOrig)
      30 rOrigIdx) 31 cutE) 32 a) 33 b') 34 v_del
  have hreg1_lo : ∀ r, r ≤ 21 ∨ r = 36 ∨ r = 37 → regs1 r = st.regs r := by
    intro r hr; dsimp only [regs1]; clear * - hr
    rw [Function.update_of_ne (by omega : r ≠ 34), Function.update_of_ne (by omega : r ≠ 33),
      Function.update_of_ne (by omega : r ≠ 32), Function.update_of_ne (by omega : r ≠ 31),
      Function.update_of_ne (by omega : r ≠ 30), Function.update_of_ne (by omega : r ≠ 29),
      Function.update_of_ne (by omega : r ≠ 28), Function.update_of_ne (by omega : r ≠ 27),
      Function.update_of_ne (by omega : r ≠ 26), Function.update_of_ne (by omega : r ≠ 25),
      Function.update_of_ne (by omega : r ≠ 24), Function.update_of_ne (by omega : r ≠ 23)]
  have hreg1_25 : regs1 25 = z := by
    dsimp only [regs1]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self]
  refine addOrigRootPopUpdate_seq_le hw16 h24_ltw hisr_z_ltw hf_rcnt_ltw hrL_cnt_ltw hb_rcnt_ltw hrcnt1_ltw
    ((hreg1_lo 0 (by decide)).trans hr0)
    ((hreg1_lo 8 (by decide)).trans hr8)
    ((hreg1_lo 10 (by decide)).trans hr10)
    ((hreg1_lo 16 (by decide)).trans hr16)
    hreg1_25 hmem1_rcnt ?_
  let regs2 : ℕ → ℕ := Function.update regs1 35 rCnt
  have hreg2_lo : ∀ r, r ≤ 21 ∨ r = 36 ∨ r = 37 → regs2 r = st.regs r :=
    fun r hr => (Function.update_of_ne (by clear * - hr; omega) _ _).trans (hreg1_lo r hr)
  have hreg2_23 : regs2 23 = restLen := by
    dsimp only [regs2, regs1]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
  have hreg2_25 : regs2 25 = z := (Function.update_of_ne (by decide) _ _).trans hreg1_25
  have hreg2_26 : regs2 26 = oldCid := by
    dsimp only [regs2, regs1]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self]
  have hreg2_27 : regs2 27 = rC := by
    dsimp only [regs2, regs1]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
  have hreg2_28 : regs2 28 = oldSize := by
    dsimp only [regs2, regs1]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self]
  have hreg2_32 : regs2 32 = a := by
    dsimp only [regs2, regs1]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self]
  have hreg2_33 : regs2 33 = b' := by
    dsimp only [regs2, regs1]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
  obtain ⟨o, st', c, hr, hq, hc⟩ :=
    hcont mem1 pos1 regs2 hdgF1_raw hfr1 hreg2_lo hreg2_23 hreg2_25 hreg2_26 hreg2_27 hreg2_28 hreg2_32 hreg2_33
  refine ⟨o, st', c, hr, hq, ?_⟩
  have hcost_min : (minEdgeUpContract w S vList tOrigList).cost
      [auxPtr, tPtr, vCap, n0, tM, zIdx, rOrigIdx] st.mem = 120 * auxLogCap n0 + 120 := rfl
  have hcost_del : ∀ m, (dgDeleteEdgeContract w vCap eCapF S.RF.F).cost [dgFPtr, cutE] m = 450 := fun _ => rfl
  rw [hcost_min, hcost_del]
  have hs1 : argsSize [.reg 9, .reg 6, .reg 2, .reg 4, .reg 5, .reg 24, .reg 30] = 7 := rfl
  have hs2 : (Expr.load (.bin .add (.reg 21) (.load (.bin .add (.reg 36) (.reg 31))))).size = 7 := rfl
  have hs3 : (Expr.load (.bin .add (.reg 21) (.load (.bin .add (.reg 37) (.reg 31))))).size = 7 := rfl
  have hs4 : argsSize [.reg 7, .reg 31] = 2 := rfl
  rw [hs1, hs2, hs3, hs4]
  exact (Nat.add_le_add_right (show k + 7 + (120 * auxLogCap n0 + 120) + 2 + 7 + 2 + 7 + 2 + 2 + 450 + 2 + 45 ≤
      k + (120 * auxLogCap n0 + 660) by
    have hL : ∀ L : ℕ, k + 7 + (120 * L + 120) + 2 + 7 + 2 + 7 + 2 + 2 + 450 + 2 + 45 ≤
        k + (120 * L + 660) := fun L => by clear * - k L; omega
    exact hL (auxLogCap n0)) c).trans hc

end

end MinCostFlow.LSF.Program
