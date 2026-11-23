module

public import MinCostFlow.LSF.Program.BatchAddRoot
import Mathlib.Tactic.Linarith

/-!
# Forest-Cut Logging Definitions and Helpers (`CompCutLogBase`)

Defines:
* `compApplyForestCut` and `CompForestCutsValid`: exact step-by-step forest-cut specification
  matching `tourCut` (edge deletions paired with new roots, no links).
* `Stmt.notWritesReg` and `runs_reg_of_notWrites`: syntactic register-preservation frame lemma
  for `WordRAM.Runs`.
* `compLogPopStepStmt`, `compLogAddOrigRootProc`, and `CutLogBufOk`.
* `compLogPopCut_seq_le`: abstracts the 12-register `minEdgeUp` + endpoint-read + `dgDeleteEdge`
  + 5-write prefix of `compLogPopStepStmt` into an opaque `regs2` exposing `regs2 31 = cutE` and
  `regs2 40..42`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Forest-cut step relation -/

/-- Apply one forest cut `(cutE, newRoot)` to a rooted forest `RF`: erases `cutE` from `RF.F` and
inserts `newRoot` into `RF.R` (matching `tourCut`). -/
def compApplyForestCut (RF : RootedForest) (p : ℕ × ℕ) : RootedForest :=
  { F := { RF.F with E := RF.F.E.erase p.1 }, R := insert p.2 RF.R }

/-- Step-by-step validity of a list of forest cuts `(cutE, newRoot)` on `RF`, matching the
precondition of `tourCut` at every step. -/
def CompForestCutsValid (vCap : ℕ) : RootedForest → List (ℕ × ℕ) → Prop
  | _, [] => True
  | RF, (e, r) :: rest =>
    e ∈ RF.F.E ∧ r < vCap ∧ r ∈ RF.F.V ∧ r ∉ RF.R ∧
    (∀ v ∈ RF.F.V, ∃! rt, rt ∈ insert r RF.R ∧
      ({ RF.F with E := RF.F.E.erase e } : MGraph).Connected v rt) ∧
    CompForestCutsValid vCap (compApplyForestCut RF (e, r)) rest

lemma compForestCutsValid_append {vCap : ℕ} {RF : RootedForest} {l₁ l₂ : List (ℕ × ℕ)}
    (h₁ : CompForestCutsValid vCap RF l₁)
    (h₂ : CompForestCutsValid vCap (l₁.foldl compApplyForestCut RF) l₂) :
    CompForestCutsValid vCap RF (l₁ ++ l₂) := by
  induction l₁ generalizing RF with
  | nil => exact h₂
  | cons p rest ih =>
    rcases p with ⟨e, r⟩
    rcases h₁ with ⟨h1, h2, h3, h4, h5, hrest⟩
    exact ⟨h1, h2, h3, h4, h5, ih hrest h₂⟩

/-! ## 2. Syntactic register-preservation frame lemma -/

/-- Syntactic predicate: statement `s` never assigns to register `r`. -/
def stmtNotWritesReg (r : ℕ) : Stmt → Prop
  | .nop => True
  | .assign d _ => d ≠ r
  | .store _ _ => True
  | .rand d => d ≠ r
  | .seq s₁ s₂ => stmtNotWritesReg r s₁ ∧ stmtNotWritesReg r s₂
  | .cond _ s₁ s₂ => stmtNotWritesReg r s₁ ∧ stmtNotWritesReg r s₂
  | .loop _ body => stmtNotWritesReg r body
  | .call d _ _ => d ≠ r
  | .ret _ => True

private lemma exec_reg_of_notWrites {w r : ℕ} {p : Program} {ω : ℕ → Bool} :
    ∀ fuel (s : Stmt) (st st' : State) (o : Outcome) (c : ℕ),
      exec w p ω fuel s st = some (o, st', c) → stmtNotWritesReg r s → st'.regs r = st.regs r
  | 0, _, _, _, _, _, h, _ => by simp [exec] at h
  | fuel + 1, s, st, st', o, c, h, hnw => by
    cases s with
    | nop => simp [exec] at h; rcases h with ⟨_, rfl, _⟩; rfl
    | assign d e =>
      simp only [exec] at h; cases he : e.eval w st <;> simp [he] at h
      rcases h with ⟨_, rfl, _⟩; exact Function.update_of_ne (Ne.symm hnw) _ _
    | store a e =>
      simp only [exec] at h; cases ha : a.eval w st <;> cases he : e.eval w st <;> simp [ha, he] at h
      rcases h with ⟨_, rfl, _⟩; rfl
    | rand d =>
      simp [exec] at h; rcases h with ⟨_, rfl, _⟩; exact Function.update_of_ne (Ne.symm hnw) _ _
    | seq s₁ s₂ =>
      simp only [exec] at h
      cases h1 : exec w p ω fuel s₁ st with
      | none => simp [h1] at h
      | some res1 =>
        rcases res1 with ⟨o1, st1, c1⟩
        cases o1 with
        | returned v =>
          simp [h1] at h; rcases h with ⟨_, rfl, _⟩
          exact exec_reg_of_notWrites fuel s₁ st st1 (.returned v) c1 h1 hnw.1
        | normal =>
          simp only [h1] at h
          cases h2 : exec w p ω fuel s₂ st1 with
          | none => simp [h2] at h
          | some res2 =>
            rcases res2 with ⟨o2, st2, c2⟩
            simp [h2] at h; rcases h with ⟨_, rfl, _⟩
            exact (exec_reg_of_notWrites fuel s₂ st1 st2 o2 c2 h2 hnw.2).trans
              (exec_reg_of_notWrites fuel s₁ st st1 .normal c1 h1 hnw.1)
    | cond e s₁ s₂ =>
      simp only [exec] at h
      cases he : e.eval w st with
      | none => simp [he] at h
      | some v =>
        simp only [he] at h
        split_ifs at h with hv
        · cases h2 : exec w p ω fuel s₂ st with
          | none => simp [h2] at h
          | some res =>
            rcases res with ⟨o2, st2, c2⟩; simp [h2] at h; rcases h with ⟨_, rfl, _⟩
            exact exec_reg_of_notWrites fuel s₂ st st2 o2 c2 h2 hnw.2
        · cases h1 : exec w p ω fuel s₁ st with
          | none => simp [h1] at h
          | some res =>
            rcases res with ⟨o1, st1, c1⟩; simp [h1] at h; rcases h with ⟨_, rfl, _⟩
            exact exec_reg_of_notWrites fuel s₁ st st1 o1 c1 h1 hnw.1
    | loop e body =>
      simp only [exec] at h
      cases he : e.eval w st with
      | none => simp [he] at h
      | some v =>
        simp only [he] at h
        split_ifs at h with hv
        · simp at h; rcases h with ⟨_, rfl, _⟩; rfl
        · cases hb : exec w p ω fuel body st with
          | none => simp [hb] at h
          | some res1 =>
            rcases res1 with ⟨o1, st1, c1⟩
            cases o1 with
            | returned u =>
              simp [hb] at h; rcases h with ⟨_, rfl, _⟩
              exact exec_reg_of_notWrites fuel body st st1 (.returned u) c1 hb hnw
            | normal =>
              simp only [hb] at h
              cases hl : exec w p ω fuel (.loop e body) st1 with
              | none => simp [hl] at h
              | some res2 =>
                rcases res2 with ⟨o2, st2, c2⟩; simp [hl] at h; rcases h with ⟨_, rfl, _⟩
                exact (exec_reg_of_notWrites fuel (.loop e body) st1 st2 o2 c2 hl hnw).trans
                  (exec_reg_of_notWrites fuel body st st1 .normal c1 hb hnw)
    | call d f args =>
      simp only [exec] at h
      cases ha : evalArgs w st args with
      | none => simp [ha] at h
      | some vs =>
        cases hp : p.procs[f]? with
        | none => simp [ha, hp] at h
        | some body =>
          simp only [ha, hp] at h
          split at h
          · cases h
          · rcases Option.some.inj h with ⟨_, rfl, _⟩
            exact Function.update_of_ne (Ne.symm hnw) _ _
    | ret e =>
      simp only [exec] at h; cases he : e.eval w st <;> simp [he] at h
      rcases h with ⟨_, rfl, _⟩; rfl

lemma runs_reg_of_notWrites {w r : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt}
    {st st' : State} {o : Outcome} {c : ℕ}
    (hr : Runs w p ω s st o st' c) (hnw : stmtNotWritesReg r s) : st'.regs r = st.regs r := by
  obtain ⟨fuel, hf⟩ := hr
  exact exec_reg_of_notWrites fuel s st st' o c hf hnw

/-! ## 3. Logging root-closure procedure -/

/-- One pop iteration of `compLogAddOrigRootProc`: identical to `addOrigRootPopStepStmt` followed
by appending `(z, cutE)` at `(rootsBuf[cnt], fDelBuf[cnt])` and incrementing `*cntPtr`.
Registers `40, 41, 42` hold `rootsBuf, fDelBuf, cntPtr`; register `43` is scratch. -/
def compLogPopStepStmt (idxMinUp idxDgDel idxBFS : ℕ) : Stmt :=
  .assign 23 (.bin .sub (.reg 23) (.const 1)) ;;
  .assign 24 (.load (.bin .add (.reg 14) (.reg 23))) ;;
  .assign 25 (.load (.bin .add (.reg 12) (.reg 24))) ;;
  .assign 26 (.load (.bin .add (.reg 17) (.reg 25))) ;;
  .assign 27 (.load (.bin .add (.reg 18) (.reg 26))) ;;
  .assign 28 (.load (.bin .add (.reg 19) (.reg 26))) ;;
  .assign 29 (.load (.bin .add (.reg 15) (.reg 27))) ;;
  .assign 30 (.bin .sub (.load (.bin .add (.reg 11) (.reg 29))) (.const 1)) ;;
  .call 31 idxMinUp [.reg 9, .reg 6, .reg 2, .reg 4, .reg 5, .reg 24, .reg 30] ;;
  .assign 32 (.load (.bin .add (.reg 21) (.load (.bin .add (.reg 36) (.reg 31))))) ;;
  .assign 33 (.load (.bin .add (.reg 21) (.load (.bin .add (.reg 37) (.reg 31))))) ;;
  .call 34 idxDgDel [.reg 7, .reg 31] ;;
  .store (.bin .add (.reg 10) (.reg 25)) (.const 1) ;;
  .assign 35 (.load (.bin .add (.reg 8) (.const fOffRCount))) ;;
  .store (.bin .add (.reg 16) (.reg 35)) (.reg 25) ;;
  .store (.bin .add (.reg 8) (.const fOffRCount)) (.bin .add (.reg 35) (.const 1)) ;;
  .store (.bin .add (.reg 0) (.const lsfOffRCount)) (.bin .add (.reg 35) (.const 1)) ;;
  .call 34 idxBFS
    [.reg 7, .reg 8, .reg 9, .reg 2, .reg 20, .reg 4,
     .reg 32, .reg 33, .reg 26, .reg 27, .reg 25, .reg 28] ;;
  .assign 43 (.load (.reg 42)) ;;
  .store (.bin .add (.reg 40) (.reg 43)) (.reg 25) ;;
  .store (.bin .add (.reg 41) (.reg 43)) (.reg 31) ;;
  .store (.reg 42) (.bin .add (.reg 43) (.const 1))

/-- Logging `T_H`-closure procedure (`args = [b, u, rootsBuf, fDelBuf, cntPtr]`, returning `0`). -/
def compLogAddOrigRootProc (idxMinUp idxDgDel idxBFS : ℕ) : Stmt :=
  .assign 40 (.reg 2) ;;
  .assign 41 (.reg 3) ;;
  .assign 42 (.reg 4) ;;
  addOrigRootHdrStmt ;;
  .cond (.load (.bin .add (.reg 10) (.reg 1)))
    (.ret (.const 0))
    (addOrigRootSetupStmt ;;
     addOrigRootClimbStmt ;;
     .loop (.reg 23) (compLogPopStepStmt idxMinUp idxDgDel idxBFS) ;;
     .ret (.const 0))

lemma compLogAddOrigRootProc_noRand (idxMinUp idxDgDel idxBFS : ℕ) :
    (compLogAddOrigRootProc idxMinUp idxDgDel idxBFS).NoRand := by
  dsimp [compLogAddOrigRootProc, addOrigRootHdrStmt, addOrigRootSetupStmt, addOrigRootClimbStmt,
    compLogPopStepStmt]
  trivial

/-- Log-buffer address separation predicate: `cntPtr`, `[rootsBuf, rootsBuf + cap)`, and
`[fDelBuf, fDelBuf + cap)` are pairwise disjoint, lie outside `[b, endAddr)`, and fit in `w` bits. -/
def CutLogBufOk (w b endAddr rootsBuf fDelBuf cntPtr cap : ℕ) : Prop :=
  (cntPtr < b ∨ endAddr ≤ cntPtr) ∧
  (rootsBuf + cap ≤ b ∨ endAddr ≤ rootsBuf) ∧
  (fDelBuf + cap ≤ b ∨ endAddr ≤ fDelBuf) ∧
  (rootsBuf + cap ≤ fDelBuf ∨ fDelBuf + cap ≤ rootsBuf) ∧
  (cntPtr < rootsBuf ∨ rootsBuf + cap ≤ cntPtr) ∧
  (cntPtr < fDelBuf ∨ fDelBuf + cap ≤ cntPtr) ∧
  rootsBuf + cap < 2 ^ w ∧ fDelBuf + cap < 2 ^ w ∧ cntPtr < 2 ^ w ∧ cap < 2 ^ w

/-! ## 4. Abstracted pop-cut prefix exposing `regs2 31 = cutE` and `regs2 40..42` -/

/-- Variant of `addOrigRootPopCut_seq_le` that also exposes `regs2 31 = cutE` and preserves
registers `40, 41, 42` for downstream cut logging. -/
lemma compLogPopCut_seq_le
    {w b idxMinUp idxDgDel auxPtr tPtr dgFPtr fAncPtr vCap eCapF n0 tM
     restLen zIdx z oldCid rC oldSize rOrig rOrigIdx cutE a b' rCnt k B : ℕ}
    {p : Program} {ω : ℕ → Bool} {S : LSFState} {vList tOrigList : List ℕ}
    {st : State} {tail : Stmt} {Q : Outcome → State → Prop}
    (hw16 : 16 ≤ 2 ^ w) (h24_ltw : 24 < 2 ^ w)
    (h_dgF_fAnc : dgFPtr + dynGraphSize vCap eCapF ≤ fAncPtr)
    (haux_ltw : auxPtr + auxSize vCap n0 < 2 ^ w) (ht_ltw : tPtr < 2 ^ w)
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
      (∀ r, r ≤ 21 ∨ r = 36 ∨ r = 37 ∨ 40 ≤ r → regs2 r = st.regs r) →
      regs2 23 = restLen → regs2 25 = z → regs2 26 = oldCid → regs2 27 = rC →
      regs2 28 = oldSize → regs2 31 = cutE → regs2 32 = a → regs2 33 = b' →
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
  refine runs_seq_call_le hMinUp (by eval_expr)
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega) hpre_min ?_
  intro ret_min mem_min pos_min hpost_min
  rcases hpost_min with ⟨_, _, _, _, _, _, _, hargs_m, rfl, hret_min⟩
  simp only [List.cons.injEq, and_true] at hargs_m
  rcases hargs_m with ⟨-, -, -, -, -, hz_m, hr_m⟩
  rw [← hz_m, ← hr_m, hcut_def] at hret_min; subst ret_min
  refine runs_seq_assign_le (v := a) (Expr.eval_load_of_eq
    (Expr.eval_bin (by eval_expr) (Expr.eval_load_of_eq (by eval_expr) rfl)
      (by dsimp [BinOp.eval]; omega)) ha_read) ?_; dsimp only
  refine runs_seq_assign_le (v := b') (Expr.eval_load_of_eq
    (Expr.eval_bin (by eval_expr) (Expr.eval_load_of_eq (by eval_expr) rfl)
      (by dsimp [BinOp.eval]; omega)) hb_read) ?_; dsimp only
  refine runs_seq_call_le hDgDel (by eval_expr)
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl <;> omega) hpre_del ?_
  intro v_del mem1 pos1 hpost_del
  rcases hpost_del with ⟨_, _, hargs_d, _, hdgF1_raw, hfr1⟩
  simp only [List.cons.injEq, and_true] at hargs_d
  rcases hargs_d with ⟨rfl, rfl⟩
  have hmem1_rcnt : mem1 (fAncPtr + fOffRCount) = rCnt := (hfr1 _ (Or.inr (by omega))).trans hRcnt_mem
  let regs1 : ℕ → ℕ := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update st.regs
        23 restLen) 24 zIdx) 25 z) 26 oldCid) 27 rC) 28 oldSize) 29 rOrig)
      30 rOrigIdx) 31 cutE) 32 a) 33 b') 34 v_del
  have hreg1_lo : ∀ r, r ≤ 21 ∨ r = 36 ∨ r = 37 ∨ 40 ≤ r → regs1 r = st.regs r := fun r hr => by
    dsimp only [regs1]; clear * - hr
    rw [Function.update_of_ne (by omega : r ≠ 34), Function.update_of_ne (by omega : r ≠ 33),
      Function.update_of_ne (by omega : r ≠ 32), Function.update_of_ne (by omega : r ≠ 31),
      Function.update_of_ne (by omega : r ≠ 30), Function.update_of_ne (by omega : r ≠ 29),
      Function.update_of_ne (by omega : r ≠ 28), Function.update_of_ne (by omega : r ≠ 27),
      Function.update_of_ne (by omega : r ≠ 26), Function.update_of_ne (by omega : r ≠ 25),
      Function.update_of_ne (by omega : r ≠ 24), Function.update_of_ne (by omega : r ≠ 23)]
  have hr1_25 : regs1 25 = z := by
    dsimp only [regs1]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self]
  refine addOrigRootPopUpdate_seq_le hw16 h24_ltw hisr_z_ltw hf_rcnt_ltw hrL_cnt_ltw hb_rcnt_ltw
    hrcnt1_ltw ((hreg1_lo 0 (by decide)).trans hr0) ((hreg1_lo 8 (by decide)).trans hr8)
    ((hreg1_lo 10 (by decide)).trans hr10) ((hreg1_lo 16 (by decide)).trans hr16) hr1_25 hmem1_rcnt ?_
  obtain ⟨o, st', c, hrun_t, hq_t, hc_t⟩ := hcont mem1 pos1 (Function.update regs1 35 rCnt)
    hdgF1_raw hfr1
    (fun r hr => (Function.update_of_ne (by clear * - hr; omega : r ≠ 35) _ _).trans (hreg1_lo r hr))
    (by rw [Function.update_of_ne (by decide)]; dsimp only [regs1]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_self])
    ((Function.update_of_ne (by decide) _ _).trans hr1_25)
    (by rw [Function.update_of_ne (by decide)]; dsimp only [regs1]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_self])
    (by rw [Function.update_of_ne (by decide)]; dsimp only [regs1]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_self])
    (by rw [Function.update_of_ne (by decide)]; dsimp only [regs1]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_self])
    (by rw [Function.update_of_ne (by decide)]; dsimp only [regs1]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_self])
    (by rw [Function.update_of_ne (by decide)]; dsimp only [regs1]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_self])
    (by rw [Function.update_of_ne (by decide)]; dsimp only [regs1]
        rw [Function.update_of_ne (by decide), Function.update_self])
  refine ⟨o, st', c, hrun_t, hq_t, ?_⟩
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
    exact hL (auxLogCap n0)) c).trans hc_t

end

end MinCostFlow.SparseCore.Program
