module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4Model
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4Lists
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4Reemb

import WordRAM.Tactic

/-!
# Phase 4 of the first step: the procedure (`AssemblyFirstStepPhase4Defs`)

Phase 4 runs the spanners of the step and builds what the output step needs. The procedure
`asmFirstPhase4Stmt fSelP fLists fRot fReemb` has the arguments of the front of Phase 4,
`[spanTbl, descPtr, n, hp, eCap, oldS, embH, lo, hi, batch, chg, lazyPtr, nNew]`, then
`[tourH, spPtr, edits, rec]`. It calls four procedures, each with the heap pointer that the one
before returns:
1. `asmFirstP4SelStmt`: the front (spanner updates, workspace, seeds) and the three selectors.
   It returns `h₁ + 6 eCap`, and the selectors lie at `h₁ + 3 eCap`, `h₁ + 4 eCap`,
   `h₁ + 5 eCap`;
2. `asmFirstP4ListsStmt`: the delete list and the insert list, with their places at
   `h₁ + 6 eCap` and `h₁ + 6 eCap + 1`;
3. `asmFirstP4RotStmt`: the list `T₀`, with its place at the heap pointer `o₂` it starts from;
4. `asmFirstP4ReembStmt`: the re-embedded list, with its place at the heap pointer `o₃` it
   starts from.
Then it writes the places into the record of the step at `rec` (the layout of
`AsmBrCoreStepAt`): the delete list at `rec`, the insert list at `rec + 2`, `T₀` at `rec + 3`,
the re-embedded list at `rec + 4` and its length at `rec + 5`. The place `rec + 1` of the split
lists is left to Phase 3.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM

/-! ## The procedure -/

@[expose] public section

/-- **Phase 4 of the first step**, `[spanTbl, descPtr, n, hp, eCap, oldS, embH, lo, hi, batch,
chg, lazyPtr, nNew, tourH, spPtr, edits, rec]`. Registers `17` to `20` hold the values that the
four calls return, register `21` holds `h₁`, and registers `22` to `26` the five words of the
record. -/
def asmFirstPhase4Stmt (fSelP fLists fRot fReemb : ℕ) : Stmt :=
  .call 17 fSelP [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
    .reg 10, .reg 11, .reg 12] ;;
  .assign 21 (.bin .sub (.reg 17) (.bin .mul (.const 6) (.reg 4))) ;;
  .call 18 fLists [.reg 13, .bin .add (.reg 3) (.bin .mul (.const 6) (.reg 4)),
    .load (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 10) (.reg 4))) (.const 1)),
    .bin .add (.reg 21) (.bin .mul (.const 5) (.reg 4)),
    .bin .add (.reg 3) (.bin .mul (.const 4) (.reg 4)),
    .load (.bin .add (.reg 3) (.bin .mul (.const 10) (.reg 4))),
    .bin .add (.reg 21) (.bin .mul (.const 3) (.reg 4)),
    .bin .add (.reg 21) (.bin .mul (.const 4) (.reg 4)), .reg 4, .reg 6, .reg 17] ;;
  .call 19 fRot [.reg 13, .reg 14, .load (.bin .add (.reg 17) (.const 1)), .reg 9, .reg 15,
    .reg 18] ;;
  .call 20 fReemb [.bin .add (.reg 3) (.bin .mul (.const 8) (.reg 4)),
    .load (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 10) (.reg 4))) (.const 2)),
    .load (.reg 17), .reg 19] ;;
  .assign 22 (.load (.reg 17)) ;;
  .assign 23 (.load (.bin .add (.reg 17) (.const 1))) ;;
  .assign 24 (.load (.reg 18)) ;;
  .assign 25 (.load (.reg 19)) ;;
  .assign 26 (.load (.reg 25)) ;;
  .store (.reg 16) (.reg 22) ;;
  .store (.bin .add (.reg 16) (.const 2)) (.reg 23) ;;
  .store (.bin .add (.reg 16) (.const 3)) (.reg 24) ;;
  .store (.bin .add (.reg 16) (.const 4)) (.bin .add (.reg 25) (.const 1)) ;;
  .store (.bin .add (.reg 16) (.const 5)) (.reg 26) ;;
  .ret (.reg 20)

/-- The memory after the record of Phase 4 is written into `mem` at `rec`, from the places of
the delete list at `hL`, of the insert list at `hL + 1`, of `T₀` at `hR`, and of the
re-embedded list at `hE`. -/
def p4RecordMem (mem : ℕ → ℕ) (rec hL hR hE : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update mem
    rec (mem hL)) (rec + 2) (mem (hL + 1))) (rec + 3) (mem hR)) (rec + 4) (mem hE + 1)) (rec + 5)
    (mem (mem hE))

end

public section

theorem asmFirstPhase4Stmt_noRand (fSelP fLists fRot fReemb : ℕ) :
    (asmFirstPhase4Stmt fSelP fLists fRot fReemb).NoRand := by
  simp [asmFirstPhase4Stmt, Stmt.NoRand]

/-- The record memory agrees with `mem` outside `[rec, rec + 6)`. -/
theorem p4RecordMem_of_ne {mem : ℕ → ℕ} {rec hL hR hE x : ℕ} (hx : x < rec ∨ rec + 6 ≤ x) :
    p4RecordMem mem rec hL hR hE x = mem x := by
  unfold p4RecordMem
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega)]

end

/-! ## The run from the runs of the four calls -/

/-- A call followed by a statement, with the cost bound carried along. -/
private theorem p4c_runs_seq_callRuns_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ}
    {args : List Expr} {s : Stmt} {st : State} {vs : List ℕ} {body : Stmt} {k T : ℕ}
    {Q : Outcome → State → Prop}
    (hargs : evalArgs w st args = some vs) (hb : p.procs[f]? = some body) {o₁ : Outcome}
    {st₁ : State} {c₁ : ℕ}
    (h₁ : Runs w p ω body (startState vs st.mem st.pos) o₁ st₁ c₁)
    (hrest : ∃ o st' c₂, Runs w p ω s { st₁ with regs := Function.update st.regs r o₁.value }
      o st' c₂ ∧ Q o st' ∧ (k + argsSize args + c₁ + 2) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f args) s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o, st', c₂, hr₂, hq, hc⟩ := hrest
  exact ⟨o, st', (argsSize args + c₁ + 1) + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨_, _, c₂,
    runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hb, h₁, rfl, rfl, rfl⟩, hr₂, rfl⟩), hq,
    by omega⟩

public section

/-- **The run of `asmFirstPhase4Stmt` from the runs of its four calls.** Each call starts from
the memory and the heap pointer that the one before leaves. The record is written last. -/
theorem asmFirstPhase4_run_of {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {fSelP fLists fRot fReemb : ℕ} {bSel bLists bRot bReemb : Stmt}
    (hf₁ : p.procs[fSelP]? = some bSel) (hf₂ : p.procs[fLists]? = some bLists)
    (hf₃ : p.procs[fRot]? = some bRot) (hf₄ : p.procs[fReemb]? = some bReemb)
    {spanTbl descPtr n hp eCap oldS embH lo hi batch chg lazyPtr nNew tourH spPtr edits rec
      pos h₁ nIns nDel insP nR delP : ℕ} {mem₀ : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hsz : h₁ + 6 * eCap + 1 < 2 ^ w) (hws : hp + 10 * eCap + 2 < 2 ^ w)
    (hrec : rec + 5 < 2 ^ w)
    {o₁ o₂ o₃ o₄ : Outcome} {st₁ st₂ st₃ st₄ : State} {c₁ c₂ c₃ c₄ : ℕ}
    (hr₁ : Runs w p ω bSel (startState [spanTbl, descPtr, n, hp, eCap, oldS, embH, lo, hi,
      batch, chg, lazyPtr, nNew] mem₀ pos) o₁ st₁ c₁)
    (ho₁ : o₁.value = h₁ + 6 * eCap)
    (hmI : st₁.mem (hp + 10 * eCap + 1) = nIns) (hmD : st₁.mem (hp + 10 * eCap) = nDel)
    (hr₂ : Runs w p ω bLists (startState [tourH, hp + 6 * eCap, nIns, h₁ + 5 * eCap,
      hp + 4 * eCap, nDel, h₁ + 3 * eCap, h₁ + 4 * eCap, eCap, embH, h₁ + 6 * eCap] st₁.mem
      st₁.pos) o₂ st₂ c₂)
    (hmP : st₂.mem (h₁ + 6 * eCap + 1) = insP)
    (hr₃ : Runs w p ω bRot (startState [tourH, spPtr, insP, batch, edits, o₂.value] st₂.mem
      st₂.pos) o₃ st₃ c₃)
    (hmR : st₃.mem (hp + 10 * eCap + 2) = nR) (hmL : st₃.mem (h₁ + 6 * eCap) = delP)
    (hr₄ : Runs w p ω bReemb (startState [hp + 8 * eCap, nR, delP, o₃.value] st₃.mem st₃.pos)
      o₄ st₄ c₄)
    (hq : st₄.mem o₃.value + 1 < 2 ^ w) :
    ∃ st' c, Runs w p ω (asmFirstPhase4Stmt fSelP fLists fRot fReemb)
        (startState [spanTbl, descPtr, n, hp, eCap, oldS, embH, lo, hi, batch, chg, lazyPtr,
          nNew, tourH, spPtr, edits, rec] mem₀ pos) (.returned o₄.value) st' c ∧
      st'.mem = p4RecordMem st₄.mem rec (h₁ + 6 * eCap) o₂.value o₃.value ∧
      c ≤ c₁ + c₂ + c₃ + c₄ + 250 := by
  have key : ∃ o st' c, Runs w p ω (asmFirstPhase4Stmt fSelP fLists fRot fReemb)
      (startState [spanTbl, descPtr, n, hp, eCap, oldS, embH, lo, hi, batch, chg, lazyPtr,
        nNew, tourH, spPtr, edits, rec] mem₀ pos) o st' c ∧
      (o = .returned o₄.value ∧
        st'.mem = p4RecordMem st₄.mem rec (h₁ + 6 * eCap) o₂.value o₃.value) ∧
      0 + c ≤ c₁ + c₂ + c₃ + c₄ + 250 := by
    unfold asmFirstPhase4Stmt
    refine p4c_runs_seq_callRuns_le (by eval_expr) hf₁ hr₁ ?_
    refine runs_seq_assign_le (v := h₁) ?_ ?_
    · exact Expr.eval_eq_of_eq (Expr.eval_sub (x := o₁.value) (y := 6 * eCap) (by eval_expr)
        (by eval_expr) (by omega)) (by omega)
    refine p4c_runs_seq_callRuns_le (by eval_expr) hf₂ hr₂ ?_
    refine p4c_runs_seq_callRuns_le (by eval_expr) hf₃ hr₃ ?_
    refine p4c_runs_seq_callRuns_le (by eval_expr) hf₄ hr₄ ?_
    refine runs_seq_assign_le (v := st₄.mem (h₁ + 6 * eCap)) (by eval_expr) ?_
    refine runs_seq_assign_le (v := st₄.mem (h₁ + 6 * eCap + 1)) (by eval_expr) ?_
    refine runs_seq_assign_le (v := st₄.mem o₂.value) (by eval_expr) ?_
    refine runs_seq_assign_le (v := st₄.mem o₃.value) (by eval_expr) ?_
    refine runs_seq_assign_le (v := st₄.mem (st₄.mem o₃.value)) (by eval_expr) ?_
    refine runs_seq_store_le (x := rec) (v := st₄.mem (h₁ + 6 * eCap)) (by eval_expr)
      (by eval_expr) ?_
    refine runs_seq_store_le (x := rec + 2) (v := st₄.mem (h₁ + 6 * eCap + 1)) (by eval_expr)
      (by eval_expr) ?_
    refine runs_seq_store_le (x := rec + 3) (v := st₄.mem o₂.value) (by eval_expr)
      (by eval_expr) ?_
    refine runs_seq_store_le (x := rec + 4) (v := st₄.mem o₃.value + 1) (by eval_expr)
      (by eval_expr) ?_
    refine runs_seq_store_le (x := rec + 5) (v := st₄.mem (st₄.mem o₃.value)) (by eval_expr)
      (by eval_expr) ?_
    wram_step
    · exact ⟨by simp, rfl⟩
    · wram_cost
  obtain ⟨o, st', c, hr, ⟨rfl, hm⟩, hc⟩ := key
  exact ⟨st', c, hr, hm, by omega⟩

end

end MinCostFlow.SparseCore.Program
