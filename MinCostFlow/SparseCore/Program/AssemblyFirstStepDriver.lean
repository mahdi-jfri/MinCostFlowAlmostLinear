module

public import WordRAM.Logic

import WordRAM.Tactic

/-!
# The driver of the first step (`AssemblyFirstStepDriver`)

The first step of a branch of the sparse core (the step of Section 6 of the paper that updates
the bundles, the spanners and the tour of a branch after a batch) runs four phases, one after
the other, each from the heap pointer that the one before returns. This file gives the procedure
that calls them and its run from the runs of the four calls.

The procedure has the arguments of the step, `[b, batch, words, edits, editWords, chg, spPtr, h]`
(the layout of `AsmBrCoreStepAt`). It reads from the branch record at `b` the side record
`restH` (at `b + 4`), the tour `tourH` (at `b + 3`), the caps `vCap` and `eCap` (at `b + 5` and
`b + 6`), the read record (at `b`, whose cell `6` holds the graph), the embedding (at `b + 1`)
and the output graph (at `b + 2`). From the side record it reads the bundle table (cell `0`), the
spanner table (cell `1`), the slot count (cell `3`), the slot cap (cell `4`), the component map
(cell `12`) and the component table (cell `14`). Then:
1. Phase 1 scans the batch from `h + 6`. It writes the counts of the new components and of the
   deleted edges at `h + 6` and `h + 7`, the new components at `h + 9 + 2 eCap + vCap` and the
   deleted edges `4 words` cells later.
2. Phase 2 activates the new components. The slot count it leaves is the end `hi` of the new
   slots, whose start `lo` is the slot count before.
3. Phase 3 runs the bundles and the tour. At the heap pointer it starts from, it writes the place
   of the split lists and the place of the descriptors of the touched slots.
4. Phase 4 runs the spanners and writes the record of the step at `h`, except the split lists.
Last, the procedure writes the place of the split lists at `h + 1`.

* `asmFirstStepMainStmt`: the procedure;
* `asmFirstStepMain_run_of`: its run from the runs of the four calls;
* `asmFirstStepDriverStmt`, `asmFirstStepDriver_run_zero`, `asmFirstStepDriver_run_main`: the
  step may call a separate procedure when `eCap = 0`. No phase needs `0 < eCap`, so the
  step calls the same procedure in both cases (`asmFirstStepDriver_run_self`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM

/-! ## The procedures -/

@[expose] public section

/-- The place of the new components of Phase 1, `h + 9 + 2 eCap + vCap`, from registers `7`
(`h`), `11` (`eCap`) and `10` (`vCap`). -/
def asmFirstStepNewCompsE : Expr :=
  .bin .add (.bin .add (.bin .add (.reg 7) (.const 9)) (.bin .mul (.const 2) (.reg 11))) (.reg 10)

/-- **The first step when `eCap ≠ 0`**, `[b, batch, words, edits, editWords, chg, spPtr, h]`.
Registers `8` to `20` hold what it reads before Phase 1: `restH`, `tourH`, `vCap`, `eCap`, the
read record and then the graph, the component map, the component table, the slot count `lo`, the bundle table, the slot
cap, the spanner table, the embedding, and the output graph and then its edge flags. Registers `21`,
`24`, `26` and `30` hold the values that the four phases return. -/
def asmFirstStepMainStmt (fScan fNewAct fP3 fP4 : ℕ) : Stmt :=
  .assign 8 (.load (.bin .add (.reg 0) (.const 4))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const 5))) ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const 6))) ;;
  .assign 12 (.load (.reg 0)) ;;
  .assign 12 (.load (.bin .add (.reg 12) (.const 6))) ;;
  .assign 13 (.load (.bin .add (.reg 8) (.const 12))) ;;
  .assign 14 (.load (.bin .add (.reg 8) (.const 14))) ;;
  .assign 15 (.load (.bin .add (.reg 8) (.const 3))) ;;
  .assign 16 (.load (.reg 8)) ;;
  .assign 17 (.load (.bin .add (.reg 8) (.const 4))) ;;
  .assign 18 (.load (.bin .add (.reg 8) (.const 1))) ;;
  .assign 19 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 20 (.load (.bin .add (.reg 0) (.const 2))) ;;
  .assign 20 (.load (.reg 20)) ;;
  .assign 20 (.bin .add (.bin .add (.reg 20) (.const 4)) (.bin .mul (.const 7) (.reg 10))) ;;
  .call 21 fScan [.reg 12, .reg 13, .reg 14, .reg 1, .reg 2, .reg 10, .reg 11,
    .bin .add (.reg 7) (.const 6)] ;;
  .assign 22 (.load (.bin .add (.reg 7) (.const 6))) ;;
  .assign 23 (.load (.bin .add (.reg 7) (.const 7))) ;;
  .call 24 fNewAct [.reg 8, .reg 9, asmFirstStepNewCompsE, .reg 22, .reg 21] ;;
  .assign 25 (.load (.bin .add (.reg 8) (.const 3))) ;;
  .call 26 fP3 [.reg 16, .reg 17, .reg 10, .reg 9, .reg 1, .reg 2, .reg 3, .reg 4, .reg 6,
    .bin .add asmFirstStepNewCompsE (.bin .mul (.const 4) (.reg 2)), .reg 23, .reg 24] ;;
  .assign 27 (.load (.reg 24)) ;;
  .assign 28 (.load (.bin .add (.reg 24) (.const 1))) ;;
  .assign 29 (.load (.reg 28)) ;;
  .call 30 fP4 [.reg 18, .bin .add (.reg 28) (.const 1), .reg 29, .reg 26, .reg 11, .reg 20,
    .reg 19, .reg 15, .reg 25, .reg 1, .reg 5, .reg 21, .reg 22, .reg 9, .reg 6, .reg 3,
    .reg 7] ;;
  .store (.bin .add (.reg 7) (.const 1)) (.reg 27) ;;
  .ret (.reg 30)

/-- **The first step**, `[b, batch, words, edits, editWords, chg, spPtr, h]`. It calls `fZero`
when the edge cap at `b + 6` is `0` and `fMain` otherwise, with the same arguments. -/
def asmFirstStepDriverStmt (fMain fZero : ℕ) : Stmt :=
  .cond (.bin .eq (.load (.bin .add (.reg 0) (.const 6))) (.const 0))
    (.call 8 fZero [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7] ;;
      .ret (.reg 8))
    (.call 8 fMain [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7] ;;
      .ret (.reg 8))

end

public section

theorem asmFirstStepMainStmt_noRand (fScan fNewAct fP3 fP4 : ℕ) :
    (asmFirstStepMainStmt fScan fNewAct fP3 fP4).NoRand := by
  simp [asmFirstStepMainStmt, Stmt.NoRand]

theorem asmFirstStepDriverStmt_noRand (fMain fZero : ℕ) :
    (asmFirstStepDriverStmt fMain fZero).NoRand := by
  simp [asmFirstStepDriverStmt, Stmt.NoRand]

end

/-! ## The runs -/

/-- A call followed by a statement, with the cost bound carried along. -/
private theorem drv_runs_seq_callRuns_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ}
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

/-- **The run of `asmFirstStepMainStmt` from the runs of its four calls.** The facts `hm_*` give
the cells that the procedure reads, each in the memory at the time it reads it. Each phase
starts from the memory and the heap pointer that the one before leaves. The procedure ends by
writing the place of the split lists at `h + 1`. -/
theorem asmFirstStepMain_run_of {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {fScan fNewAct fP3 fP4 : ℕ} {bScan bNewAct bP3 bP4 : Stmt}
    (hf₁ : p.procs[fScan]? = some bScan) (hf₂ : p.procs[fNewAct]? = some bNewAct)
    (hf₃ : p.procs[fP3]? = some bP3) (hf₄ : p.procs[fP4]? = some bP4)
    {b batch words edits editWords chg spPtr h pos : ℕ}
    {restH tourH vCap eCap rd gPtr cmpH ctH lo bunH slotCap spanTbl embH outH g : ℕ}
    {nNew nDel hi splitPtr descPtr nT : ℕ} {mem₀ : ℕ → ℕ}
    (hm_rest : mem₀ (b + 4) = restH) (hm_tour : mem₀ (b + 3) = tourH)
    (hm_v : mem₀ (b + 5) = vCap) (hm_e : mem₀ (b + 6) = eCap) (hm_rd : mem₀ b = rd)
    (hm_g : mem₀ (rd + 6) = gPtr) (hm_cmp : mem₀ (restH + 12) = cmpH)
    (hm_ct : mem₀ (restH + 14) = ctH) (hm_lo : mem₀ (restH + 3) = lo)
    (hm_bun : mem₀ restH = bunH) (hm_sc : mem₀ (restH + 4) = slotCap)
    (hm_span : mem₀ (restH + 1) = spanTbl) (hm_emb : mem₀ (b + 1) = embH)
    (hm_out : mem₀ (b + 2) = outH) (hm_og : mem₀ outH = g)
    (hw16 : 16 ≤ 2 ^ w) (hb_w : b + 6 < 2 ^ w) (hrd_w : rd + 6 < 2 ^ w)
    (hrest_w : restH + 14 < 2 ^ w) (hg_w : g + 4 + 7 * vCap < 2 ^ w)
    (hh_w : h + 9 + 2 * eCap + vCap + 4 * words < 2 ^ w)
    {o₁ o₂ o₃ o₄ : Outcome} {st₁ st₂ st₃ st₄ : State} {c₁ c₂ c₃ c₄ : ℕ}
    (hr₁ : Runs w p ω bScan
      (startState [gPtr, cmpH, ctH, batch, words, vCap, eCap, h + 6] mem₀ pos) o₁ st₁ c₁)
    (hm_nNew : st₁.mem (h + 6) = nNew) (hm_nDel : st₁.mem (h + 7) = nDel)
    (hr₂ : Runs w p ω bNewAct (startState [restH, tourH, h + 9 + 2 * eCap + vCap, nNew,
      o₁.value] st₁.mem st₁.pos) o₂ st₂ c₂)
    (hm_hi : st₂.mem (restH + 3) = hi)
    (hr₃ : Runs w p ω bP3 (startState [bunH, slotCap, vCap, tourH, batch, words, edits,
      editWords, spPtr, h + 9 + 2 * eCap + vCap + 4 * words, nDel, o₂.value] st₂.mem st₂.pos)
      o₃ st₃ c₃)
    (hm_sp : st₃.mem o₂.value = splitPtr) (hm_desc : st₃.mem (o₂.value + 1) = descPtr)
    (hm_nT : st₃.mem descPtr = nT)
    (ho₂_w : o₂.value + 1 < 2 ^ w) (hdesc_w : descPtr + 1 < 2 ^ w)
    (hr₄ : Runs w p ω bP4 (startState [spanTbl, descPtr + 1, nT, o₃.value, eCap,
      g + 4 + 7 * vCap, embH, lo, hi, batch, chg, o₁.value, nNew, tourH, spPtr, edits, h]
      st₃.mem st₃.pos) o₄ st₄ c₄) :
    ∃ st' c, Runs w p ω (asmFirstStepMainStmt fScan fNewAct fP3 fP4)
        (startState [b, batch, words, edits, editWords, chg, spPtr, h] mem₀ pos)
        (.returned o₄.value) st' c ∧
      st'.mem = Function.update st₄.mem (h + 1) splitPtr ∧
      c ≤ c₁ + c₂ + c₃ + c₄ + 300 := by
  have key : ∃ o st' c, Runs w p ω (asmFirstStepMainStmt fScan fNewAct fP3 fP4)
      (startState [b, batch, words, edits, editWords, chg, spPtr, h] mem₀ pos) o st' c ∧
      (o = .returned o₄.value ∧ st'.mem = Function.update st₄.mem (h + 1) splitPtr) ∧
      0 + c ≤ c₁ + c₂ + c₃ + c₄ + 300 := by
    unfold asmFirstStepMainStmt asmFirstStepNewCompsE
    refine runs_seq_assign_le (v := restH) (by eval_expr) ?_
    refine runs_seq_assign_le (v := tourH) (by eval_expr) ?_
    refine runs_seq_assign_le (v := vCap) (by eval_expr) ?_
    refine runs_seq_assign_le (v := eCap) (by eval_expr) ?_
    refine runs_seq_assign_le (v := rd) (by eval_expr) ?_
    refine runs_seq_assign_le (v := gPtr) (by eval_expr) ?_
    refine runs_seq_assign_le (v := cmpH) (by eval_expr) ?_
    refine runs_seq_assign_le (v := ctH) (by eval_expr) ?_
    refine runs_seq_assign_le (v := lo) (by eval_expr) ?_
    refine runs_seq_assign_le (v := bunH) (by eval_expr) ?_
    refine runs_seq_assign_le (v := slotCap) (by eval_expr) ?_
    refine runs_seq_assign_le (v := spanTbl) (by eval_expr) ?_
    refine runs_seq_assign_le (v := embH) (by eval_expr) ?_
    refine runs_seq_assign_le (v := outH) (by eval_expr) ?_
    refine runs_seq_assign_le (v := g) (by eval_expr) ?_
    refine runs_seq_assign_le (v := g + 4 + 7 * vCap) (by eval_expr) ?_
    refine drv_runs_seq_callRuns_le (by eval_expr) hf₁ hr₁ ?_
    refine runs_seq_assign_le (v := nNew) (by eval_expr) ?_
    refine runs_seq_assign_le (v := nDel) (by eval_expr) ?_
    refine drv_runs_seq_callRuns_le (by eval_expr) hf₂ hr₂ ?_
    refine runs_seq_assign_le (v := hi) (by eval_expr) ?_
    refine drv_runs_seq_callRuns_le (by eval_expr) hf₃ hr₃ ?_
    refine runs_seq_assign_le (v := splitPtr) (by eval_expr) ?_
    refine runs_seq_assign_le (v := descPtr) (by eval_expr) ?_
    refine runs_seq_assign_le (v := nT) (by eval_expr) ?_
    refine drv_runs_seq_callRuns_le (by eval_expr) hf₄ hr₄ ?_
    refine runs_seq_store_le (x := h + 1) (v := splitPtr) (by eval_expr) (by eval_expr) ?_
    wram_step
    · exact ⟨by simp, rfl⟩
    · wram_cost
  obtain ⟨o, st', c, hr, ⟨rfl, hm⟩, hc⟩ := key
  exact ⟨st', c, hr, hm, by omega⟩

/-- **The run of the first step when `eCap = 0`**: the run of the call of `fZero`. -/
theorem asmFirstStepDriver_run_zero {w : ℕ} {p : Program} {ω : ℕ → Bool} {fMain fZero : ℕ}
    {bZero : Stmt} (hf : p.procs[fZero]? = some bZero)
    {b batch words edits editWords chg spPtr h pos : ℕ} {mem₀ : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hb_w : b + 6 < 2 ^ w) (hm_e : mem₀ (b + 6) = 0)
    {o : Outcome} {st : State} {c : ℕ}
    (hr : Runs w p ω bZero (startState [b, batch, words, edits, editWords, chg, spPtr, h] mem₀
      pos) o st c) :
    ∃ st' c', Runs w p ω (asmFirstStepDriverStmt fMain fZero)
        (startState [b, batch, words, edits, editWords, chg, spPtr, h] mem₀ pos)
        (.returned o.value) st' c' ∧ st'.mem = st.mem ∧ c' ≤ c + 40 := by
  have key : ∃ o' st' c', Runs w p ω (asmFirstStepDriverStmt fMain fZero)
      (startState [b, batch, words, edits, editWords, chg, spPtr, h] mem₀ pos) o' st' c' ∧
      (o' = .returned o.value ∧ st'.mem = st.mem) ∧ 0 + c' ≤ c + 40 := by
    unfold asmFirstStepDriverStmt
    refine runs_cond_le (Expr.eval_eq_op (x := 0) (y := 0) (by eval_expr) (by eval_expr)
      (by omega)) (fun _ => ?_) (fun h0 => absurd h0 (by simp))
    refine drv_runs_seq_callRuns_le (by eval_expr) hf hr ?_
    wram_step
    · exact ⟨by simp, rfl⟩
    · wram_cost
  obtain ⟨o', st', c', hr', ⟨rfl, hm⟩, hc⟩ := key
  exact ⟨st', c', hr', hm, by omega⟩

/-- **The run of the first step when `eCap ≠ 0`**: the run of the call of `fMain`. -/
theorem asmFirstStepDriver_run_main {w : ℕ} {p : Program} {ω : ℕ → Bool} {fMain fZero : ℕ}
    {bMain : Stmt} (hf : p.procs[fMain]? = some bMain)
    {b batch words edits editWords chg spPtr h pos eCap : ℕ} {mem₀ : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hb_w : b + 6 < 2 ^ w) (hm_e : mem₀ (b + 6) = eCap)
    (heCap : eCap ≠ 0)
    {o : Outcome} {st : State} {c : ℕ}
    (hr : Runs w p ω bMain (startState [b, batch, words, edits, editWords, chg, spPtr, h] mem₀
      pos) o st c) :
    ∃ st' c', Runs w p ω (asmFirstStepDriverStmt fMain fZero)
        (startState [b, batch, words, edits, editWords, chg, spPtr, h] mem₀ pos)
        (.returned o.value) st' c' ∧ st'.mem = st.mem ∧ c' ≤ c + 40 := by
  have key : ∃ o' st' c', Runs w p ω (asmFirstStepDriverStmt fMain fZero)
      (startState [b, batch, words, edits, editWords, chg, spPtr, h] mem₀ pos) o' st' c' ∧
      (o' = .returned o.value ∧ st'.mem = st.mem) ∧ 0 + c' ≤ c + 40 := by
    unfold asmFirstStepDriverStmt
    refine runs_cond_le (Expr.eval_eq_op (x := eCap) (y := 0) (by eval_expr) (by eval_expr)
      (by omega)) (fun h0 => absurd h0 (by simp [heCap])) (fun _ => ?_)
    refine drv_runs_seq_callRuns_le (by eval_expr) hf hr ?_
    wram_step
    · exact ⟨by simp, rfl⟩
    · wram_cost
  obtain ⟨o', st', c', hr', ⟨rfl, hm⟩, hc⟩ := key
  exact ⟨st', c', hr', hm, by omega⟩

/-- **The run of the first step when both branches call `fMain`**: the run of the call of
`fMain`, for every edge cap. It is `asmFirstStepDriver_run_zero` when the cell `b + 6` holds `0`,
and `asmFirstStepDriver_run_main` otherwise. -/
theorem asmFirstStepDriver_run_self {w : ℕ} {p : Program} {ω : ℕ → Bool} {fMain : ℕ}
    {bMain : Stmt} (hf : p.procs[fMain]? = some bMain)
    {b batch words edits editWords chg spPtr h pos : ℕ} {mem₀ : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hb_w : b + 6 < 2 ^ w)
    {o : Outcome} {st : State} {c : ℕ}
    (hr : Runs w p ω bMain (startState [b, batch, words, edits, editWords, chg, spPtr, h] mem₀
      pos) o st c) :
    ∃ st' c', Runs w p ω (asmFirstStepDriverStmt fMain fMain)
        (startState [b, batch, words, edits, editWords, chg, spPtr, h] mem₀ pos)
        (.returned o.value) st' c' ∧ st'.mem = st.mem ∧ c' ≤ c + 40 := by
  by_cases h0 : mem₀ (b + 6) = 0
  · exact asmFirstStepDriver_run_zero hf hw16 hb_w h0 hr
  · exact asmFirstStepDriver_run_main hf hw16 hb_w rfl h0 hr

end

end MinCostFlow.SparseCore.Program
