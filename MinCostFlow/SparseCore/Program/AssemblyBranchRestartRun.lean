module

public import MinCostFlow.SparseCore.Program.AssemblyBranchRestartModel

/-!
# The run of the restart program of a branch (`AssemblyBranchRestartRun`)

The program `asmBrRestartStmt` (`AssemblyBranchRestartIface.lean`) reads seven words of the
records of the branch and of the bundle side (and three more as arguments of the first call), and
makes three calls: the restart of P8, the reset
of P7 and the refresh of the embedding table. This file proves that, once the three calls run, the
whole program runs, returns the value of the last call, and costs at most `100` steps more than
the three calls (`asmBrRestartStmt_runs`). The arguments of the calls are the words read from the
records. The second and third calls read one more word of the record of the branch, and the second
call reads the word of the readout data of P10 that points to its graph `S` (`ASM_READ_S`), each in
the memory that the previous call left.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM

/-- **The run of the restart program.** Let the record of the branch be at `b` and the record of
the bundle side at `sd = mem (b + ASM_BR_REST)`. If the restart of P8 runs on the words of the
records, the reset of P7 then runs on the output graph, the tour, the graph `S` of P10 and the end
of the first call, and the refresh then runs on the embedding table, the spanners, the slots and
the end of the second call, then the program runs, returns the end of the third call, ends with
its memory, and costs at most the three calls and `100` steps. -/
theorem asmBrRestartStmt_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {f8 fReset fEmb : ℕ}
    {b b4 j h pos : ℕ} {mem : ℕ → ℕ}
    {body8 bodyR bodyE : Stmt} {o8 oR oE : Outcome} {st8 stR stE : State} {c8 cR cE : ℕ}
    (hb : b + ASM_BR_SIZE < 2 ^ w)
    (hsd : mem (b + ASM_BR_REST) + ASM_SD_SIZE < 2 ^ w)
    (hrd : mem (b + ASM_BR_READ) + ASM_READ_S < 2 ^ w)
    (hf8 : p.procs[f8]? = some body8) (hfR : p.procs[fReset]? = some bodyR)
    (hfE : p.procs[fEmb]? = some bodyE)
    (hrun8 : Runs w p ω body8
      (startState [mem (mem (b + ASM_BR_REST) + ASM_SD_BUN), mem (b + ASM_BR_TOUR),
        mem (mem (b + ASM_BR_REST) + ASM_SD_SPAN), mem (b + ASM_BR_READ),
        mem (mem (b + ASM_BR_REST) + ASM_SD_NSLOTS), mem (mem (b + ASM_BR_REST) + ASM_SD_SLOTS),
        h, b4, j, mem (mem (b + ASM_BR_REST) + ASM_SD_SPLIT),
        mem (mem (b + ASM_BR_REST) + ASM_SD_SPV), mem (mem (b + ASM_BR_REST) + ASM_SD_SPE),
        mem (mem (b + ASM_BR_REST) + ASM_SD_SPL)]
        mem pos) o8 st8 c8)
    (hrunR : Runs w p ω bodyR
      (startState [st8.mem (b + ASM_BR_OUT), mem (b + ASM_BR_TOUR),
        st8.mem (mem (b + ASM_BR_READ) + ASM_READ_S), o8.value] st8.mem st8.pos) oR stR cR)
    (hrunE : Runs w p ω bodyE
      (startState [stR.mem (b + ASM_BR_EMB), mem (mem (b + ASM_BR_REST) + ASM_SD_SPAN),
        mem (mem (b + ASM_BR_REST) + ASM_SD_SLOTS), mem (mem (b + ASM_BR_REST) + ASM_SD_NSLOTS),
        oR.value] stR.mem stR.pos) oE stE cE) :
    ∃ st' c, Runs w p ω (asmBrRestartStmt f8 fReset fEmb) (startState [b, b4, j, h] mem pos)
      (.returned oE.value) st' c ∧ st'.mem = stE.mem ∧ c ≤ c8 + cR + cE + 100 := by
  set sd := mem (b + ASM_BR_REST) with hsddef
  have hw : ∀ k, k ≤ ASM_BR_SIZE → b + k < 2 ^ w := fun k hk => by omega
  have hws : ∀ k, k ≤ ASM_SD_SIZE → sd + k < 2 ^ w := fun k hk => by omega
  have hk : ∀ k, k ≤ ASM_BR_SIZE → k < 2 ^ w := fun k hk => by have := hw k hk; omega
  have hks : ∀ k, k ≤ ASM_SD_SIZE → k < 2 ^ w := fun k hk => by have := hws k hk; omega
  have hk5 : ASM_READ_S < 2 ^ w := by omega
  -- the seven loads
  set st0 := startState [b, b4, j, h] mem pos with hst0
  set r1 := Function.update st0.regs 4 sd with hr1
  set r2 := Function.update r1 5 (mem (sd + ASM_SD_BUN)) with hr2
  set r3 := Function.update r2 6 (mem (b + ASM_BR_TOUR)) with hr3
  set r4 := Function.update r3 7 (mem (sd + ASM_SD_SPAN)) with hr4
  set r5 := Function.update r4 8 (mem (b + ASM_BR_READ)) with hr5
  set r6 := Function.update r5 9 (mem (sd + ASM_SD_NSLOTS)) with hr6
  set r7 := Function.update r6 10 (mem (sd + ASM_SD_SLOTS)) with hr7
  have e1 : (Expr.load (.bin .add (.reg 0) (.const ASM_BR_REST))).eval w st0 = some sd := by
    have h1 := hk ASM_BR_REST (by decide)
    have h2 := hw ASM_BR_REST (by decide)
    simp [Expr.eval, hst0, startState, h1, h2, BinOp.eval, hsddef]
  have e2 : (Expr.load (.bin .add (.reg 4) (.const ASM_SD_BUN))).eval w { st0 with regs := r1 } =
      some (mem (sd + ASM_SD_BUN)) := by
    have h1 := hks ASM_SD_BUN (by decide)
    have h2 := hws ASM_SD_BUN (by decide)
    simp [Expr.eval, hr1, hst0, startState, h1, h2, BinOp.eval]
  have e3 : (Expr.load (.bin .add (.reg 0) (.const ASM_BR_TOUR))).eval w
      { st0 with regs := r2 } = some (mem (b + ASM_BR_TOUR)) := by
    have h1 := hk ASM_BR_TOUR (by decide)
    have h2 := hw ASM_BR_TOUR (by decide)
    simp [Expr.eval, hr2, hr1, hst0, startState, h1, h2, BinOp.eval]
  have e4 : (Expr.load (.bin .add (.reg 4) (.const ASM_SD_SPAN))).eval w
      { st0 with regs := r3 } = some (mem (sd + ASM_SD_SPAN)) := by
    have h1 := hks ASM_SD_SPAN (by decide)
    have h2 := hws ASM_SD_SPAN (by decide)
    simp [Expr.eval, hr3, hr2, hr1, hst0, startState, h1, h2, BinOp.eval]
  have e5 : (Expr.load (.bin .add (.reg 0) (.const ASM_BR_READ))).eval w
      { st0 with regs := r4 } = some (mem (b + ASM_BR_READ)) := by
    have h1 := hk ASM_BR_READ (by decide)
    have h2 := hw ASM_BR_READ (by decide)
    simp [Expr.eval, hr4, hr3, hr2, hr1, hst0, startState, h1, h2, BinOp.eval]
  have e6 : (Expr.load (.bin .add (.reg 4) (.const ASM_SD_NSLOTS))).eval w
      { st0 with regs := r5 } = some (mem (sd + ASM_SD_NSLOTS)) := by
    have h1 := hks ASM_SD_NSLOTS (by decide)
    have h2 := hws ASM_SD_NSLOTS (by decide)
    simp [Expr.eval, hr5, hr4, hr3, hr2, hr1, hst0, startState, h1, h2, BinOp.eval]
  have e7 : (Expr.load (.bin .add (.reg 4) (.const ASM_SD_SLOTS))).eval w
      { st0 with regs := r6 } = some (mem (sd + ASM_SD_SLOTS)) := by
    have h1 := hks ASM_SD_SLOTS (by decide)
    have h2 := hws ASM_SD_SLOTS (by decide)
    simp [Expr.eval, hr6, hr5, hr4, hr3, hr2, hr1, hst0, startState, h1, h2, BinOp.eval]
  -- the three calls
  set s7 : State := { st0 with regs := r7 } with hs7
  have hargs8 : evalArgs w s7 [.reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 3, .reg 1,
      .reg 2, .load (.bin .add (.reg 4) (.const ASM_SD_SPLIT)),
      .load (.bin .add (.reg 4) (.const ASM_SD_SPV)),
      .load (.bin .add (.reg 4) (.const ASM_SD_SPE)),
      .load (.bin .add (.reg 4) (.const ASM_SD_SPL))] = some [mem (sd + ASM_SD_BUN),
        mem (b + ASM_BR_TOUR), mem (sd + ASM_SD_SPAN), mem (b + ASM_BR_READ),
        mem (sd + ASM_SD_NSLOTS), mem (sd + ASM_SD_SLOTS), h, b4, j, mem (sd + ASM_SD_SPLIT),
        mem (sd + ASM_SD_SPV), mem (sd + ASM_SD_SPE), mem (sd + ASM_SD_SPL)] := by
    have h1 := hks ASM_SD_SPLIT (by decide)
    have h2 := hws ASM_SD_SPLIT (by decide)
    have h3 := hks ASM_SD_SPV (by decide)
    have h4 := hws ASM_SD_SPV (by decide)
    have h5 := hks ASM_SD_SPE (by decide)
    have h6 := hws ASM_SD_SPE (by decide)
    have h7 := hks ASM_SD_SPL (by decide)
    have h8 := hws ASM_SD_SPL (by decide)
    simp [evalArgs, Expr.eval, hs7, hr7, hr6, hr5, hr4, hr3, hr2, hr1, hst0, startState, h1, h2,
      h3, h4, h5, h6, h7, h8, BinOp.eval]
  set s8 : State := { st8 with regs := Function.update r7 11 o8.value } with hs8
  have hcall8 : Runs w p ω (.call 11 f8 [.reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 3,
      .reg 1, .reg 2, .load (.bin .add (.reg 4) (.const ASM_SD_SPLIT)),
      .load (.bin .add (.reg 4) (.const ASM_SD_SPV)),
      .load (.bin .add (.reg 4) (.const ASM_SD_SPE)),
      .load (.bin .add (.reg 4) (.const ASM_SD_SPL))]) s7 .normal s8
      (argsSize [.reg 5, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 3, .reg 1, .reg 2,
        .load (.bin .add (.reg 4) (.const ASM_SD_SPLIT)),
        .load (.bin .add (.reg 4) (.const ASM_SD_SPV)),
        .load (.bin .add (.reg 4) (.const ASM_SD_SPE)),
        .load (.bin .add (.reg 4) (.const ASM_SD_SPL))] + c8 + 1) :=
    runs_call_iff.mpr ⟨_, body8, o8, st8, c8, hargs8, hf8, hrun8, rfl, rfl, rfl⟩
  have hargsR : evalArgs w s8 [.load (.bin .add (.reg 0) (.const ASM_BR_OUT)), .reg 6,
      .load (.bin .add (.reg 8) (.const ASM_READ_S)), .reg 11] =
      some [st8.mem (b + ASM_BR_OUT), mem (b + ASM_BR_TOUR),
        st8.mem (mem (b + ASM_BR_READ) + ASM_READ_S), o8.value] := by
    have h1 := hk ASM_BR_OUT (by decide)
    have h2 := hw ASM_BR_OUT (by decide)
    simp [evalArgs, Expr.eval, hs8, hr7, hr6, hr5, hr4, hr3, hr2, hr1, hst0, startState, h1, h2,
      hk5, hrd, BinOp.eval]
  set s9 : State := { stR with regs := Function.update s8.regs 12 oR.value } with hs9
  have hcallR : Runs w p ω (.call 12 fReset [.load (.bin .add (.reg 0) (.const ASM_BR_OUT)),
      .reg 6, .load (.bin .add (.reg 8) (.const ASM_READ_S)), .reg 11]) s8 .normal s9
      (argsSize [.load (.bin .add (.reg 0) (.const ASM_BR_OUT)), .reg 6,
        .load (.bin .add (.reg 8) (.const ASM_READ_S)), .reg 11] + cR + 1) :=
    runs_call_iff.mpr ⟨_, bodyR, oR, stR, cR, hargsR, hfR, hrunR, rfl, rfl, rfl⟩
  have hargsE : evalArgs w s9 [.load (.bin .add (.reg 0) (.const ASM_BR_EMB)), .reg 7, .reg 10,
      .reg 9, .reg 12] = some [stR.mem (b + ASM_BR_EMB), mem (sd + ASM_SD_SPAN),
        mem (sd + ASM_SD_SLOTS), mem (sd + ASM_SD_NSLOTS), oR.value] := by
    have h1 := hk ASM_BR_EMB (by decide)
    have h2 := hw ASM_BR_EMB (by decide)
    simp [evalArgs, Expr.eval, hs9, hs8, hr7, hr6, hr5, hr4, hr3, hr2, hr1, hst0, startState, h1,
      h2, BinOp.eval]
  set s10 : State := { stE with regs := Function.update s9.regs 13 oE.value } with hs10
  have hcallE : Runs w p ω (.call 13 fEmb [.load (.bin .add (.reg 0) (.const ASM_BR_EMB)), .reg 7,
      .reg 10, .reg 9, .reg 12]) s9 .normal s10
      (argsSize [.load (.bin .add (.reg 0) (.const ASM_BR_EMB)), .reg 7, .reg 10, .reg 9,
        .reg 12] + cE + 1) :=
    runs_call_iff.mpr ⟨_, bodyE, oE, stE, cE, hargsE, hfE, hrunE, rfl, rfl, rfl⟩
  have hret : Runs w p ω (.ret (.reg 13)) s10 (.returned oE.value) s10 2 :=
    runs_ret_iff.mpr ⟨oE.value, by simp [Expr.eval, hs10], rfl, rfl, rfl⟩
  -- the sequence
  have q1 := runs_seq_iff.mpr (Or.inr ⟨s10, _, _, hcallE, hret, rfl⟩)
  have q2 := runs_seq_iff.mpr (Or.inr ⟨s9, _, _, hcallR, q1, rfl⟩)
  have q3 := runs_seq_iff.mpr (Or.inr ⟨s8, _, _, hcall8, q2, rfl⟩)
  have q4 := runs_seq_iff.mpr (Or.inr ⟨s7, _, _, runs_assign_iff.mpr ⟨_, e7, rfl, rfl, rfl⟩,
    q3, rfl⟩)
  have q5 := runs_seq_iff.mpr (Or.inr ⟨{ st0 with regs := r6 }, _, _,
    runs_assign_iff.mpr ⟨_, e6, rfl, rfl, rfl⟩, q4, rfl⟩)
  have q6 := runs_seq_iff.mpr (Or.inr ⟨{ st0 with regs := r5 }, _, _,
    runs_assign_iff.mpr ⟨_, e5, rfl, rfl, rfl⟩, q5, rfl⟩)
  have q7 := runs_seq_iff.mpr (Or.inr ⟨{ st0 with regs := r4 }, _, _,
    runs_assign_iff.mpr ⟨_, e4, rfl, rfl, rfl⟩, q6, rfl⟩)
  have q8 := runs_seq_iff.mpr (Or.inr ⟨{ st0 with regs := r3 }, _, _,
    runs_assign_iff.mpr ⟨_, e3, rfl, rfl, rfl⟩, q7, rfl⟩)
  have q9 := runs_seq_iff.mpr (Or.inr ⟨{ st0 with regs := r2 }, _, _,
    runs_assign_iff.mpr ⟨_, e2, rfl, rfl, rfl⟩, q8, rfl⟩)
  have q10 := runs_seq_iff.mpr (Or.inr ⟨{ st0 with regs := r1 }, _, _,
    runs_assign_iff.mpr ⟨_, e1, rfl, rfl, rfl⟩, q9, rfl⟩)
  refine ⟨s10, _, q10, rfl, ?_⟩
  simp only [argsSize, Expr.size]
  omega

end MinCostFlow.SparseCore.Program
