module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4Edge

import WordRAM.Tactic

/-!
# The scan of the spanner's batch `U_H` in Phase 4 (`AssemblyFirstStepP4ScanUH`)

After the update of a slot, the spanner leaves the batch `U_H` that turns its old spanner `H` into
the new one `H'` (`DSUpdatePost`). Phase 4 needs its edges for two reasons.
* An edge inserted into `H` may enter the new output graph `S_cur'`, and an edge deleted from `H`
  may leave it (`outInsSet_subset_sup` and `outDelSet_subset_sup`). So each such edge is marked
  from the new presence arrays of the slot and pushed into the candidate list `insSup` or
  `delSup`.
* An edge deleted from `H` that stays in the slot's graph and was in the old output graph leaves
  the output graph while it keeps a walk in the spanner. Its walk must be written into the
  embedding table, so it goes into the copy buffer. This is the set `(H ∩ G') \ H'` of
  `stepBundleTree`, whose walks also give the set `D_left`.

`asmFirstScanSlotUHStmt fEdge` takes `[gEPres, hEPres, uhPtr, ws, eCap, isOld, oldS]`: the presence
arrays of the slot's new graph and spanner, the batch, the workspace, the cap, whether the slot was
active before the step, and the presence array of the old output graph. It reads the batch in the
format of `BatchAt` (as `asmFirstSeedBatchStmt` does) and calls the one-edge procedure
`asmFirstP4EdgeStmt` (`AssemblyFirstStepP4Edge.lean`) on every inserted or deleted edge.
`asmFirstScanSlotUH_runs` proves that it turns the workspace `S` into
`U_H.foldl (p4StepUH GE HE OS isOld) S`, keeps every cell outside the workspace, and costs at
most `340 * |U_H| + 30` steps.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

/-- Unfolds the places of the Phase 4 workspace and closes the goal by `omega`. -/
local macro "p4o" : tactic => `(tactic| ((try simp only [p4WsSize, p4InDtot, p4InAct, p4InTgt,
  p4InDelSup, p4DelSup, p4InInsSup, p4InsSup, p4InReemb, p4Reemb, p4SeenCopy, p4DelLen, p4InsLen,
  p4ReembLen, p4CopyLen, p4CopyBuf] at *) <;> omega))

@[expose] public section

/-- The work on one update of the spanner's batch `U_H`. An inserted edge is marked and pushed
into `insSup`. A deleted edge is marked and pushed into `delSup`, and it goes into the copy buffer
when the slot was active before (`isOld`), the edge stays in the slot's graph `GE` but not in its
spanner `HE`, and it was in the old output graph `OS`. A split needs no work. -/
noncomputable def p4StepUH (GE HE OS : Finset ℕ) (isOld : Bool) (S : Phase4WS) :
    Update → Phase4WS
  | .insert e _ _ => p4StepEdge GE HE false false true false S e
  | .delete e => p4StepEdge GE HE false true false
      (isOld && decide (e ∈ GE ∧ e ∉ HE ∧ e ∈ OS)) S e
  | .split _ _ _ _ => S

/-- The edge of an insert or a delete is below `eCap`. -/
def UpdEdgeBelow (eCap : ℕ) : Update → Prop
  | .insert e _ _ => e < eCap
  | .delete e => e < eCap
  | .split _ _ _ _ => True

/-- The copy flag of a deleted edge `e` (register `11`) into register `13`: the word of the old
output graph at `e` when the slot was active before (register `5`), `e` is in the slot's graph
(register `0`) and `e` is not in its spanner (register `1`), and `0` otherwise. -/
def asmFirstUHCopyFlag : Stmt :=
  .assign 13 (.const 0) ;;
  .cond (.reg 5)
    (.cond (.load (.bin .add (.reg 0) (.reg 11)))
      (.cond (.load (.bin .add (.reg 1) (.reg 11)))
        .nop
        (.assign 13 (.load (.bin .add (.reg 6) (.reg 11)))))
      .nop)
    .nop

/-- The loop body of `asmFirstScanSlotUHStmt`: the work on the update at `cur` (register `8`),
which then moves `cur` past the update. -/
def asmFirstScanUHBody (fEdge : ℕ) : Stmt :=
  .assign 10 (.load (.reg 8)) ;;
  .cond (.bin .eq (.reg 10) (.const 0))
    (.assign 11 (.load (.bin .add (.reg 8) (.const 1))) ;;
     .call 12 fEdge [.reg 0, .reg 1, .reg 3, .reg 4, .reg 11, .const 0, .const 0, .const 1,
       .const 0] ;;
     .assign 8 (.bin .add (.reg 8) (.const 4)))
    (.cond (.bin .eq (.reg 10) (.const 1))
      (.assign 11 (.load (.bin .add (.reg 8) (.const 1))) ;;
       asmFirstUHCopyFlag ;;
       .call 12 fEdge [.reg 0, .reg 1, .reg 3, .reg 4, .reg 11, .const 0, .const 1, .const 0,
         .reg 13] ;;
       .assign 8 (.bin .add (.reg 8) (.const 2)))
      (.assign 11 (.load (.bin .add (.reg 8) (.const 3))) ;;
       .assign 12 (.load (.bin .add (.reg 8) (.const 4))) ;;
       .assign 8 (.bin .add (.bin .add (.bin .add (.reg 8) (.const 5)) (.reg 11)) (.reg 12))))

/-- **The scan of `U_H`**, `[gEPres, hEPres, uhPtr, ws, eCap, isOld, oldS]`. -/
def asmFirstScanSlotUHStmt (fEdge : ℕ) : Stmt :=
  .assign 7 (.load (.reg 2)) ;;
  .assign 8 (.bin .add (.reg 2) (.const 1)) ;;
  forRange 9 (.const 0) (.reg 7) (asmFirstScanUHBody fEdge) ;;
  .ret (.const 0)

theorem asmFirstScanSlotUHStmt_noRand (fEdge : ℕ) : (asmFirstScanSlotUHStmt fEdge).NoRand := by
  simp [asmFirstScanSlotUHStmt, asmFirstScanUHBody, asmFirstUHCopyFlag, forRange, forUp,
    Stmt.NoRand]

end

/-! ## Helpers -/

/-- A statement given by a lemma on its runs, at the start of a sequence. -/
private theorem runs_seq_block_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s₁ s : Stmt}
    {st : State} {B k T : ℕ} {Q : Outcome → State → Prop} {R : State → Prop}
    (h₁ : ∃ st₁ c₁, Runs w p ω s₁ st .normal st₁ c₁ ∧ R st₁ ∧ c₁ ≤ B)
    (hrest : ∀ st₁, R st₁ →
      ∃ o st' c, Runs w p ω s st₁ o st' c ∧ Q o st' ∧ (k + B + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq s₁ s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨st₁, c₁, hr₁, hR, hc₁⟩ := h₁
  obtain ⟨o, st', c, hr, hq, hc⟩ := hrest st₁ hR
  exact ⟨o, st', c₁ + c + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c, hr₁, hr, rfl⟩), hq, by omega⟩

/-- A call whose body is given by a run, at the start of a sequence. -/
private theorem runs_seq_callRuns_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ}
    {args : List Expr} {s : Stmt} {st : State} {vs : List ℕ} {body : Stmt} {k T : ℕ}
    {Q : Outcome → State → Prop}
    (hargs : evalArgs w st args = some vs) (hb : p.procs[f]? = some body) {o₁ : Outcome}
    {st₁ : State} {c₁ : ℕ} (h₁ : Runs w p ω body (startState vs st.mem st.pos) o₁ st₁ c₁)
    (hrest : ∃ o st' c₂, Runs w p ω s { st₁ with regs := Function.update st.regs r o₁.value }
      o st' c₂ ∧ Q o st' ∧ (k + argsSize args + c₁ + 2) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f args) s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o, st', c₂, hr₂, hq, hc⟩ := hrest
  exact ⟨o, st', (argsSize args + c₁ + 1) + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨_, _, c₂,
    runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hb, h₁, rfl, rfl, rfl⟩, hr₂, rfl⟩), hq,
    by omega⟩

/-- The run of `asmFirstUHCopyFlag`: it sets register `13` to the copy flag. -/
private theorem uhCopyFlag_runs {w gEPres hEPres oldS isOld e : ℕ} {p : Program}
    {ω : ℕ → Bool} {GE HE OS : Finset ℕ} {st : State} (hw16 : 16 ≤ 2 ^ w)
    (hr0 : st.regs 0 = gEPres) (hr1 : st.regs 1 = hEPres) (hr5 : st.regs 5 = isOld)
    (hr6 : st.regs 6 = oldS) (hr11 : st.regs 11 = e)
    (hge : st.mem (gEPres + e) = if e ∈ GE then 1 else 0)
    (hhe : st.mem (hEPres + e) = if e ∈ HE then 1 else 0)
    (hos : st.mem (oldS + e) = if e ∈ OS then 1 else 0)
    (hg_w : gEPres + e < 2 ^ w) (hh_w : hEPres + e < 2 ^ w) (ho_w : oldS + e < 2 ^ w) :
    ∃ st' c, Runs w p ω asmFirstUHCopyFlag st .normal st' c ∧ (st'.mem = st.mem ∧
      st'.pos = st.pos ∧
      st'.regs = Function.update st.regs 13
        (if isOld ≠ 0 ∧ e ∈ GE ∧ e ∉ HE ∧ e ∈ OS then 1 else 0)) ∧ c ≤ 30 := by
  have key : ∃ o st' c, Runs w p ω asmFirstUHCopyFlag st o st' c ∧
      (o = .normal ∧ st'.mem = st.mem ∧ st'.pos = st.pos ∧
        st'.regs = Function.update st.regs 13
          (if isOld ≠ 0 ∧ e ∈ GE ∧ e ∉ HE ∧ e ∈ OS then 1 else 0)) ∧ 0 + c ≤ 30 := by
    unfold asmFirstUHCopyFlag
    wram_run
    all_goals first
      | wram_cost
      | (refine ⟨rfl, rfl, rfl, ?_⟩
         funext r
         by_cases hr : r = 13
         · subst hr
           by_cases hGE : e ∈ GE <;> by_cases hHE : e ∈ HE <;> by_cases hOS : e ∈ OS <;>
             simp_all
         · simp [hr])
  obtain ⟨o, st', c, hr, ⟨rfl, h1, h2, h3⟩, hc⟩ := key
  exact ⟨st', c, hr, ⟨h1, h2, h3⟩, by omega⟩


/-- The copy flag as a boolean. -/
private lemma decide_copyFlag (isOld e : ℕ) (GE HE OS : Finset ℕ) :
    decide ((if isOld ≠ 0 ∧ e ∈ GE ∧ e ∉ HE ∧ e ∈ OS then 1 else 0) ≠ 0) =
      (decide (isOld ≠ 0) && decide (e ∈ GE ∧ e ∉ HE ∧ e ∈ OS)) := by
  by_cases h1 : isOld = 0 <;> by_cases h2 : e ∈ GE <;> by_cases h3 : e ∈ HE <;>
    by_cases h4 : e ∈ OS <;> simp [h1, h2, h3, h4]

set_option maxHeartbeats 1600000 in
/-- One pass of the loop body of `asmFirstScanSlotUHStmt`, on the update `u` at `cur`. -/
private theorem scanUHBody_runs {w fEdge fPush fMark gEPres hEPres ws eCap isOld oldS cur len : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hfEdge : p.procs[fEdge]? = some (asmFirstP4EdgeStmt fPush fMark))
    (hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt)
    (hfMark : p.procs[fMark]? = some asmFirstMarkSlotEdgeStmt)
    {GE HE OS : Finset ℕ} {Hk : MGraph} {u : Update} {S : Phase4WS} {st : State}
    (hw16 : 16 ≤ 2 ^ w)
    (hr0 : st.regs 0 = gEPres) (hr1 : st.regs 1 = hEPres) (hr3 : st.regs 3 = ws)
    (hr4 : st.regs 4 = eCap) (hr5 : st.regs 5 = isOld) (hr6 : st.regs 6 = oldS)
    (hr8 : st.regs 8 = cur)
    (hW : Phase4WSAt st.mem ws eCap S)
    (hGE : ∀ e < eCap, st.mem (gEPres + e) = if e ∈ GE then 1 else 0)
    (hHE : ∀ e < eCap, st.mem (hEPres + e) = if e ∈ HE then 1 else 0)
    (hOS : ∀ e < eCap, st.mem (oldS + e) = if e ∈ OS then 1 else 0)
    (huAt : UpdateAt st.mem cur Hk u len)
    (hcap : UpdEdgeBelow eCap u)
    (hcur_w : cur + len < 2 ^ w)
    (hg_disj : gEPres + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ gEPres)
    (hh_disj : hEPres + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ hEPres)
    (hg_w : gEPres + eCap < 2 ^ w) (hh_w : hEPres + eCap < 2 ^ w)
    (ho_w : oldS + eCap < 2 ^ w) (hws_w : ws + p4WsSize eCap < 2 ^ w) :
    ∃ o st' c, Runs w p ω (asmFirstScanUHBody fEdge) st o st' c ∧
      (o = .normal ∧ st'.regs 8 = cur + len ∧
        (∀ r, r ≠ 8 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → st'.regs r = st.regs r) ∧
        Phase4WSAt st'.mem ws eCap (p4StepUH GE HE OS (decide (isOld ≠ 0)) S u) ∧
        (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st'.mem a = st.mem a)) ∧
      0 + c ≤ 330 := by
  have h0w : 0 < 2 ^ w := by omega
  have hlen2 := huAt.ge_two
  cases u with
  | insert e x y =>
    obtain ⟨rfl, hL⟩ := huAt
    have hm0 : st.mem cur = 0 := by simpa using hL 0 (by simp)
    have hm1 : st.mem (cur + 1) = e := by simpa using hL 1 (by simp)
    have hm0' : st.mem (st.regs 8) = 0 := by rw [hr8]; exact hm0
    have hm1' : st.mem (st.regs 8 + 1) = e := by rw [hr8]; exact hm1
    have he : e < eCap := hcap
    obtain ⟨stE, cE, hrE, hWE, hfrE, hcE⟩ := asmFirstP4Edge_runs (fD := 0) (fDel := 0)
      (fIns := 1) (fCopy := 0) (pos := st.pos) (ω := ω) hfPush hfMark hw16 hW hGE hHE he
      hg_disj hh_disj hg_w hh_w hws_w
    unfold asmFirstScanUHBody
    wram_step
    wram_step
    wram_step
    refine runs_seq_callRuns_le (by eval_expr) hfEdge hrE ?_
    wram_step
    · refine ⟨rfl, by simp [hr8], fun r h8 h10 h11 h12 _ => by
        simp [h8, h10, h11, h12], ?_, fun a ha => hfrE a ha⟩
      simpa [p4StepUH] using hWE
    · wram_cost
  | delete e =>
    obtain ⟨rfl, hL⟩ := huAt
    have hm0 : st.mem cur = 1 := by simpa using hL 0 (by simp)
    have hm1 : st.mem (cur + 1) = e := by simpa using hL 1 (by simp)
    have hm0' : st.mem (st.regs 8) = 1 := by rw [hr8]; exact hm0
    have hm1' : st.mem (st.regs 8 + 1) = e := by rw [hr8]; exact hm1
    have he : e < eCap := hcap
    obtain ⟨stE, cE, hrE, hWE, hfrE, hcE⟩ := asmFirstP4Edge_runs (fD := 0) (fDel := 1)
      (fIns := 0) (fCopy := if isOld ≠ 0 ∧ e ∈ GE ∧ e ∉ HE ∧ e ∈ OS then 1 else 0)
      (pos := st.pos) (ω := ω) hfPush hfMark hw16 hW hGE hHE he hg_disj hh_disj hg_w hh_w hws_w
    unfold asmFirstScanUHBody
    wram_step
    wram_step
    wram_step
    wram_step
    refine runs_seq_block_le (uhCopyFlag_runs (GE := GE) (HE := HE) (OS := OS) (e := e)
      (gEPres := gEPres) (hEPres := hEPres) (isOld := isOld) (oldS := oldS) hw16
      (by simp [hr0]) (by simp [hr1]) (by simp [hr5]) (by simp [hr6]) (by simp [hm1'])
      (hGE e he) (hHE e he) (hOS e he) (by omega) (by omega) (by omega)) ?_
    rintro ⟨m₁, r₁, p₁⟩ ⟨hm₁, hp₁, hr₁⟩
    simp only at hm₁ hp₁ hr₁
    subst hm₁ hp₁ hr₁
    refine runs_seq_callRuns_le (by eval_expr) hfEdge hrE ?_
    wram_step
    · refine ⟨rfl, by simp [hr8], fun r h8 h10 h11 h12 h13 => by
        simp [h8, h10, h11, h12, h13], ?_, fun a ha => hfrE a ha⟩
      simpa [p4StepUH, decide_copyFlag] using hWE
    · wram_cost
  | split v v' St Sh =>
    rcases huAt with ⟨Lt, Lh, -, -, -, -, rfl, hL⟩ | ⟨Lt, Lh, -, -, -, -, rfl, hL⟩
    all_goals
      have hm3 : st.mem (cur + 3) = Lt.length := by simpa using hL 3 (by simp)
      have hm4 : st.mem (cur + 4) = Lh.length := by simpa using hL 4 (by simp)
      have hm0 : st.mem cur ≠ 0 ∧ st.mem cur ≠ 1 := by
        have := hL 0 (by simp); simp at this; omega
      have hm3' : st.mem (st.regs 8 + 3) = Lt.length := by rw [hr8]; exact hm3
      have hm4' : st.mem (st.regs 8 + 4) = Lh.length := by rw [hr8]; exact hm4
      have hm0' : st.mem (st.regs 8) ≠ 0 ∧ st.mem (st.regs 8) ≠ 1 := by rw [hr8]; exact hm0
      unfold asmFirstScanUHBody
      wram_run
    all_goals first
      | wram_cost
      | (refine ⟨rfl, by simp [hm3, hm4, hr8]; try omega,
          fun r h8 h10 h11 h12 _ => by simp [h8, h10, h11, h12],
          by simpa [p4StepUH] using hW, fun _ _ => rfl⟩)


/-! ## The run -/

public section

set_option maxHeartbeats 1600000 in
/-- **The scan of `U_H`.** From the workspace `S`, with the batch `U_H` and the presence arrays of
the slot's new graph `GE`, of its new spanner `HE` and of the old output graph `OS` outside the
workspace, `asmFirstScanSlotUHStmt` leaves the workspace
`U_H.foldl (p4StepUH GE HE OS (isOld ≠ 0)) S`, keeps every cell outside the workspace, and costs
at most `340 * |U_H| + 30`. -/
theorem asmFirstScanSlotUH_runs
    {w fEdge fPush fMark gEPres hEPres uhPtr ws eCap isOld oldS words pos : ℕ} {p : Program}
    (hfEdge : p.procs[fEdge]? = some (asmFirstP4EdgeStmt fPush fMark))
    (hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt)
    (hfMark : p.procs[fMark]? = some asmFirstMarkSlotEdgeStmt)
    {GE HE OS : Finset ℕ} {H : MGraph} {UH : List Update} {S : Phase4WS} {mem₀ : ℕ → ℕ}
    {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hW : Phase4WSAt mem₀ ws eCap S)
    (hGE : ∀ e < eCap, mem₀ (gEPres + e) = if e ∈ GE then 1 else 0)
    (hHE : ∀ e < eCap, mem₀ (hEPres + e) = if e ∈ HE then 1 else 0)
    (hOS : ∀ e < eCap, mem₀ (oldS + e) = if e ∈ OS then 1 else 0)
    (hBat : BatchAt mem₀ uhPtr H UH words) (hCaps : ∀ u ∈ UH, UpdEdgeBelow eCap u)
    (hg_disj : gEPres + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ gEPres)
    (hh_disj : hEPres + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ hEPres)
    (ho_disj : oldS + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ oldS)
    (hu_disj : uhPtr + words ≤ ws ∨ ws + p4WsSize eCap ≤ uhPtr)
    (hg_w : gEPres + eCap < 2 ^ w) (hh_w : hEPres + eCap < 2 ^ w)
    (ho_w : oldS + eCap < 2 ^ w) (hu_w : uhPtr + words < 2 ^ w)
    (hws_w : ws + p4WsSize eCap < 2 ^ w) :
    ∃ st' cost,
      Runs w p ω (asmFirstScanSlotUHStmt fEdge)
        (startState [gEPres, hEPres, uhPtr, ws, eCap, isOld, oldS] mem₀ pos) (.returned 0) st'
        cost ∧
      Phase4WSAt st'.mem ws eCap (UH.foldl (p4StepUH GE HE OS (decide (isOld ≠ 0))) S) ∧
      (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st'.mem a = mem₀ a) ∧
      cost ≤ 340 * UH.length + 30 := by
  classical
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  obtain ⟨hB1, hlen, hBB⟩ := hBat
  have hUL : 2 * UH.length ≤ words - 1 := batchBodyAt_length_le hBB
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = gEPres ∧ st.regs 1 = hEPres ∧ st.regs 3 = ws ∧ st.regs 4 = eCap ∧
    st.regs 5 = isOld ∧ st.regs 6 = oldS ∧ st.regs 7 = UH.length ∧ st.regs 9 = i ∧
    (∃ W, uhPtr < st.regs 8 ∧ st.regs 8 + W ≤ uhPtr + words ∧
      BatchBodyAt mem₀ (st.regs 8) (H.applyBatch (UH.take i)) (UH.drop i) W) ∧
    Phase4WSAt st.mem ws eCap ((UH.take i).foldl (p4StepUH GE HE OS (decide (isOld ≠ 0))) S) ∧
    (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st.mem a = mem₀ a)
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 9) (lo := .const 0) (hi := .reg 7)
    (body := asmFirstScanUHBody fEdge)
    (P := fun st => st.regs 0 = gEPres ∧ st.regs 1 = hEPres ∧ st.regs 3 = ws ∧
      st.regs 4 = eCap ∧ st.regs 5 = isOld ∧ st.regs 6 = oldS ∧ st.regs 7 = UH.length ∧
      st.regs 8 = uhPtr + 1 ∧ st.mem = mem₀)
    (Inv := Inv) (fun _ => 330) 0 UH.length (Nat.zero_le _) h1w (fun _ => by omega)
    (fun st ⟨h0, h1, h3, h4, h5, h6, h7, h8, hm⟩ => ⟨Expr.eval_const h0w, by simp [h0],
      by simp [h1], by simp [h3], by simp [h4], by simp [h5], by simp [h6], by simp [h7],
      by simp, ⟨words - 1, by simp [h8], by simp [h8]; omega, by
        show BatchBodyAt mem₀ (Function.update st.regs 9 0 8) (H.applyBatch (UH.take 0))
          (UH.drop 0) (words - 1)
        rw [Function.update_of_ne (by decide), h8]; exact hBB⟩,
      by simpa [hm] using hW, fun a _ => by simp [hm]⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.2.2.2.2.1)
    (fun i _ hi st ω' hI => by
      obtain ⟨h0, h1, h3, h4, h5, h6, h7, h9, ⟨W, hlo, hhi, hBBi⟩, hWi, hfri⟩ := hI
      rw [List.drop_eq_getElem_cons hi] at hBBi
      obtain ⟨len, hlenW, huAt, hBBrest⟩ := hBBi
      have hagree : ∀ j < len, st.mem (st.regs 8 + j) = mem₀ (st.regs 8 + j) := fun j hj =>
        hfri _ (by rcases hu_disj with h | h <;> omega)
      have hst : ∀ x, x + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ x → ∀ e < eCap,
          st.mem (x + e) = mem₀ (x + e) := fun x hx e he =>
        hfri _ (by rcases hx with h | h <;> omega)
      obtain ⟨o, st', c, hr, ⟨rfl, h8', hregs', hW', hfr'⟩, hc⟩ := scanUHBody_runs (ω := ω')
        (GE := GE) (HE := HE) (OS := OS) (cur := st.regs 8) (len := len) hfEdge hfPush hfMark
        hw16 h0 h1 h3 h4 h5 h6 rfl hWi
        (fun e he => (hst _ hg_disj e he).trans (hGE e he))
        (fun e he => (hst _ hh_disj e he).trans (hHE e he))
        (fun e he => (hst _ ho_disj e he).trans (hOS e he))
        (huAt.of_agree hagree) (hCaps _ (List.getElem_mem hi)) (by omega) hg_disj hh_disj
        hg_w hh_w ho_w hws_w
      have htake : UH.take (i + 1) = UH.take i ++ [UH[i]] := List.take_succ_eq_append_getElem hi
      have hreg : ∀ r, r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 →
          (Function.update st'.regs 9 (i + 1)) r = st.regs r := fun r h8 h9 h10 h11 h12 h13 => by
        rw [Function.update_of_ne h9]; exact hregs' r h8 h10 h11 h12 h13
      refine ⟨.normal, st', c, hr, ⟨⟨(hreg 0 (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)).trans h0,
        (hreg 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1,
        (hreg 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h3,
        (hreg 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h4,
        (hreg 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h5,
        (hreg 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h6,
        (hreg 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h7,
        by simp, ⟨W - len, ?_, ?_, ?_⟩, ?_, fun a ha => (hfr' a ha).trans (hfri a ha)⟩,
        (hregs' 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h9⟩,
        by show c ≤ 330; omega⟩
      · show uhPtr < Function.update st'.regs 9 (i + 1) 8
        rw [Function.update_of_ne (by decide), h8']; omega
      · show Function.update st'.regs 9 (i + 1) 8 + (W - len) ≤ uhPtr + words
        rw [Function.update_of_ne (by decide), h8']; omega
      · show BatchBodyAt mem₀ (Function.update st'.regs 9 (i + 1) 8)
          (H.applyBatch (UH.take (i + 1))) (UH.drop (i + 1)) (W - len)
        rw [Function.update_of_ne (by decide), h8', htake, applyBatch_append]
        exact hBBrest
      · rw [htake, List.foldl_append]; simpa using hW')
  set s0 := startState [gEPres, hEPres, uhPtr, ws, eCap, isOld, oldS] mem₀ pos with hs0
  have hm2 : s0.mem uhPtr = UH.length := hlen
  have hs02 : s0.regs 2 = uhPtr := by simp [s0, startState]
  have key : ∃ o st' c, Runs w p ω (asmFirstScanSlotUHStmt fEdge) s0 o st' c ∧
      (o = .returned 0 ∧
        Phase4WSAt st'.mem ws eCap (UH.foldl (p4StepUH GE HE OS (decide (isOld ≠ 0))) S) ∧
        (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st'.mem a = mem₀ a)) ∧
      0 + c ≤ 340 * UH.length + 30 := by
    unfold asmFirstScanSlotUHStmt
    wram_step
    wram_step
    refine runs_seq_triple_le hloop ⟨by simp [s0, startState], by simp [s0, startState],
      by simp [s0, startState], by simp [s0, startState], by simp [s0, startState],
      by simp [s0, startState], by simp [hm2], by simp [s0, startState], by simp [s0, startState]⟩ ?_
    rintro st₁ ⟨-, -, -, -, -, -, -, -, -, hWf, hfrf⟩
    rw [List.take_length] at hWf
    wram_step
    · exact ⟨rfl, hWf, hfrf⟩
    · have hrc : rangeCost (fun _ => 330) 0 UH.length = 330 * UH.length := by
        simp [rangeCost, Nat.mul_comm]
      rw [hrc]; wram_cost
  obtain ⟨o, st', c, hr, ⟨rfl, hWf, hfrf⟩, hc⟩ := key
  exact ⟨st', c, hr, hWf, hfrf, by omega⟩

end

end MinCostFlow.SparseCore.Program
