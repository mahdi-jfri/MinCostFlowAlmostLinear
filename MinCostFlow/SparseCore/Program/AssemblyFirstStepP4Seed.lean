module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepOutSeed
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSlotScanD

import WordRAM.Tactic

/-!
# The seeds of the candidate lists of Phase 4 (`AssemblyFirstStepP4Seed`)

Phase 4 collects three lists in its workspace (`Phase4WSAt`): a superset of the edges that leave
the output graph (`delSup`), a superset of the edges that enter it (`insSup`), and the edges whose
walks change (`reemb`). Before the spanners are updated, the procedure
`asmFirstP4SeedStmt fSeedB fSeedL fAppend`, with arguments `[batch, chg, ws, eCap, lazyPtr, nNew]`,
puts into these lists the edges that do not come from a spanner:
* the deleted edges of the batch go into `delSup`, and the deleted and inserted edges go into
  `insSup` (`asmFirstSeedBatch_runs`);
* the edges of the components that Phase 2 made active go into `insSup` and `reemb`
  (`asmFirstSeedLazy_runs`);
* the forest edges that the batch removes (the list `fDel` of the change record at `chg`) go into
  `insSup` (`asmFirstAppendList_runs`).

`asmFirstP4Seed_runs` gives the workspace with the three new lists and what they hold. It writes
only these lists, so every other cell, in the workspace or outside it, is kept.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Read

/-! ## The procedure -/

@[expose] public section

/-- **The seeds of the candidate lists of Phase 4**, `[batch, chg, ws, eCap, lazyPtr, nNew]`.
Registers `6` to `14` hold the places of the three lists in the workspace (flags, entries,
length). -/
def asmFirstP4SeedStmt (fSeedB fSeedL fAppend : ℕ) : Stmt :=
  .assign 6 (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 3))) ;;
  .assign 7 (.bin .add (.reg 2) (.bin .mul (.const 4) (.reg 3))) ;;
  .assign 8 (.bin .add (.reg 2) (.bin .mul (.const 10) (.reg 3))) ;;
  .assign 9 (.bin .add (.reg 2) (.bin .mul (.const 5) (.reg 3))) ;;
  .assign 10 (.bin .add (.reg 2) (.bin .mul (.const 6) (.reg 3))) ;;
  .assign 11 (.bin .add (.reg 8) (.const 1)) ;;
  .assign 12 (.bin .add (.reg 2) (.bin .mul (.const 7) (.reg 3))) ;;
  .assign 13 (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 3))) ;;
  .assign 14 (.bin .add (.reg 8) (.const 2)) ;;
  .call 15 fSeedB [.reg 0, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11] ;;
  .call 15 fSeedL [.reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 4, .reg 5] ;;
  .assign 16 (.load (.reg 1)) ;;
  .call 15 fAppend [.reg 9, .reg 10, .reg 11, .bin .add (.bin .add (.reg 1) (.const 2)) (.reg 16),
    .load (.bin .add (.bin .add (.reg 1) (.const 1)) (.reg 16))] ;;
  .ret (.const 0)

end

/-- A call followed by a statement, with the cost bound carried along. -/
private theorem runs_seq_callRuns_le' {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ}
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

public section

theorem asmFirstP4SeedStmt_noRand (fSeedB fSeedL fAppend : ℕ) :
    (asmFirstP4SeedStmt fSeedB fSeedL fAppend).NoRand := by
  simp [asmFirstP4SeedStmt, Stmt.NoRand]

/-- The workspace with new candidate lists. The memory may change only in the cells of the three
lists, and the new lists are stored there. -/
theorem phase4WSAt_setBufs {mem mem' : ℕ → ℕ} {ws eCap : ℕ} {S : Phase4WS} {Ld Li Lr : List ℕ}
    (h : Phase4WSAt mem ws eCap S)
    (hag : ∀ a, (a < ws + 3 * eCap ∨ (ws + 9 * eCap ≤ a ∧ a < ws + 10 * eCap) ∨
      ws + 10 * eCap + 3 ≤ a) → mem' a = mem a)
    (hD : DedupBufAt mem' (ws + 3 * eCap) (ws + 4 * eCap) (ws + 10 * eCap) eCap Ld)
    (hI : DedupBufAt mem' (ws + 5 * eCap) (ws + 6 * eCap) (ws + 10 * eCap + 1) eCap Li)
    (hR : DedupBufAt mem' (ws + 7 * eCap) (ws + 8 * eCap) (ws + 10 * eCap + 2) eCap Lr) :
    Phase4WSAt mem' ws eCap { S with delSup := Ld, insSup := Li, reemb := Lr } := by
  unfold Phase4WSAt at h ⊢
  simp only [p4InDtot, p4InAct, p4InTgt, p4InDelSup, p4DelSup, p4InInsSup, p4InsSup, p4InReemb,
    p4Reemb, p4SeenCopy, p4DelLen, p4InsLen, p4ReembLen, p4CopyLen, p4CopyBuf] at h ⊢
  obtain ⟨hD0, hA0, hT0, -, -, -, hSC0, hnd, hcb, hcl, hclat⟩ := h
  refine ⟨fun e he => (hag _ (by omega)).trans (hD0 e he),
    fun e he => (hag _ (by omega)).trans (hA0 e he),
    fun e he => (hag _ (by omega)).trans (hT0 e he), hD, hI, hR,
    fun e he => (hag _ (by omega)).trans (hSC0 e he), hnd, hcb, (hag _ (by omega)).trans hcl,
    fun i hi => (hag _ (by omega)).trans (hclat i hi)⟩

set_option maxHeartbeats 1600000 in
/-- **The run of the seeds of Phase 4.** The workspace at `ws` holds `S`. The batch at `batch`,
the table of the lists of the newly active components at `lazyPtr` with these lists, and the
change record at `chg` lie outside the workspace, and all their edges are below `eCap`. Then
`asmFirstP4SeedStmt` puts the deleted edges of the batch into `delSup`; the deleted and inserted
edges of the batch, the edges of the lists and the removed forest edges into `insSup`; and the
edges of the lists into `reemb`. Every cell outside the workspace is kept. -/
theorem asmFirstP4Seed_runs {w fSeedB fSeedL fAppend fPush batch chg ws eCap lazyPtr nNew words
      pos : ℕ} {p : Program}
    (hfSeedB : p.procs[fSeedB]? = some (asmFirstSeedBatchStmt fPush))
    (hfSeedL : p.procs[fSeedL]? = some (asmFirstSeedLazyStmt fAppend))
    (hfAppend : p.procs[fAppend]? = some (asmFirstAppendListStmt fPush))
    (hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt)
    {G₀ : MGraph} {U : List Update} {c : LSFChange} {lazyE : Fin nNew → List ℕ} {S : Phase4WS}
    {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hW : Phase4WSAt mem₀ ws eCap S) (hws_w : ws + p4WsSize eCap < 2 ^ w)
    (hBat : BatchAt mem₀ batch G₀ U words)
    (hCaps : ∀ u ∈ U, match u with
      | .insert e _ _ => e < eCap | .delete e => e < eCap | .split _ _ _ _ => True)
    (hBatOut : batch + words ≤ ws ∨ ws + p4WsSize eCap ≤ batch) (hBat_w : batch + words < 2 ^ w)
    (hLazy : ∀ (i : Fin nNew), ∃ ptr, mem₀ (lazyPtr + 2 * i.1) = ptr ∧
      mem₀ (lazyPtr + 2 * i.1 + 1) = (lazyE i).length ∧ ListAt mem₀ ptr (lazyE i) ∧
      ptr + (lazyE i).length < 2 ^ w ∧ (∀ e ∈ lazyE i, e < eCap) ∧
      (ptr + (lazyE i).length ≤ ws ∨ ws + p4WsSize eCap ≤ ptr))
    (hLazyT : lazyPtr + 2 * nNew ≤ ws ∨ ws + p4WsSize eCap ≤ lazyPtr)
    (hLazy_w : lazyPtr + 2 * nNew < 2 ^ w)
    (hChg : LSFChangeAt mem₀ chg c) (hfDel_cap : ∀ e ∈ c.fDel, e < eCap)
    (hChgOut : chg + c.words ≤ ws ∨ ws + p4WsSize eCap ≤ chg) (hChg_w : chg + c.words < 2 ^ w) :
    ∃ st' cost, ∃ Ld Li Lr : List ℕ,
      Runs w p ω (asmFirstP4SeedStmt fSeedB fSeedL fAppend)
        (startState [batch, chg, ws, eCap, lazyPtr, nNew] mem₀ pos) (.returned 0) st' cost ∧
      Phase4WSAt st'.mem ws eCap { S with delSup := Ld, insSup := Li, reemb := Lr } ∧
      (∀ e, e ∈ Ld ↔ e ∈ S.delSup ∨ e ∈ batchDeletes U) ∧
      (∀ e, e ∈ Li ↔ e ∈ S.insSup ∨ e ∈ batchDeletes U ∨ e ∈ batchInsEdges U ∨
        (∃ i : Fin nNew, e ∈ lazyE i) ∨ e ∈ c.fDel) ∧
      (∀ e, e ∈ Lr ↔ e ∈ S.reemb ∨ ∃ i : Fin nNew, e ∈ lazyE i) ∧
      (∀ a, (a < ws ∨ ws + p4WsSize eCap ≤ a) → st'.mem a = mem₀ a) ∧
      cost ≤ 130 * U.length + 130 * ((List.finRange nNew).map fun i => (lazyE i).length).sum +
        90 * nNew + 60 * c.fDel.length + 200 := by
  classical
  have h0w : 0 < 2 ^ w := by omega
  have hcw : c.words = 2 + c.roots.length + c.fDel.length := by
    simp only [LSFChange.words, LSFChange.size]; omega
  simp only [p4WsSize] at hws_w hBatOut hLazy hLazyT hChgOut ⊢
  have hW' := hW
  unfold Phase4WSAt at hW'
  simp only [p4InDelSup, p4DelSup, p4DelLen, p4InInsSup, p4InsSup, p4InsLen, p4InReemb, p4Reemb,
    p4ReembLen] at hW'
  have hDd₀ := hW'.2.2.2.1
  have hDi₀ := hW'.2.2.2.2.1
  have hDr₀ := hW'.2.2.2.2.2.1
  clear hW'
  -- The seeds from the batch.
  obtain ⟨st₁, c₁, Ld, Li₁, hr₁, hDd₁, hDi₁, hLd, hLi₁, hfr₁, hc₁⟩ :=
    asmFirstSeedBatch_runs (pos := pos) (ω := ω) hfPush hw16 hBat hCaps hDd₀ hDi₀
      (fun a ha => by unfold OutOf; omega) (by unfold OutOf; omega) (by unfold OutOf; omega)
      (fun a h1 h2 => by unfold OutOf; omega) hBat_w (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have hfr₁' : ∀ a, (a < ws + 3 * eCap ∨ (ws + 7 * eCap ≤ a ∧ a < ws + 10 * eCap) ∨
      ws + 10 * eCap + 2 ≤ a) → st₁.mem a = mem₀ a := fun a ha =>
    hfr₁ a (by unfold OutOf; omega) (by unfold OutOf; omega) (by omega) (by unfold OutOf; omega)
      (by unfold OutOf; omega) (by omega)
  -- The seeds from the lists of the newly active components.
  have hDr₁ : DedupBufAt st₁.mem (ws + 7 * eCap) (ws + 8 * eCap) (ws + 10 * eCap + 2) eCap
      S.reemb :=
    dedupBufAt_of_agree_cap hDr₀ (fun e he => hfr₁' _ (by omega)) (fun i hi => hfr₁' _ (by omega))
      (hfr₁' _ (by omega))
  have hLazy₁ : ∀ (i : Fin nNew), ∃ ptr, st₁.mem (lazyPtr + 2 * i.1) = ptr ∧
      st₁.mem (lazyPtr + 2 * i.1 + 1) = (lazyE i).length ∧ ListAt st₁.mem ptr (lazyE i) ∧
      ptr + (lazyE i).length < 2 ^ w ∧ (∀ e ∈ lazyE i, e < eCap) ∧
      (ptr + (lazyE i).length ≤ ws + 5 * eCap ∨ ws + 5 * eCap + eCap ≤ ptr) ∧
      (ptr + (lazyE i).length ≤ ws + 6 * eCap ∨ ws + 6 * eCap + eCap ≤ ptr) ∧
      (ws + 10 * eCap + 1 < ptr ∨ ptr + (lazyE i).length ≤ ws + 10 * eCap + 1) ∧
      (ptr + (lazyE i).length ≤ ws + 7 * eCap ∨ ws + 7 * eCap + eCap ≤ ptr) ∧
      (ptr + (lazyE i).length ≤ ws + 8 * eCap ∨ ws + 8 * eCap + eCap ≤ ptr) ∧
      (ws + 10 * eCap + 2 < ptr ∨ ptr + (lazyE i).length ≤ ws + 10 * eCap + 2) := by
    intro i
    obtain ⟨ptr, h1, h2, h3, h4, h5, h6⟩ := hLazy i
    have hi := i.2
    refine ⟨ptr, (hfr₁' _ (by omega)).trans h1, (hfr₁' _ (by omega)).trans h2,
      fun j hj => (hfr₁' _ (by omega)).trans (h3 j hj), h4, h5, by omega, by omega, by omega,
      by omega, by omega, by omega⟩
  obtain ⟨st₂, c₂, Li₂, Lr, hr₂, hDi₂, hDr₂, hLi₂, hLr, hfr₂, hc₂⟩ :=
    asmFirstSeedLazy_runs (lazyPtr := lazyPtr) (pos := st₁.pos) (ω := ω) hfPush hfAppend hw16 hDi₁
      hDr₁ hLazy₁ (fun a h1 h2 => by unfold OutOf; omega) (fun a ha => by unfold OutOf; omega)
      (by unfold OutOf; omega) (by unfold OutOf; omega) hLazy_w (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have hfr₂' : ∀ a, (a < ws + 5 * eCap ∨ (ws + 9 * eCap ≤ a ∧ a < ws + 10 * eCap + 1) ∨
      ws + 10 * eCap + 3 ≤ a) → st₂.mem a = st₁.mem a := fun a ha =>
    hfr₂ a (by unfold OutOf; omega) (by unfold OutOf; omega) (by omega) (by unfold OutOf; omega)
      (by unfold OutOf; omega) (by omega)
  -- The removed forest edges.
  have hm_r : st₂.mem chg = c.roots.length :=
    (hfr₂' _ (by omega)).trans ((hfr₁' _ (by omega)).trans hChg.1)
  have hm_f : st₂.mem (chg + 1 + c.roots.length) = c.fDel.length :=
    (hfr₂' _ (by omega)).trans ((hfr₁' _ (by omega)).trans hChg.2.2.1)
  have hSrc : ListAt st₂.mem (chg + 2 + c.roots.length) c.fDel := fun j hj =>
    (hfr₂' _ (by omega)).trans ((hfr₁' _ (by omega)).trans (hChg.2.2.2 j hj))
  obtain ⟨st₃, c₃, hr₃, hDi₃, hfr₃, hc₃⟩ :=
    asmFirstAppendList_runs (pos := st₂.pos) (ω := ω) hfPush hw16 hDi₂ hSrc hfDel_cap
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  have hfr₃' : ∀ a, (a < ws + 5 * eCap ∨ ws + 7 * eCap ≤ a) → a ≠ ws + 10 * eCap + 1 →
      st₃.mem a = st₂.mem a := fun a ha hne =>
    hfr₃ a (by omega) (by omega) hne
  -- The workspace at the end.
  have hDd₃ : DedupBufAt st₃.mem (ws + 3 * eCap) (ws + 4 * eCap) (ws + 10 * eCap) eCap Ld :=
    dedupBufAt_of_agree_cap hDd₁
      (fun e he => ((hfr₃' _ (by omega) (by omega)).trans (hfr₂' _ (by omega))))
      (fun i hi => ((hfr₃' _ (by omega) (by omega)).trans (hfr₂' _ (by omega))))
      ((hfr₃' _ (by omega) (by omega)).trans (hfr₂' _ (by omega)))
  have hDr₃ : DedupBufAt st₃.mem (ws + 7 * eCap) (ws + 8 * eCap) (ws + 10 * eCap + 2) eCap Lr :=
    dedupBufAt_of_agree_cap hDr₂ (fun e he => hfr₃' _ (by omega) (by omega))
      (fun i hi => hfr₃' _ (by omega) (by omega)) (hfr₃' _ (by omega) (by omega))
  have hag : ∀ a, (a < ws + 3 * eCap ∨ (ws + 9 * eCap ≤ a ∧ a < ws + 10 * eCap) ∨
      ws + 10 * eCap + 3 ≤ a) → st₃.mem a = mem₀ a := fun a ha =>
    (hfr₃' a (by omega) (by omega)).trans ((hfr₂' a (by omega)).trans (hfr₁' a (by omega)))
  have hWS₃ := phase4WSAt_setBufs hW hag hDd₃ hDi₃ hDr₃
  -- The run.
  set s0 := startState [batch, chg, ws, eCap, lazyPtr, nNew] mem₀ pos with hs0
  have hs0_0 : s0.regs 0 = batch := by simp [s0, startState]
  have hs0_1 : s0.regs 1 = chg := by simp [s0, startState]
  have hs0_2 : s0.regs 2 = ws := by simp [s0, startState]
  have hs0_3 : s0.regs 3 = eCap := by simp [s0, startState]
  have hs0_4 : s0.regs 4 = lazyPtr := by simp [s0, startState]
  have hs0_5 : s0.regs 5 = nNew := by simp [s0, startState]
  have key : ∃ o st' cc, Runs w p ω (asmFirstP4SeedStmt fSeedB fSeedL fAppend) s0 o st' cc ∧
      (o = .returned 0 ∧
        Phase4WSAt st'.mem ws eCap
          { S with delSup := Ld, insSup := appendDedup Li₂ c.fDel, reemb := Lr } ∧
        (∀ a, (a < ws ∨ ws + (11 * eCap + 4) ≤ a) → st'.mem a = mem₀ a)) ∧
      0 + cc ≤ 130 * U.length + 130 * ((List.finRange nNew).map fun i => (lazyE i).length).sum +
        90 * nNew + 60 * c.fDel.length + 200 := by
    unfold asmFirstP4SeedStmt
    wram_step
    wram_step
    wram_step
    wram_step
    wram_step
    wram_step
    wram_step
    wram_step
    wram_step
    refine runs_seq_callRuns_le' (by eval_expr) hfSeedB hr₁ ?_
    refine runs_seq_callRuns_le' (by eval_expr) hfSeedL hr₂ ?_
    wram_step
    refine runs_seq_callRuns_le' (by eval_expr) hfAppend hr₃ ?_
    wram_step
    · exact ⟨rfl, hWS₃, fun a ha => hag a (by omega)⟩
    · wram_cost
  obtain ⟨o, st', c', hr, ⟨ho, hq₁, hq₂⟩, hc⟩ := key
  subst ho
  refine ⟨st', c', Ld, appendDedup Li₂ c.fDel, Lr, hr, hq₁, hLd, fun e => ?_, fun e => ?_, hq₂,
    by omega⟩
  · rw [mem_appendDedup_iff, hLi₂, hLi₁]
    tauto
  · rw [hLr]

end

end MinCostFlow.SparseCore.Program
