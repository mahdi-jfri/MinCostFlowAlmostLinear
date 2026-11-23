module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSlotScanD

import WordRAM.Tactic

/-!
# One edge of the Phase 4 workspace (`AssemblyFirstStepP4Edge`)

Each spanner task of Phase 4 reads the outputs `D`, `R` and `U_H` of the update of its slot, and
the walks of the edges that leave the spanner (the set `D_left` of `stepBundleTree`). Every edge
it reads gets the same kind of work in the Phase 4 workspace `Phase4WSAt`
(`AssemblyFirstStepSlotScanD.lean`). This file gives that work as one procedure, so that each scan
is a loop that calls it.

`asmFirstP4EdgeStmt fPush fMark` takes `[gEPres, hEPres, ws, eCap, e, fD, fDel, fIns, fCopy]`.
It reads each of the four flags as a boolean (`≠ 0`), and
1. adds `e` to `inDtot` if `fD`;
2. marks `e` in `inAct` and `inTgt` from the presence arrays of the slot's graph (`gEPres`) and of
   its spanner (`hEPres`), as `asmFirstMarkSlotEdgeStmt` does;
3. pushes `e` into the candidate list `delSup` if `fDel`, and into `insSup` if `fIns`;
4. pushes `e` into the copy buffer if `fCopy`, at most once per edge (`pushCopy`).

`asmFirstP4Edge_runs` proves that it turns the workspace `S` into `p4StepEdge GE HE … S e`, keeps
every cell outside the workspace, and costs at most `260` steps. The proof runs the parts one by
one. The lemmas `phase4WSAt_dtot`, `phase4WSAt_mark`, `phase4WSAt_pushDel` and
`phase4WSAt_pushIns` say how each part changes the workspace.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

/-- Unfolds the places of the Phase 4 workspace and closes the goal by `omega`. -/
local macro "p4o" : tactic => `(tactic| ((try simp only [p4WsSize, p4InDtot, p4InAct, p4InTgt,
  p4InDelSup, p4DelSup, p4InInsSup, p4InsSup, p4InReemb, p4Reemb, p4SeenCopy, p4DelLen, p4InsLen,
  p4ReembLen, p4CopyLen, p4CopyBuf] at *) <;> omega))

@[expose] public section

/-- The mark of one edge `e` of a slot: if `e` is an edge of the slot's graph `GE`, it becomes
active, and it is a target edge exactly when it is in the spanner `HE`. -/
noncomputable def p4Mark (GE HE : Finset ℕ) (S : Phase4WS) (e : ℕ) : Phase4WS :=
  open Classical in
  { S with
    inAct := if e ∈ GE then insert e S.inAct else S.inAct
    inTgt := if e ∈ GE then (if e ∈ HE then insert e S.inTgt else S.inTgt.erase e) else S.inTgt }

/-- The work on one edge `e`: add it to `inDtot` (`fD`), mark it, push it into `delSup` (`fDel`)
and `insSup` (`fIns`), and into the copy buffer (`fCopy`). -/
noncomputable def p4StepEdge (GE HE : Finset ℕ) (fD fDel fIns fCopy : Bool) (S : Phase4WS)
    (e : ℕ) : Phase4WS :=
  let S1 := if fD then { S with inDtot := insert e S.inDtot } else S
  let S2 := p4Mark GE HE S1 e
  let S3 := if fDel then { S2 with delSup := pushDedup S2.delSup e } else S2
  let S4 := if fIns then { S3 with insSup := pushDedup S3.insSup e } else S3
  if fCopy then pushCopy S4 e else S4

/-- The push into the copy buffer, at most once per edge (registers `9 = seenCopy`,
`11 = copyLen`, `12 = copyBuf`, `14 = e`, `16` scratch), as in `p4PushCopy_runs`. -/
def p4PushCopyBlock : Stmt :=
  .cond (.bin .eq (.load (.bin .add (.reg 9) (.reg 14))) (.const 0))
    (.store (.bin .add (.reg 9) (.reg 14)) (.const 1) ;;
     .assign 16 (.load (.reg 11)) ;;
     .store (.bin .add (.reg 12) (.reg 16)) (.reg 14) ;;
     .store (.reg 11) (.bin .add (.reg 16) (.const 1)))
    .nop

/-- The setup of `asmFirstP4EdgeStmt`: the places of the workspace go into registers. -/
def asmFirstP4EdgeSetup : Stmt :=
  .assign 9 (.bin .add (.reg 2) (.bin .mul (.const 9) (.reg 3))) ;;      -- seenCopy
  .assign 10 (.bin .add (.reg 2) (.reg 3)) ;;                            -- inAct
  .assign 13 (.bin .add (.reg 10) (.reg 3)) ;;                           -- inTgt
  .assign 17 (.bin .add (.reg 13) (.reg 3)) ;;                           -- inDelSup
  .assign 18 (.bin .add (.reg 17) (.reg 3)) ;;                           -- delSup
  .assign 20 (.bin .add (.reg 18) (.reg 3)) ;;                           -- inInsSup
  .assign 21 (.bin .add (.reg 20) (.reg 3)) ;;                           -- insSup
  .assign 19 (.bin .add (.reg 2) (.bin .mul (.const 10) (.reg 3))) ;;    -- delLen
  .assign 22 (.bin .add (.reg 19) (.const 1)) ;;                         -- insLen
  .assign 11 (.bin .add (.reg 19) (.const 3)) ;;                         -- copyLen
  .assign 12 (.bin .add (.reg 19) (.const 4)) ;;                         -- copyBuf
  .assign 14 (.reg 4)                                                    -- e

/-- **The work on one edge**, `[gEPres, hEPres, ws, eCap, e, fD, fDel, fIns, fCopy]`. -/
def asmFirstP4EdgeStmt (fPush fMark : ℕ) : Stmt :=
  asmFirstP4EdgeSetup ;;
  .cond (.reg 5) (.store (.bin .add (.reg 2) (.reg 4)) (.const 1)) .nop ;;
  .call 15 fMark [.reg 0, .reg 1, .reg 10, .reg 13, .reg 4] ;;
  .cond (.reg 6) (.call 15 fPush [.reg 17, .reg 18, .reg 19, .reg 4]) .nop ;;
  .cond (.reg 7) (.call 15 fPush [.reg 20, .reg 21, .reg 22, .reg 4]) .nop ;;
  .cond (.reg 8) p4PushCopyBlock .nop ;;
  .ret (.const 0)

theorem asmFirstP4EdgeStmt_noRand (fPush fMark : ℕ) :
    (asmFirstP4EdgeStmt fPush fMark).NoRand := by
  simp [asmFirstP4EdgeStmt, asmFirstP4EdgeSetup, p4PushCopyBlock, Stmt.NoRand]

end

/-! ## How each part changes the workspace -/

public section

private lemma copyBuf_length_le {mem : ℕ → ℕ} {ws eCap : ℕ} {S : Phase4WS}
    (h : Phase4WSAt mem ws eCap S) : S.copyBuf.length ≤ eCap := by
  obtain ⟨-, -, -, -, -, -, -, hnd, hcb, -, -⟩ := h
  rw [← List.toFinset_card_of_nodup hnd]
  calc S.copyBuf.toFinset.card ≤ (Finset.range eCap).card :=
        Finset.card_le_card fun e he => Finset.mem_range.mpr (hcb e (List.mem_toFinset.mp he)).1
    _ = eCap := Finset.card_range eCap

/-- The parts of a workspace after the three flag arrays `inDtot`, `inAct` and `inTgt` stay
when the memory keeps every cell from `ws + 3 * eCap` on. -/
private lemma phase4WSAt_tail {mem mem' : ℕ → ℕ} {ws eCap : ℕ} {S : Phase4WS}
    (h : Phase4WSAt mem ws eCap S)
    (hfr : ∀ a, ws + 3 * eCap ≤ a → mem' a = mem a) :
    DedupBufAt mem' (p4InDelSup ws eCap) (p4DelSup ws eCap) (p4DelLen ws eCap) eCap S.delSup ∧
    DedupBufAt mem' (p4InInsSup ws eCap) (p4InsSup ws eCap) (p4InsLen ws eCap) eCap S.insSup ∧
    DedupBufAt mem' (p4InReemb ws eCap) (p4Reemb ws eCap) (p4ReembLen ws eCap) eCap S.reemb ∧
    (∀ e < eCap, mem' (p4SeenCopy ws eCap + e) = if e ∈ S.seenCopy then 1 else 0) ∧
    mem' (p4CopyLen ws eCap) = S.copyBuf.length ∧ ListAt mem' (p4CopyBuf ws eCap) S.copyBuf := by
  have hcb := copyBuf_length_le h
  obtain ⟨-, -, -, hDS, hIS, hR, hSC, -, -, hcl, hclat⟩ := h
  exact ⟨dedupBufAt_of_agree_cap hDS (fun x hx => hfr _ (by p4o)) (fun x hx => hfr _ (by p4o))
      (hfr _ (by p4o)),
    dedupBufAt_of_agree_cap hIS (fun x hx => hfr _ (by p4o)) (fun x hx => hfr _ (by p4o))
      (hfr _ (by p4o)),
    dedupBufAt_of_agree_cap hR (fun x hx => hfr _ (by p4o)) (fun x hx => hfr _ (by p4o))
      (hfr _ (by p4o)),
    fun x hx => (hfr _ (by p4o)).trans (hSC x hx), (hfr _ (by p4o)).trans hcl,
    fun i hi => (hfr _ (by p4o)).trans (hclat i hi)⟩

/-- Setting the `inDtot` flag of `e` adds `e` to `inDtot`. -/
lemma phase4WSAt_dtot {mem : ℕ → ℕ} {ws eCap e : ℕ} {S : Phase4WS}
    (h : Phase4WSAt mem ws eCap S) (he : e < eCap) :
    Phase4WSAt (Function.update mem (ws + e) 1) ws eCap
      { S with inDtot := insert e S.inDtot } := by
  have hfr : ∀ a, ws + eCap ≤ a → Function.update mem (ws + e) 1 a = mem a := fun a ha => by
    rw [Function.update_of_ne (by omega)]
  obtain ⟨hDS, hIS, hR, hSC, hcl, hclat⟩ := phase4WSAt_tail h fun a ha => hfr a (by omega)
  obtain ⟨hD, hA, hT, -, -, -, -, hnd, hcb, -, -⟩ := h
  refine ⟨fun x hx => ?_, fun x hx => (hfr _ (by p4o)).trans (hA x hx),
    fun x hx => (hfr _ (by p4o)).trans (hT x hx), hDS, hIS, hR, hSC, hnd, hcb, hcl, hclat⟩
  by_cases hxe : x = e
  · subst hxe; simp [p4InDtot]
  · simp only [p4InDtot] at hD ⊢
    rw [Function.update_of_ne (by omega), hD x hx]
    simp [hxe]

/-- The post of `asmFirstMarkSlotEdgeStmt` on the workspace marks `e`. -/
lemma phase4WSAt_mark {mem mem' : ℕ → ℕ} {ws eCap e : ℕ} {GE HE : Finset ℕ} {S : Phase4WS}
    (h : Phase4WSAt mem ws eCap S) (he : e < eCap)
    (hin : e ∈ GE → mem' (p4InAct ws eCap + e) = 1 ∧
      mem' (p4InTgt ws eCap + e) = if e ∈ HE then 1 else 0)
    (hout : e ∉ GE → mem' = mem)
    (hfr : ∀ a, a ≠ p4InAct ws eCap + e → a ≠ p4InTgt ws eCap + e → mem' a = mem a) :
    Phase4WSAt mem' ws eCap (p4Mark GE HE S e) := by
  classical
  by_cases hG : e ∈ GE
  · obtain ⟨hDS, hIS, hR, hSC, hcl, hclat⟩ :=
      phase4WSAt_tail h fun a ha => hfr a (by p4o) (by p4o)
    obtain ⟨hD, hA, hT, -, -, -, -, hnd, hcb, -, -⟩ := h
    obtain ⟨hA1, hT1⟩ := hin hG
    refine ⟨fun x hx => (hfr _ (by p4o) (by p4o)).trans (hD x hx), fun x hx => ?_,
      fun x hx => ?_, hDS, hIS, hR, hSC, hnd, hcb, hcl, hclat⟩
    · by_cases hxe : x = e
      · subst hxe; simp [p4Mark, hG, hA1]
      · rw [hfr _ (by p4o) (by p4o), hA x hx]; simp [p4Mark, hG, hxe]
    · by_cases hxe : x = e
      · subst hxe; rw [hT1]; by_cases hH : x ∈ HE <;> simp [p4Mark, hG, hH]
      · rw [hfr _ (by p4o) (by p4o), hT x hx]
        by_cases hH : e ∈ HE <;> simp [p4Mark, hG, hH, hxe]
  · rw [hout hG]
    simpa [p4Mark, hG] using h

/-- A push of `e` into `delSup` that keeps every other cell changes only `delSup`. -/
lemma phase4WSAt_pushDel {mem mem' : ℕ → ℕ} {ws eCap e : ℕ} {S : Phase4WS}
    (h : Phase4WSAt mem ws eCap S)
    (hbuf : DedupBufAt mem' (p4InDelSup ws eCap) (p4DelSup ws eCap) (p4DelLen ws eCap) eCap
      (pushDedup S.delSup e))
    (hfr : ∀ a, (a < p4InDelSup ws eCap ∨ p4InDelSup ws eCap + eCap ≤ a) →
      (a < p4DelSup ws eCap ∨ p4DelSup ws eCap + eCap ≤ a) → a ≠ p4DelLen ws eCap →
      mem' a = mem a) :
    Phase4WSAt mem' ws eCap { S with delSup := pushDedup S.delSup e } := by
  have hcb := copyBuf_length_le h
  obtain ⟨hD, hA, hT, -, hIS, hR, hSC, hnd, hcb', hcl, hclat⟩ := h
  have hfr' : ∀ a, (a < ws + 3 * eCap ∨ ws + 5 * eCap ≤ a) → a ≠ ws + 10 * eCap →
      mem' a = mem a := fun a ha hne => hfr a (by p4o) (by p4o) (by p4o)
  exact ⟨fun x hx => (hfr' _ (by p4o) (by p4o)).trans (hD x hx),
    fun x hx => (hfr' _ (by p4o) (by p4o)).trans (hA x hx),
    fun x hx => (hfr' _ (by p4o) (by p4o)).trans (hT x hx), hbuf,
    dedupBufAt_of_agree_cap hIS (fun x hx => hfr' _ (by p4o) (by p4o))
      (fun x hx => hfr' _ (by p4o) (by p4o)) (hfr' _ (by p4o) (by p4o)),
    dedupBufAt_of_agree_cap hR (fun x hx => hfr' _ (by p4o) (by p4o))
      (fun x hx => hfr' _ (by p4o) (by p4o)) (hfr' _ (by p4o) (by p4o)),
    fun x hx => (hfr' _ (by p4o) (by p4o)).trans (hSC x hx), hnd, hcb',
    (hfr' _ (by p4o) (by p4o)).trans hcl,
    fun i hi => (hfr' _ (by p4o) (by p4o)).trans (hclat i hi)⟩

/-- A push of `e` into `insSup` that keeps every other cell changes only `insSup`. -/
lemma phase4WSAt_pushIns {mem mem' : ℕ → ℕ} {ws eCap e : ℕ} {S : Phase4WS}
    (h : Phase4WSAt mem ws eCap S)
    (hbuf : DedupBufAt mem' (p4InInsSup ws eCap) (p4InsSup ws eCap) (p4InsLen ws eCap) eCap
      (pushDedup S.insSup e))
    (hfr : ∀ a, (a < p4InInsSup ws eCap ∨ p4InInsSup ws eCap + eCap ≤ a) →
      (a < p4InsSup ws eCap ∨ p4InsSup ws eCap + eCap ≤ a) → a ≠ p4InsLen ws eCap →
      mem' a = mem a) :
    Phase4WSAt mem' ws eCap { S with insSup := pushDedup S.insSup e } := by
  have hcb := copyBuf_length_le h
  obtain ⟨hD, hA, hT, hDS, -, hR, hSC, hnd, hcb', hcl, hclat⟩ := h
  have hfr' : ∀ a, (a < ws + 5 * eCap ∨ ws + 7 * eCap ≤ a) → a ≠ ws + 10 * eCap + 1 →
      mem' a = mem a := fun a ha hne => hfr a (by p4o) (by p4o) (by p4o)
  exact ⟨fun x hx => (hfr' _ (by p4o) (by p4o)).trans (hD x hx),
    fun x hx => (hfr' _ (by p4o) (by p4o)).trans (hA x hx),
    fun x hx => (hfr' _ (by p4o) (by p4o)).trans (hT x hx),
    dedupBufAt_of_agree_cap hDS (fun x hx => hfr' _ (by p4o) (by p4o))
      (fun x hx => hfr' _ (by p4o) (by p4o)) (hfr' _ (by p4o) (by p4o)), hbuf,
    dedupBufAt_of_agree_cap hR (fun x hx => hfr' _ (by p4o) (by p4o))
      (fun x hx => hfr' _ (by p4o) (by p4o)) (hfr' _ (by p4o) (by p4o)),
    fun x hx => (hfr' _ (by p4o) (by p4o)).trans (hSC x hx), hnd, hcb',
    (hfr' _ (by p4o) (by p4o)).trans hcl,
    fun i hi => (hfr' _ (by p4o) (by p4o)).trans (hclat i hi)⟩

/-! ## The parts of the run -/

/-- The setup puts the places of the workspace into registers and changes nothing else. -/
private theorem p4Edge_setup_runs {w gEPres hEPres ws eCap e fD fDel fIns fCopy pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem₀ : ℕ → ℕ} (hw16 : 16 ≤ 2 ^ w)
    (hws_w : ws + p4WsSize eCap < 2 ^ w) :
    ∃ o st₁ c, Runs w p ω asmFirstP4EdgeSetup
        (startState [gEPres, hEPres, ws, eCap, e, fD, fDel, fIns, fCopy] mem₀ pos) o st₁ c ∧
      (o = .normal ∧ st₁.mem = mem₀ ∧ st₁.regs 0 = gEPres ∧ st₁.regs 1 = hEPres ∧
        st₁.regs 2 = ws ∧ st₁.regs 4 = e ∧ st₁.regs 5 = fD ∧ st₁.regs 6 = fDel ∧
        st₁.regs 7 = fIns ∧ st₁.regs 8 = fCopy ∧ st₁.regs 9 = p4SeenCopy ws eCap ∧
        st₁.regs 10 = p4InAct ws eCap ∧ st₁.regs 11 = p4CopyLen ws eCap ∧
        st₁.regs 12 = p4CopyBuf ws eCap ∧ st₁.regs 13 = p4InTgt ws eCap ∧ st₁.regs 14 = e ∧
        st₁.regs 17 = p4InDelSup ws eCap ∧ st₁.regs 18 = p4DelSup ws eCap ∧
        st₁.regs 19 = p4DelLen ws eCap ∧ st₁.regs 20 = p4InInsSup ws eCap ∧
        st₁.regs 21 = p4InsSup ws eCap ∧ st₁.regs 22 = p4InsLen ws eCap) ∧
      0 + c ≤ 70 := by
  have hws' : ws + 11 * eCap + 4 < 2 ^ w := by simp only [p4WsSize] at hws_w; omega
  unfold asmFirstP4EdgeSetup
  wram_run
  · simp only [Function.update_apply, startState, p4SeenCopy, p4InAct, p4CopyLen, p4CopyBuf,
      p4InTgt, p4InDelSup, p4DelSup, p4DelLen, p4InInsSup, p4InsSup, p4InsLen]
    simp
    omega
  · wram_cost

/-- Part 1: add `e` to `inDtot` if `fD ≠ 0`. -/
private theorem p4Edge_dtot_runs {w ws eCap e fD : ℕ} {p : Program} {ω : ℕ → Bool}
    {S : Phase4WS} {st : State} (hw16 : 16 ≤ 2 ^ w) (hws_w : ws + p4WsSize eCap < 2 ^ w)
    (he : e < eCap) (hr2 : st.regs 2 = ws) (hr4 : st.regs 4 = e) (hr5 : st.regs 5 = fD)
    (hW : Phase4WSAt st.mem ws eCap S) :
    ∃ st' c, Runs w p ω (.cond (.reg 5) (.store (.bin .add (.reg 2) (.reg 4)) (.const 1)) .nop)
        st .normal st' c ∧ st'.regs = st.regs ∧
      Phase4WSAt st'.mem ws eCap
        (if decide (fD ≠ 0) = true then { S with inDtot := insert e S.inDtot } else S) ∧
      (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st'.mem a = st.mem a) ∧ c ≤ 10 := by
  have h1w : 1 < 2 ^ w := by omega
  by_cases h0 : fD = 0
  · refine ⟨st, _, runs_cond_iff.mpr ⟨0, 1, Expr.eval_reg_of_eq (hr5.trans h0),
      by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩, rfl, by simpa [h0] using hW,
      fun _ _ => rfl, by simp [Expr.size]⟩
  · refine ⟨⟨Function.update st.mem (ws + e) 1, st.regs, st.pos⟩, _,
      runs_cond_iff.mpr ⟨fD, 5, Expr.eval_reg_of_eq hr5, ?_, rfl⟩, rfl,
      by simpa [h0] using phase4WSAt_dtot hW he, fun a ha => ?_, by simp [Expr.size]⟩
    · simp only [h0, ↓reduceIte]
      exact runs_store_iff.mpr ⟨ws + e, 1, Expr.eval_add (Expr.eval_reg_of_eq hr2)
        (Expr.eval_reg_of_eq hr4) (by p4o), Expr.eval_const h1w, rfl, rfl, rfl⟩
    · exact Function.update_of_ne (by p4o) _ _

/-- Part 2: mark `e` from the presence arrays of the slot's graph and spanner. -/
private theorem p4Edge_mark_runs {w fMark gEPres hEPres ws eCap e : ℕ} {p : Program}
    {ω : ℕ → Bool} (hfMark : p.procs[fMark]? = some asmFirstMarkSlotEdgeStmt)
    {GE HE : Finset ℕ} {S : Phase4WS} {st : State} (hw16 : 16 ≤ 2 ^ w)
    (hr0 : st.regs 0 = gEPres) (hr1 : st.regs 1 = hEPres) (hr10 : st.regs 10 = p4InAct ws eCap)
    (hr13 : st.regs 13 = p4InTgt ws eCap) (hr4 : st.regs 4 = e)
    (hW : Phase4WSAt st.mem ws eCap S)
    (hGE : st.mem (gEPres + e) = if e ∈ GE then 1 else 0)
    (hHE : st.mem (hEPres + e) = if e ∈ HE then 1 else 0) (he : e < eCap)
    (hh_disj : hEPres + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ hEPres)
    (hg_w : gEPres + eCap < 2 ^ w) (hh_w : hEPres + eCap < 2 ^ w)
    (hws_w : ws + p4WsSize eCap < 2 ^ w) :
    ∃ st' c, Runs w p ω (.call 15 fMark [.reg 0, .reg 1, .reg 10, .reg 13, .reg 4])
        st .normal st' c ∧ (∀ r, r ≠ 15 → st'.regs r = st.regs r) ∧
      Phase4WSAt st'.mem ws eCap (p4Mark GE HE S e) ∧
      (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st'.mem a = st.mem a) ∧ c ≤ 40 := by
  obtain ⟨stM, cM, hrM, hin, hout, hfr, hcM⟩ := asmFirstMarkSlotEdge_runs (p := p) (ω := ω)
    (pos := st.pos) (inActPtr := p4InAct ws eCap) (inTgtPtr := p4InTgt ws eCap)
    hw16 he hGE hHE (by p4o) (by p4o) hg_w hh_w (by p4o) (by p4o)
  have hargs : evalArgs w st [.reg 0, .reg 1, .reg 10, .reg 13, .reg 4] =
      some [gEPres, hEPres, p4InAct ws eCap, p4InTgt ws eCap, e] :=
    evalArgs_cons (Expr.eval_reg_of_eq hr0) <| evalArgs_cons (Expr.eval_reg_of_eq hr1) <|
    evalArgs_cons (Expr.eval_reg_of_eq hr10) <| evalArgs_cons (Expr.eval_reg_of_eq hr13) <|
    evalArgs_cons (Expr.eval_reg_of_eq hr4) <| evalArgs_nil _ _
  refine ⟨⟨stM.mem, Function.update st.regs 15 0, stM.pos⟩, _,
    runs_call_iff.mpr ⟨_, _, .returned 0, stM, cM, hargs, hfMark, hrM, rfl, rfl, rfl⟩,
    fun r hr => by simp [hr], phase4WSAt_mark hW he hin hout hfr,
    fun a ha => hfr a (by p4o) (by p4o), by simp only [argsSize, Expr.size]; omega⟩

/-- Part 3: push `e` into `delSup` if `fDel ≠ 0`. -/
private theorem p4Edge_del_runs {w fPush ws eCap e fDel : ℕ} {p : Program} {ω : ℕ → Bool}
    (hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt) {S : Phase4WS} {st : State}
    (hw16 : 16 ≤ 2 ^ w) (hws_w : ws + p4WsSize eCap < 2 ^ w) (he : e < eCap)
    (hr6 : st.regs 6 = fDel) (hr17 : st.regs 17 = p4InDelSup ws eCap)
    (hr18 : st.regs 18 = p4DelSup ws eCap) (hr19 : st.regs 19 = p4DelLen ws eCap)
    (hr4 : st.regs 4 = e) (hW : Phase4WSAt st.mem ws eCap S) :
    ∃ st' c, Runs w p ω
        (.cond (.reg 6) (.call 15 fPush [.reg 17, .reg 18, .reg 19, .reg 4]) .nop)
        st .normal st' c ∧ (∀ r, r ≠ 15 → st'.regs r = st.regs r) ∧
      Phase4WSAt st'.mem ws eCap
        (if decide (fDel ≠ 0) = true then { S with delSup := pushDedup S.delSup e } else S) ∧
      (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st'.mem a = st.mem a) ∧ c ≤ 45 := by
  by_cases h0 : fDel = 0
  · refine ⟨st, _, runs_cond_iff.mpr ⟨0, 1, Expr.eval_reg_of_eq (hr6.trans h0),
      by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩, fun _ _ => rfl,
      by simpa [h0] using hW, fun _ _ => rfl, by simp [Expr.size]⟩
  · obtain ⟨stP, cP, hrP, hbuf, hfr, hcP⟩ := asmFirstPushDedup_runs (p := p) (ω := ω)
      (pos := st.pos) hw16 hW.2.2.2.1 he (Or.inl (by p4o)) (Or.inr (by p4o)) (Or.inr (by p4o))
      (by p4o) (by p4o) (by p4o)
    have hargs : evalArgs w st [.reg 17, .reg 18, .reg 19, .reg 4] =
        some [p4InDelSup ws eCap, p4DelSup ws eCap, p4DelLen ws eCap, e] :=
      evalArgs_cons (Expr.eval_reg_of_eq hr17) <| evalArgs_cons (Expr.eval_reg_of_eq hr18) <|
      evalArgs_cons (Expr.eval_reg_of_eq hr19) <| evalArgs_cons (Expr.eval_reg_of_eq hr4) <|
      evalArgs_nil _ _
    refine ⟨⟨stP.mem, Function.update st.regs 15 0, stP.pos⟩, _,
      runs_cond_iff.mpr ⟨fDel, _, Expr.eval_reg_of_eq hr6, by
        simp only [h0, ↓reduceIte]
        exact runs_call_iff.mpr ⟨_, _, .returned 0, stP, cP, hargs, hfPush, hrP, rfl, rfl, rfl⟩,
        rfl⟩,
      fun r hr => by simp [hr], by simpa [h0] using phase4WSAt_pushDel hW hbuf hfr,
      fun a ha => hfr a (by p4o) (by p4o) (by p4o), by simp only [argsSize, Expr.size]; omega⟩

/-- Part 4: push `e` into `insSup` if `fIns ≠ 0`. -/
private theorem p4Edge_ins_runs {w fPush ws eCap e fIns : ℕ} {p : Program} {ω : ℕ → Bool}
    (hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt) {S : Phase4WS} {st : State}
    (hw16 : 16 ≤ 2 ^ w) (hws_w : ws + p4WsSize eCap < 2 ^ w) (he : e < eCap)
    (hr7 : st.regs 7 = fIns) (hr20 : st.regs 20 = p4InInsSup ws eCap)
    (hr21 : st.regs 21 = p4InsSup ws eCap) (hr22 : st.regs 22 = p4InsLen ws eCap)
    (hr4 : st.regs 4 = e) (hW : Phase4WSAt st.mem ws eCap S) :
    ∃ st' c, Runs w p ω
        (.cond (.reg 7) (.call 15 fPush [.reg 20, .reg 21, .reg 22, .reg 4]) .nop)
        st .normal st' c ∧ (∀ r, r ≠ 15 → st'.regs r = st.regs r) ∧
      Phase4WSAt st'.mem ws eCap
        (if decide (fIns ≠ 0) = true then { S with insSup := pushDedup S.insSup e } else S) ∧
      (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st'.mem a = st.mem a) ∧ c ≤ 45 := by
  by_cases h0 : fIns = 0
  · refine ⟨st, _, runs_cond_iff.mpr ⟨0, 1, Expr.eval_reg_of_eq (hr7.trans h0),
      by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩, fun _ _ => rfl,
      by simpa [h0] using hW, fun _ _ => rfl, by simp [Expr.size]⟩
  · obtain ⟨stP, cP, hrP, hbuf, hfr, hcP⟩ := asmFirstPushDedup_runs (p := p) (ω := ω)
      (pos := st.pos) hw16 hW.2.2.2.2.1 he (Or.inl (by p4o)) (Or.inr (by p4o))
      (Or.inr (by p4o)) (by p4o) (by p4o) (by p4o)
    have hargs : evalArgs w st [.reg 20, .reg 21, .reg 22, .reg 4] =
        some [p4InInsSup ws eCap, p4InsSup ws eCap, p4InsLen ws eCap, e] :=
      evalArgs_cons (Expr.eval_reg_of_eq hr20) <| evalArgs_cons (Expr.eval_reg_of_eq hr21) <|
      evalArgs_cons (Expr.eval_reg_of_eq hr22) <| evalArgs_cons (Expr.eval_reg_of_eq hr4) <|
      evalArgs_nil _ _
    refine ⟨⟨stP.mem, Function.update st.regs 15 0, stP.pos⟩, _,
      runs_cond_iff.mpr ⟨fIns, _, Expr.eval_reg_of_eq hr7, by
        simp only [h0, ↓reduceIte]
        exact runs_call_iff.mpr ⟨_, _, .returned 0, stP, cP, hargs, hfPush, hrP, rfl, rfl, rfl⟩,
        rfl⟩,
      fun r hr => by simp [hr], by simpa [h0] using phase4WSAt_pushIns hW hbuf hfr,
      fun a ha => hfr a (by p4o) (by p4o) (by p4o), by simp only [argsSize, Expr.size]; omega⟩

/-- Part 5: push `e` into the copy buffer if `fCopy ≠ 0`. -/
private theorem p4Edge_copy_runs {w ws eCap e fCopy : ℕ} {p : Program} {ω : ℕ → Bool}
    {S : Phase4WS} {st : State} (hw16 : 16 ≤ 2 ^ w) (hws_w : ws + p4WsSize eCap < 2 ^ w)
    (he : e < eCap) (hr8 : st.regs 8 = fCopy) (hr9 : st.regs 9 = p4SeenCopy ws eCap)
    (hr11 : st.regs 11 = p4CopyLen ws eCap) (hr12 : st.regs 12 = p4CopyBuf ws eCap)
    (hr14 : st.regs 14 = e) (hW : Phase4WSAt st.mem ws eCap S) :
    ∃ st' c, Runs w p ω (.cond (.reg 8) p4PushCopyBlock .nop) st .normal st' c ∧
      (∀ r, r ≠ 16 → st'.regs r = st.regs r) ∧
      Phase4WSAt st'.mem ws eCap (if decide (fCopy ≠ 0) = true then pushCopy S e else S) ∧
      (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st'.mem a = st.mem a) ∧ c ≤ 35 := by
  by_cases h0 : fCopy = 0
  · refine ⟨st, _, runs_cond_iff.mpr ⟨0, 1, Expr.eval_reg_of_eq (hr8.trans h0),
      by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩, fun _ _ => rfl,
      by simpa [h0] using hW, fun _ _ => rfl, by simp [Expr.size]⟩
  · obtain ⟨st', c, hr, hregs, hW', hfr, -, -, hc⟩ :=
      p4PushCopy_runs (p := p) (ω := ω) hw16 hws_w he hr9 hr11 hr12 hr14 hW
    exact ⟨st', _, runs_cond_iff.mpr ⟨fCopy, c, Expr.eval_reg_of_eq hr8,
      by simp only [h0, ↓reduceIte]; exact hr, rfl⟩, hregs, by simpa [h0] using hW', hfr,
      by simp only [Expr.size]; omega⟩

/-! ## The run -/

set_option maxHeartbeats 800000 in
/-- **The work on one edge.** From the workspace `S`, with the presence arrays of the slot's
graph `GE` and spanner `HE` outside the workspace, `asmFirstP4EdgeStmt` leaves the workspace
`p4StepEdge GE HE (fD ≠ 0) (fDel ≠ 0) (fIns ≠ 0) (fCopy ≠ 0) S e`, keeps every cell outside the
workspace, and costs at most `260`. -/
theorem asmFirstP4Edge_runs {w fPush fMark gEPres hEPres ws eCap e fD fDel fIns fCopy pos : ℕ}
    {p : Program}
    (hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt)
    (hfMark : p.procs[fMark]? = some asmFirstMarkSlotEdgeStmt)
    {GE HE : Finset ℕ} {S : Phase4WS} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hW : Phase4WSAt mem₀ ws eCap S)
    (hGE : ∀ e < eCap, mem₀ (gEPres + e) = if e ∈ GE then 1 else 0)
    (hHE : ∀ e < eCap, mem₀ (hEPres + e) = if e ∈ HE then 1 else 0)
    (he : e < eCap)
    (hg_disj : gEPres + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ gEPres)
    (hh_disj : hEPres + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ hEPres)
    (hg_w : gEPres + eCap < 2 ^ w) (hh_w : hEPres + eCap < 2 ^ w)
    (hws_w : ws + p4WsSize eCap < 2 ^ w) :
    ∃ st' cost,
      Runs w p ω (asmFirstP4EdgeStmt fPush fMark)
        (startState [gEPres, hEPres, ws, eCap, e, fD, fDel, fIns, fCopy] mem₀ pos)
        (.returned 0) st' cost ∧
      Phase4WSAt st'.mem ws eCap
        (p4StepEdge GE HE (decide (fD ≠ 0)) (decide (fDel ≠ 0)) (decide (fIns ≠ 0))
          (decide (fCopy ≠ 0)) S e) ∧
      (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st'.mem a = mem₀ a) ∧
      cost ≤ 260 := by
  classical
  have h0w : 0 < 2 ^ w := by omega
  obtain ⟨o₁, st₁, c₁, hr₁, ⟨rfl, hm₁, h0, h1, h2, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h17, h18, h19, h20, h21, h22⟩, hc₁⟩ :=
    p4Edge_setup_runs (p := p) (ω := ω) (gEPres := gEPres) (hEPres := hEPres) (e := e)
      (fD := fD) (fDel := fDel) (fIns := fIns) (fCopy := fCopy) (pos := pos) (mem₀ := mem₀)
      hw16 hws_w
  obtain ⟨st₂, c₂, hr₂, hR₂, hW₂, hF₂, hc₂⟩ :=
    p4Edge_dtot_runs (p := p) (ω := ω) hw16 hws_w he h2 h4 h5 (hm₁ ▸ hW)
  have hF₂' : ∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st₂.mem a = mem₀ a := fun a ha =>
    (hF₂ a ha).trans (congrFun hm₁ a)
  rw [← hR₂] at h0 h1 h4 h6 h7 h8 h9 h10 h11 h12 h13 h14 h17 h18 h19 h20 h21 h22
  obtain ⟨st₃, c₃, hr₃, hR₃, hW₃, hF₃, hc₃⟩ :=
    p4Edge_mark_runs (p := p) (ω := ω) (GE := GE) (HE := HE) hfMark hw16 h0 h1 h10 h13 h4 hW₂
      ((hF₂' _ (by p4o)).trans (hGE e he)) ((hF₂' _ (by p4o)).trans (hHE e he)) he hh_disj
      hg_w hh_w hws_w
  rw [← hR₃ _ (by decide)] at h4 h6 h7 h8 h9 h11 h12 h14 h17 h18 h19 h20 h21 h22
  obtain ⟨st₄, c₄, hr₄, hR₄, hW₄, hF₄, hc₄⟩ :=
    p4Edge_del_runs (p := p) (ω := ω) hfPush hw16 hws_w he h6 h17 h18 h19 h4 hW₃
  rw [← hR₄ _ (by decide)] at h4 h7 h8 h9 h11 h12 h14 h20 h21 h22
  obtain ⟨st₅, c₅, hr₅, hR₅, hW₅, hF₅, hc₅⟩ :=
    p4Edge_ins_runs (p := p) (ω := ω) hfPush hw16 hws_w he h7 h20 h21 h22 h4 hW₄
  rw [← hR₅ _ (by decide)] at h8 h9 h11 h12 h14
  obtain ⟨st₆, c₆, hr₆, -, hW₆, hF₆, hc₆⟩ :=
    p4Edge_copy_runs (p := p) (ω := ω) hw16 hws_w he h8 h9 h11 h12 h14 hW₅
  have hret : Runs w p ω (.ret (.const 0)) st₆ (.returned 0) st₆ 2 :=
    runs_ret_iff.mpr ⟨0, Expr.eval_const h0w, rfl, rfl, rfl⟩
  refine ⟨st₆, _,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr₁, runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr₂,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr₃, runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr₄,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr₅, runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr₆,
          hret, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    hW₆, fun a ha => (hF₆ a ha).trans <| (hF₅ a ha).trans <| (hF₄ a ha).trans <|
      (hF₃ a ha).trans (hF₂' a ha), by omega⟩

end

end MinCostFlow.SparseCore.Program
