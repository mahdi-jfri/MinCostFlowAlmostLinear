module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSlotScanD

import WordRAM.Tactic

/-!
# Verification of the per-slot `D` workspace scanner (`AssemblyFirstStepSlotScanProof`)

Defines the pure one-edge updates of the workspace (`p4StepD`, `p4StepR`, `p4StepNew`) for the
three scanners of `AssemblyFirstStepSlotScanD.lean`, and proves the first one,
`asmFirstScanSlotD_runs`: it scans `D` of an updated slot, adds `D` to `inDtot`, `delSup` and
`insSup`, and updates `inAct`/`inTgt` on `D ∩ GE`, in `≤ 170 * dL.length + 60` steps. It leaves
memory untouched outside `[ws, ws + p4WsSize eCap)`. The other two scanners are proved in
`AssemblyFirstStepSlotScanR.lean` and `AssemblyFirstStepSlotScanNew.lean`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

/-- Unfolds the places of the Phase 4 workspace and closes the goal by `omega`. -/
local macro "p4o" : tactic => `(tactic| ((try simp only [p4WsSize, p4InDtot, p4InAct, p4InTgt,
  p4InDelSup, p4DelSup, p4InInsSup, p4InsSup, p4InReemb, p4Reemb, p4SeenCopy, p4DelLen, p4InsLen,
  p4ReembLen, p4CopyLen, p4CopyBuf] at *) <;> omega))

public section

/-- Pure `Phase4WS` update for one element `e` of `D`. -/
@[expose] noncomputable def p4StepD (GE HE : Finset ℕ) (S : Phase4WS) (e : ℕ) : Phase4WS :=
  open Classical in
  { S with
    inDtot := insert e S.inDtot
    inAct := if e ∈ GE then insert e S.inAct else S.inAct
    inTgt := if e ∈ GE then (if e ∈ HE then insert e S.inTgt else S.inTgt.erase e) else S.inTgt
    delSup := pushDedup S.delSup e
    insSup := pushDedup S.insSup e }

/-- Pure `Phase4WS` update for one element `e` of `R`. -/
@[expose] noncomputable def p4StepR (GE HE : Finset ℕ) (isOld : Bool) (S : Phase4WS) (e : ℕ) : Phase4WS :=
  open Classical in
  let S1 := { S with reemb := pushDedup S.reemb e }
  if isOld ∧ e ∈ GE ∧ e ∉ HE then pushCopy S1 e else S1

/-- Pure `Phase4WS` update for one element `e` of a newly active slot's `G.eList`. -/
@[expose] noncomputable def p4StepNew (HE : Finset ℕ) (S : Phase4WS) (e : ℕ) : Phase4WS :=
  open Classical in
  let S1 := { S with
    inAct := insert e S.inAct
    inTgt := if e ∈ HE then insert e S.inTgt else S.inTgt.erase e
    insSup := pushDedup S.insSup e }
  if e ∉ HE then pushCopy S1 e else S1

/-! ## 1. `asmFirstScanSlotD_runs` -/

set_option maxHeartbeats 600000 in
theorem asmFirstScanSlotD_runs {w fPush fMark gEPres hEPres dPtr ws eCap pos : ℕ} {p : Program}
    (hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt)
    (hfMark : p.procs[fMark]? = some asmFirstMarkSlotEdgeStmt)
    {GE HE : Finset ℕ} {dL : List ℕ} {S₀ : Phase4WS} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hW : Phase4WSAt mem₀ ws eCap S₀)
    (hGE : ∀ e < eCap, mem₀ (gEPres + e) = if e ∈ GE then 1 else 0)
    (hHE : ∀ e < eCap, mem₀ (hEPres + e) = if e ∈ HE then 1 else 0)
    (hDL : ListAt mem₀ dPtr dL) (hDL_cap : ∀ e ∈ dL, e < eCap)
    (hg_disj : gEPres + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ gEPres)
    (hh_disj : hEPres + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ hEPres)
    (hd_disj : dPtr + dL.length ≤ ws ∨ ws + p4WsSize eCap ≤ dPtr)
    (hg_w : gEPres + eCap < 2 ^ w) (hh_w : hEPres + eCap < 2 ^ w)
    (hd_w : dPtr + dL.length < 2 ^ w) (hws_w : ws + p4WsSize eCap < 2 ^ w) :
    ∃ st' cost,
      Runs w p ω (asmFirstScanSlotDStmt fPush fMark)
        (startState [gEPres, hEPres, dPtr, dL.length, ws, eCap] mem₀ pos) (.returned 0) st' cost ∧
      Phase4WSAt st'.mem ws eCap (dL.foldl (p4StepD GE HE) S₀) ∧
      (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st'.mem a = mem₀ a) ∧
      cost ≤ 170 * dL.length + 60 := by
  classical
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have h10w : 10 < 2 ^ w := by omega
  have hws_un : ws + 11 * eCap + 4 < 2 ^ w := by unfold p4WsSize at hws_w; omega
  set s0 := startState [gEPres, hEPres, dPtr, dL.length, ws, eCap] mem₀ pos
  set r6 := Function.update s0.regs 6 (p4InAct ws eCap)
  set r7 := Function.update r6 7 (p4InTgt ws eCap)
  set r8 := Function.update r7 8 (p4InDelSup ws eCap)
  set r9 := Function.update r8 9 (p4DelSup ws eCap)
  set r10 := Function.update r9 10 (p4InInsSup ws eCap)
  set r11 := Function.update r10 11 (p4InsSup ws eCap)
  set r12 := Function.update r11 12 (p4DelLen ws eCap)
  set r13 := Function.update r12 13 (p4InsLen ws eCap)
  have hsetup : ∃ c0, Runs w p ω
      (.assign 6 (.bin .add (.reg 4) (.reg 5)) ;;
       .assign 7 (.bin .add (.reg 6) (.reg 5)) ;;
       .assign 8 (.bin .add (.reg 7) (.reg 5)) ;;
       .assign 9 (.bin .add (.reg 8) (.reg 5)) ;;
       .assign 10 (.bin .add (.reg 9) (.reg 5)) ;;
       .assign 11 (.bin .add (.reg 10) (.reg 5)) ;;
       .assign 12 (.bin .add (.reg 4) (.bin .mul (.const 10) (.reg 5))) ;;
       .assign 13 (.bin .add (.reg 12) (.const 1)))
      s0 .normal ⟨mem₀, r13, pos⟩ c0 ∧ c0 ≤ 45 := by
    have a6 : Runs w p ω (.assign 6 (.bin .add (.reg 4) (.reg 5))) s0 .normal ⟨mem₀, r6, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨p4InAct ws eCap, Expr.eval_add (Expr.eval_reg_of_eq (by simp [s0, startState]))
        (Expr.eval_reg_of_eq (by simp [s0, startState])) (by omega), rfl, rfl, rfl⟩
    have a7 : Runs w p ω (.assign 7 (.bin .add (.reg 6) (.reg 5))) ⟨mem₀, r6, pos⟩ .normal ⟨mem₀, r7, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨p4InTgt ws eCap, by
        have h6 : r6 6 = ws + eCap := by simp [r6, p4InAct]
        have h5 : r6 5 = eCap := by simp [r6, s0, startState]
        have he : (Expr.bin .add (.reg 6) (.reg 5)).eval w ⟨mem₀, r6, pos⟩ = some (ws + eCap + eCap) :=
          Expr.eval_add (Expr.eval_reg_of_eq h6) (Expr.eval_reg_of_eq h5) (by omega)
        simpa [p4InTgt, show ws + eCap + eCap = ws + 2 * eCap by omega] using he, rfl, rfl, rfl⟩
    have a8 : Runs w p ω (.assign 8 (.bin .add (.reg 7) (.reg 5))) ⟨mem₀, r7, pos⟩ .normal ⟨mem₀, r8, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨p4InDelSup ws eCap, by
        have h7 : r7 7 = ws + 2 * eCap := by simp [r7, p4InTgt]
        have h5 : r7 5 = eCap := by simp [r7, r6, s0, startState]
        have he : (Expr.bin .add (.reg 7) (.reg 5)).eval w ⟨mem₀, r7, pos⟩ = some (ws + 2 * eCap + eCap) :=
          Expr.eval_add (Expr.eval_reg_of_eq h7) (Expr.eval_reg_of_eq h5) (by omega)
        simpa [p4InDelSup, show ws + 2 * eCap + eCap = ws + 3 * eCap by omega] using he, rfl, rfl, rfl⟩
    have a9 : Runs w p ω (.assign 9 (.bin .add (.reg 8) (.reg 5))) ⟨mem₀, r8, pos⟩ .normal ⟨mem₀, r9, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨p4DelSup ws eCap, by
        have h8 : r8 8 = ws + 3 * eCap := by simp [r8, p4InDelSup]
        have h5 : r8 5 = eCap := by simp [r8, r7, r6, s0, startState]
        have he : (Expr.bin .add (.reg 8) (.reg 5)).eval w ⟨mem₀, r8, pos⟩ = some (ws + 3 * eCap + eCap) :=
          Expr.eval_add (Expr.eval_reg_of_eq h8) (Expr.eval_reg_of_eq h5) (by omega)
        simpa [p4DelSup, show ws + 3 * eCap + eCap = ws + 4 * eCap by omega] using he, rfl, rfl, rfl⟩
    have a10 : Runs w p ω (.assign 10 (.bin .add (.reg 9) (.reg 5))) ⟨mem₀, r9, pos⟩ .normal ⟨mem₀, r10, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨p4InInsSup ws eCap, by
        have h9 : r9 9 = ws + 4 * eCap := by simp [r9, p4DelSup]
        have h5 : r9 5 = eCap := by simp [r9, r8, r7, r6, s0, startState]
        have he : (Expr.bin .add (.reg 9) (.reg 5)).eval w ⟨mem₀, r9, pos⟩ = some (ws + 4 * eCap + eCap) :=
          Expr.eval_add (Expr.eval_reg_of_eq h9) (Expr.eval_reg_of_eq h5) (by omega)
        simpa [p4InInsSup, show ws + 4 * eCap + eCap = ws + 5 * eCap by omega] using he, rfl, rfl, rfl⟩
    have a11 : Runs w p ω (.assign 11 (.bin .add (.reg 10) (.reg 5))) ⟨mem₀, r10, pos⟩ .normal ⟨mem₀, r11, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨p4InsSup ws eCap, by
        have h10 : r10 10 = ws + 5 * eCap := by simp [r10, p4InInsSup]
        have h5 : r10 5 = eCap := by simp [r10, r9, r8, r7, r6, s0, startState]
        have he : (Expr.bin .add (.reg 10) (.reg 5)).eval w ⟨mem₀, r10, pos⟩ = some (ws + 5 * eCap + eCap) :=
          Expr.eval_add (Expr.eval_reg_of_eq h10) (Expr.eval_reg_of_eq h5) (by omega)
        simpa [p4InsSup, show ws + 5 * eCap + eCap = ws + 6 * eCap by omega] using he, rfl, rfl, rfl⟩
    have a12 : Runs w p ω (.assign 12 (.bin .add (.reg 4) (.bin .mul (.const 10) (.reg 5))))
        ⟨mem₀, r11, pos⟩ .normal ⟨mem₀, r12, pos⟩ 6 := by
      have h4 : r11 4 = ws := by simp [r11, r10, r9, r8, r7, r6, s0, startState]
      have h5 : r11 5 = eCap := by simp [r11, r10, r9, r8, r7, r6, s0, startState]
      have hm : (Expr.bin .mul (.const 10) (.reg 5)).eval w ⟨mem₀, r11, pos⟩ = some (10 * eCap) :=
        Expr.eval_mul (Expr.eval_const h10w) (Expr.eval_reg_of_eq h5) (by omega)
      exact runs_assign_iff.mpr ⟨p4DelLen ws eCap, Expr.eval_add (Expr.eval_reg_of_eq h4) hm (by omega), rfl, rfl, rfl⟩
    have a13 : Runs w p ω (.assign 13 (.bin .add (.reg 12) (.const 1))) ⟨mem₀, r12, pos⟩ .normal ⟨mem₀, r13, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨p4InsLen ws eCap, Expr.eval_add (Expr.eval_reg_of_eq (by simp [r12, p4DelLen]))
        (Expr.eval_const h1w) (by p4o), rfl, rfl, rfl⟩
    exact ⟨_, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a6, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a7,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, a8, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a9,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, a10, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a11,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, a12, a13, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩
  obtain ⟨c0, hr0, hc0⟩ := hsetup
  let inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = gEPres ∧ st.regs 1 = hEPres ∧ st.regs 2 = dPtr ∧ st.regs 3 = dL.length ∧
    st.regs 4 = ws ∧ st.regs 6 = p4InAct ws eCap ∧ st.regs 7 = p4InTgt ws eCap ∧
    st.regs 8 = p4InDelSup ws eCap ∧ st.regs 9 = p4DelSup ws eCap ∧
    st.regs 10 = p4InInsSup ws eCap ∧ st.regs 11 = p4InsSup ws eCap ∧
    st.regs 12 = p4DelLen ws eCap ∧ st.regs 13 = p4InsLen ws eCap ∧ st.regs 14 = i ∧
    Phase4WSAt st.mem ws eCap ((dL.take i).foldl (p4StepD GE HE) S₀) ∧
    (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st.mem a = mem₀ a)
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 14) (lo := .const 0) (hi := .reg 3)
    (body := .assign 15 (.load (.bin .add (.reg 2) (.reg 14))) ;;
      .store (.bin .add (.reg 4) (.reg 15)) (.const 1) ;;
      .call 16 fMark [.reg 0, .reg 1, .reg 6, .reg 7, .reg 15] ;;
      .call 16 fPush [.reg 8, .reg 9, .reg 12, .reg 15] ;;
      .call 16 fPush [.reg 10, .reg 11, .reg 13, .reg 15])
    (P := fun st => inv 0 { st with regs := Function.update st.regs 14 0 })
    (Inv := inv) (fun _ => 150) 0 dL.length (Nat.zero_le _) h1w (fun _ => by omega)
    (fun st hI => ⟨Expr.eval_const h0w, hI⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.2.1)
    (fun i _ hi st ω' ⟨hr0', hr1', hr2', hr3', hr4', hr6', hr7', hr8', hr9', hr10', hr11', hr12', hr13', hr14', hWi, hfri⟩ => by
      set e := dL[i]'hi
      have heCap : e < eCap := hDL_cap e (List.getElem_mem hi)
      set Si := (dL.take i).foldl (p4StepD GE HE) S₀
      have hme : st.mem (dPtr + i) = e :=
        (hfri (dPtr + i) (by rcases hd_disj with h | h <;> omega)).trans (hDL i hi)
      set rA := Function.update st.regs 15 e
      set m1 := Function.update st.mem (ws + e) 1
      have h15 : Runs w p ω' (.assign 15 (.load (.bin .add (.reg 2) (.reg 14)))) st .normal ⟨st.mem, rA, st.pos⟩ 5 :=
        runs_assign_iff.mpr ⟨e, Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr2') (Expr.eval_reg_of_eq hr14') (by omega)) hme, rfl, rfl, rfl⟩
      have hs1 : Runs w p ω' (.store (.bin .add (.reg 4) (.reg 15)) (.const 1))
          ⟨st.mem, rA, st.pos⟩ .normal ⟨m1, rA, st.pos⟩ 5 :=
        runs_store_iff.mpr ⟨ws + e, 1,
          Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, hr4'])) (Expr.eval_reg_of_eq (by simp [rA])) (by omega),
          Expr.eval_const h1w, rfl, rfl, rfl⟩
      have hm1_g : m1 (gEPres + e) = if e ∈ GE then 1 else 0 := by
        dsimp only [m1]; rw [Function.update_of_ne (by p4o)]
        exact (hfri _ (by rcases hg_disj with h | h <;> omega)).trans (hGE e heCap)
      have hm1_h : m1 (hEPres + e) = if e ∈ HE then 1 else 0 := by
        dsimp only [m1]; rw [Function.update_of_ne (by p4o)]
        exact (hfri _ (by rcases hh_disj with h | h <;> omega)).trans (hHE e heCap)
      obtain ⟨stM, cM, hrM, hM_in, hM_out, hM_fr, hcM⟩ := asmFirstMarkSlotEdge_runs (p := p) (ω := ω') (pos := st.pos)
        (inActPtr := p4InAct ws eCap) (inTgtPtr := p4InTgt ws eCap)
        hw16 heCap hm1_g hm1_h
        (by p4o)
        (by p4o) hg_w hh_w (by p4o) (by p4o)
      have hm1_outside : ∀ a, ws + eCap ≤ a → m1 a = st.mem a := fun a ha => by
        dsimp only [m1]; rw [Function.update_of_ne (by omega)]
      have hstM_outside : ∀ a, a < p4InAct ws eCap ∨ p4InDelSup ws eCap ≤ a → stM.mem a = m1 a := fun a ha =>
        hM_fr a (by p4o)
          (by p4o)
      have hDS_M : DedupBufAt stM.mem (p4InDelSup ws eCap) (p4DelSup ws eCap) (p4DelLen ws eCap) eCap Si.delSup :=
        dedupBufAt_of_agree hWi.2.2.2.1
          (fun x hx => (hstM_outside _ (Or.inr (by simp [p4InDelSup]))).trans (hm1_outside _ (by p4o)))
          (fun j hj => have := dedupBuf_length_le hWi.2.2.2.1
            (hstM_outside _ (Or.inr (by p4o))).trans (hm1_outside _ (by p4o)))
          ((hstM_outside _ (Or.inr (by p4o))).trans (hm1_outside _ (by p4o)))
      obtain ⟨stP1, cP1, hrP1, hDS1, hfrP1, hcP1⟩ := asmFirstPushDedup_runs (p := p) (ω := ω') (pos := stM.pos)
        hw16 hDS_M heCap (Or.inl (by p4o))
        (Or.inr (by p4o)) (Or.inr (by p4o))
        (by p4o) (by p4o) (by p4o)
      have hIS_P1 : DedupBufAt stP1.mem (p4InInsSup ws eCap) (p4InsSup ws eCap) (p4InsLen ws eCap) eCap Si.insSup :=
        dedupBufAt_of_agree hWi.2.2.2.2.1
          (fun x hx => (hfrP1 _ (Or.inr (by p4o))
            (Or.inr (by p4o)) (by p4o)).trans
            ((hstM_outside _ (Or.inr (by p4o))).trans
              (hm1_outside _ (by p4o))))
          (fun j hj => have := dedupBuf_length_le hWi.2.2.2.2.1
            (hfrP1 _ (Or.inr (by p4o))
              (Or.inr (by p4o)) (by p4o)).trans
              ((hstM_outside _ (Or.inr (by p4o))).trans
                (hm1_outside _ (by p4o))))
          ((hfrP1 _ (Or.inr (by p4o))
            (Or.inr (by p4o)) (by p4o)).trans
            ((hstM_outside _ (Or.inr (by p4o))).trans
              (hm1_outside _ (by p4o))))
      obtain ⟨stP2, cP2, hrP2, hIS2, hfrP2, hcP2⟩ := asmFirstPushDedup_runs (p := p) (ω := ω') (pos := stP1.pos)
        hw16 hIS_P1 heCap (Or.inl (by p4o))
        (Or.inr (by p4o)) (Or.inr (by p4o))
        (by p4o) (by p4o) (by p4o)
      set rB := Function.update rA 16 0
      have heAM : evalArgs w ⟨m1, rA, st.pos⟩ [.reg 0, .reg 1, .reg 6, .reg 7, .reg 15] =
          some [gEPres, hEPres, p4InAct ws eCap, p4InTgt ws eCap, e] :=
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA, hr0'])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA, hr1'])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA, hr6'])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA, hr7'])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA])) <| evalArgs_nil _ _
      have hcM_run : Runs w p ω' (.call 16 fMark [.reg 0, .reg 1, .reg 6, .reg 7, .reg 15])
          ⟨m1, rA, st.pos⟩ .normal ⟨stM.mem, rB, stM.pos⟩
          (argsSize [.reg 0, .reg 1, .reg 6, .reg 7, .reg 15] + cM + 1) :=
        runs_call_iff.mpr ⟨_, asmFirstMarkSlotEdgeStmt, .returned 0, stM, cM, heAM, hfMark, hrM, rfl, rfl, rfl⟩
      have heAP1 : evalArgs w ⟨stM.mem, rB, stM.pos⟩ [.reg 8, .reg 9, .reg 12, .reg 15] =
          some [p4InDelSup ws eCap, p4DelSup ws eCap, p4DelLen ws eCap, e] :=
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, hr8'])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, hr9'])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, hr12'])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA])) <| evalArgs_nil _ _
      have hcP1_run : Runs w p ω' (.call 16 fPush [.reg 8, .reg 9, .reg 12, .reg 15])
          ⟨stM.mem, rB, stM.pos⟩ .normal ⟨stP1.mem, Function.update rB 16 0, stP1.pos⟩
          (argsSize [.reg 8, .reg 9, .reg 12, .reg 15] + cP1 + 1) :=
        runs_call_iff.mpr ⟨_, asmFirstPushDedupStmt, .returned 0, stP1, cP1, heAP1, hfPush, hrP1, rfl, rfl, rfl⟩
      have hrB_eq : Function.update rB 16 0 = rB := by simp [rB]
      rw [hrB_eq] at hcP1_run
      have heAP2 : evalArgs w ⟨stP1.mem, rB, stP1.pos⟩ [.reg 10, .reg 11, .reg 13, .reg 15] =
          some [p4InInsSup ws eCap, p4InsSup ws eCap, p4InsLen ws eCap, e] :=
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, hr10'])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, hr11'])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, hr13'])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA])) <| evalArgs_nil _ _
      have hcP2_run : Runs w p ω' (.call 16 fPush [.reg 10, .reg 11, .reg 13, .reg 15])
          ⟨stP1.mem, rB, stP1.pos⟩ .normal ⟨stP2.mem, rB, stP2.pos⟩
          (argsSize [.reg 10, .reg 11, .reg 13, .reg 15] + cP2 + 1) := by
        have h0 : Runs w p ω' (.call 16 fPush [.reg 10, .reg 11, .reg 13, .reg 15])
            ⟨stP1.mem, rB, stP1.pos⟩ .normal ⟨stP2.mem, Function.update rB 16 0, stP2.pos⟩
            (argsSize [.reg 10, .reg 11, .reg 13, .reg 15] + cP2 + 1) :=
          runs_call_iff.mpr ⟨_, asmFirstPushDedupStmt, .returned 0, stP2, cP2, heAP2, hfPush, hrP2, rfl, rfl, rfl⟩
        rwa [hrB_eq] at h0
      have htk : (dL.take (i + 1)).foldl (p4StepD GE HE) S₀ = p4StepD GE HE Si e := by
        rw [List.take_succ_eq_append_getElem hi, List.foldl_append]; rfl
      have hP2_keep_lt3 : ∀ a, a < p4InDelSup ws eCap → stP2.mem a = stM.mem a := fun a ha =>
        (hfrP2 a (Or.inl (by p4o))
          (Or.inl (by p4o))
          (by p4o)).trans
        (hfrP1 a (Or.inl ha) (Or.inl (by p4o))
          (by p4o))
      have hP2_keep_ge7 : ∀ a, p4InReemb ws eCap ≤ a → a ≠ p4DelLen ws eCap → a ≠ p4InsLen ws eCap →
          stP2.mem a = st.mem a := fun a ha hne1 hne2 =>
        (hfrP2 a (Or.inr (by p4o))
          (Or.inr (by p4o)) hne2).trans <|
        (hfrP1 a (Or.inr (by p4o))
          (Or.inr (by p4o)) hne1).trans <|
        (hstM_outside a (Or.inr (by p4o))).trans
          (hm1_outside a (by p4o))
      refine ⟨.normal, ⟨stP2.mem, rB, stP2.pos⟩, _,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, h15,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs1,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcM_run,
              runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcP1_run, hcP2_run, rfl⟩), rfl⟩), rfl⟩), rfl⟩),
        ⟨⟨by simp [rB, rA, hr0'], by simp [rB, rA, hr1'], by simp [rB, rA, hr2'], by simp [rB, rA, hr3'],
          by simp [rB, rA, hr4'], by simp [rB, rA, hr6'], by simp [rB, rA, hr7'], by simp [rB, rA, hr8'],
          by simp [rB, rA, hr9'], by simp [rB, rA, hr10'], by simp [rB, rA, hr11'], by simp [rB, rA, hr12'],
          by simp [rB, rA, hr13'], by simp, ?_, ?_⟩, by simp [rB, rA, hr14']⟩,
        by show _ ≤ 150; simp only [argsSize, Expr.size]; omega⟩
      · rw [htk]; dsimp only [p4StepD]
        refine ⟨fun e' he' => ?_, fun e' he' => ?_, fun e' he' => ?_,
          dedupBufAt_of_agree hDS1
            (fun x hx => hfrP2 _ (Or.inl (by p4o))
              (Or.inl (by p4o)) (by p4o))
            (fun j hj => have := dedupBuf_length_le hDS1
              hfrP2 _ (Or.inl (by p4o))
                (Or.inl (by p4o)) (by p4o))
            (hfrP2 _ (Or.inr (by p4o))
              (Or.inr (by p4o)) (by p4o)),
          hIS2,
          dedupBufAt_of_agree hWi.2.2.2.2.2.1
            (fun x hx => hP2_keep_ge7 _ (by simp [p4InReemb]) (by p4o) (by p4o))
            (fun j hj => have := dedupBuf_length_le hWi.2.2.2.2.2.1
              hP2_keep_ge7 _ (by p4o) (by p4o) (by p4o))
            (hP2_keep_ge7 _ (by p4o) (by p4o) (by p4o)),
          fun e' he' => (hP2_keep_ge7 _ (by p4o)
            (by p4o) (by p4o)).trans (hWi.2.2.2.2.2.2.1 e' he'),
          hWi.2.2.2.2.2.2.2.1, hWi.2.2.2.2.2.2.2.2.1,
          (hP2_keep_ge7 _ (by p4o)
            (by p4o) (by p4o)).trans hWi.2.2.2.2.2.2.2.2.2.1,
          fun j hj => (hP2_keep_ge7 _ (by p4o)
            (by p4o) (by p4o)).trans (hWi.2.2.2.2.2.2.2.2.2.2 j hj)⟩
        · rw [hP2_keep_lt3 _ (by p4o),
            hstM_outside _ (Or.inl (by p4o))]
          by_cases hee : e' = e
          · subst hee; simp [m1, p4InDtot]
          · simp only [p4InDtot, m1, Function.update_of_ne (by omega : ws + e' ≠ ws + e),
              Finset.mem_insert, hee, false_or]; exact hWi.1 e' he'
        · rw [hP2_keep_lt3 _ (by p4o)]
          by_cases hee : e' = e
          · subst hee; by_cases hG : e ∈ GE
            · simp [(hM_in hG).1, hG]
            · rw [hM_out hG, hm1_outside _ (by p4o)]; simp [hG, hWi.2.1 e heCap]
          · rw [hM_fr _ (by omega) (by p4o), hm1_outside _ (by p4o)]
            by_cases hG : e ∈ GE <;> simp [hG, hee, hWi.2.1 e' he']
        · rw [hP2_keep_lt3 _ (by p4o)]
          by_cases hee : e' = e
          · subst hee; by_cases hG : e ∈ GE
            · rw [(hM_in hG).2]; by_cases hH : e ∈ HE <;> simp [hG, hH]
            · rw [hM_out hG, hm1_outside _ (by p4o)]; simp [hG, hWi.2.2.1 e heCap]
          · rw [hM_fr _ (by p4o) (by omega), hm1_outside _ (by p4o)]
            by_cases hG : e ∈ GE
            · by_cases hH : e ∈ HE <;> simp [hG, hH, hee, hWi.2.2.1 e' he']
            · simp [hG, hWi.2.2.1 e' he']
      · intro a ha
        have h1 : stP2.mem a = st.mem a := by
          rcases ha with hlt | hge
          · rw [hP2_keep_lt3 a (by p4o),
              hstM_outside a (Or.inl (by p4o))]
            dsimp only [m1]; rw [Function.update_of_ne (by omega)]
          · exact hP2_keep_ge7 a (by p4o)
              (by p4o) (by p4o)
        exact h1.trans (hfri a ha))
  obtain ⟨o, st1, c1, hr1, hpost1, hc1⟩ := hloop ⟨mem₀, r13, pos⟩ ω
    ⟨by simp [r13, r12, r11, r10, r9, r8, r7, r6, s0, startState],
     by simp [r13, r12, r11, r10, r9, r8, r7, r6, s0, startState],
     by simp [r13, r12, r11, r10, r9, r8, r7, r6, s0, startState],
     by simp [r13, r12, r11, r10, r9, r8, r7, r6, s0, startState],
     by simp [r13, r12, r11, r10, r9, r8, r7, r6, s0, startState],
     by simp [r13, r12, r11, r10, r9, r8, r7, r6], by simp [r13, r12, r11, r10, r9, r8, r7],
     by simp [r13, r12, r11, r10, r9, r8], by simp [r13, r12, r11, r10, r9],
     by simp [r13, r12, r11, r10], by simp [r13, r12, r11], by simp [r13, r12],
     by simp [r13], by simp, by simpa using hW, fun _ _ => rfl⟩
  cases o with
  | returned _ => cases hpost1
  | normal =>
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hWf, hfrf⟩ := hpost1
  rw [List.take_length] at hWf
  have hret : Runs w p ω (.ret (.const 0)) st1 (.returned 0) st1 2 :=
    runs_ret_iff.mpr ⟨0, Expr.eval_const h0w, rfl, rfl, rfl⟩
  have hrc : rangeCost (fun _ => 150) 0 dL.length = 150 * dL.length := by
    simp [rangeCost, Nat.mul_comm]
  dsimp only at hc1; simp only [hrc, Nat.sub_zero, Expr.size] at hc1
  rcases (runs_seq_iff.mp hr0).resolve_left (by simp) with ⟨_, _, _, a6, hr0_1, rfl⟩
  rcases (runs_seq_iff.mp hr0_1).resolve_left (by simp) with ⟨_, _, _, a7, hr0_2, rfl⟩
  rcases (runs_seq_iff.mp hr0_2).resolve_left (by simp) with ⟨_, _, _, a8, hr0_3, rfl⟩
  rcases (runs_seq_iff.mp hr0_3).resolve_left (by simp) with ⟨_, _, _, a9, hr0_4, rfl⟩
  rcases (runs_seq_iff.mp hr0_4).resolve_left (by simp) with ⟨_, _, _, a10, hr0_5, rfl⟩
  rcases (runs_seq_iff.mp hr0_5).resolve_left (by simp) with ⟨_, _, _, a11, hr0_6, rfl⟩
  rcases (runs_seq_iff.mp hr0_6).resolve_left (by simp) with ⟨_, _, _, a12, a13, rfl⟩
  exact ⟨st1, _,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, a6, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a7,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, a8, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a9,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, a10, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a11,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, a12, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a13,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr1, hret, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    hWf, hfrf, by omega⟩

end

end MinCostFlow.SparseCore.Program
