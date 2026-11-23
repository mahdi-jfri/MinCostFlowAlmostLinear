module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSlotScanR

import WordRAM.Tactic

/-!
# Verification of the newly-active-slot `G.eList` scanner (`AssemblyFirstStepSlotScanNew`)

Verifies `asmFirstScanNewSlotStmt fPush` (`AssemblyFirstStepSlotScanD.lean`):
given a newly active slot's `G.eList` (`ListAt mem₀ gEList gL`) and `H.ePres` (`HE`), resets
`copyBuf := []`, sets `inAct[e] := 1` and `inTgt[e] := H.ePres[e]` for every `e ∈ gL`, pushes `e`
into `insSup`, and pushes `e` into `copyBuf` whenever `e ∉ HE`, in `≤ 135 * gL.length + 75` steps,
leaving all memory outside `[ws, ws + p4WsSize eCap)` untouched.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

/-- Unfolds the places of the Phase 4 workspace and closes the goal by `omega`. -/
local macro "p4o" : tactic => `(tactic| ((try simp only [p4WsSize, p4InDtot, p4InAct, p4InTgt,
  p4InDelSup, p4DelSup, p4InInsSup, p4InsSup, p4InReemb, p4Reemb, p4SeenCopy, p4DelLen, p4InsLen,
  p4ReembLen, p4CopyLen, p4CopyBuf] at *) <;> omega))

public section

set_option maxHeartbeats 600000 in
theorem asmFirstScanNewSlot_runs {w fPush gEList hEPres ws eCap pos : ℕ} {p : Program}
    (hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt)
    {HE : Finset ℕ} {gL : List ℕ} {S₀ : Phase4WS} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hW : Phase4WSAt mem₀ ws eCap S₀)
    (hGL : ListAt mem₀ gEList gL) (hGL_cap : ∀ e ∈ gL, e < eCap)
    (hHE : ∀ e < eCap, mem₀ (hEPres + e) = if e ∈ HE then 1 else 0)
    (hg_disj : gEList + gL.length ≤ ws ∨ ws + p4WsSize eCap ≤ gEList)
    (hh_disj : hEPres + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ hEPres)
    (hg_w : gEList + gL.length < 2 ^ w) (hh_w : hEPres + eCap < 2 ^ w)
    (hws_w : ws + p4WsSize eCap < 2 ^ w) :
    ∃ st' cost,
      Runs w p ω (asmFirstScanNewSlotStmt fPush)
        (startState [gEList, gL.length, hEPres, ws, eCap] mem₀ pos) (.returned 0) st' cost ∧
      Phase4WSAt st'.mem ws eCap (gL.foldl (p4StepNew HE) { S₀ with copyBuf := [] }) ∧
      (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st'.mem a = mem₀ a) ∧
      cost ≤ 135 * gL.length + 75 := by
  classical
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h5w : 5 < 2 ^ w := by omega
  have h9w : 9 < 2 ^ w := by omega
  have h10w : 10 < 2 ^ w := by omega
  have hws_un : ws + 11 * eCap + 4 < 2 ^ w := by unfold p4WsSize at hws_w; omega
  set s0 := startState [gEList, gL.length, hEPres, ws, eCap] mem₀ pos
  set r5 := Function.update s0.regs 5 (p4InAct ws eCap)
  set r6 := Function.update r5 6 (p4InTgt ws eCap)
  set r7 := Function.update r6 7 (p4InInsSup ws eCap)
  set r8 := Function.update r7 8 (p4InsSup ws eCap)
  set r9 := Function.update r8 9 (p4SeenCopy ws eCap)
  set r10 := Function.update r9 10 (p4InsLen ws eCap)
  set r11 := Function.update r10 11 (p4CopyLen ws eCap)
  set r12 := Function.update r11 12 (p4CopyBuf ws eCap)
  set m0 := Function.update mem₀ (p4CopyLen ws eCap) 0
  have hsetup : ∃ c0, Runs w p ω
      (.assign 5 (.bin .add (.reg 3) (.reg 4)) ;;
       .assign 6 (.bin .add (.reg 5) (.reg 4)) ;;
       .assign 7 (.bin .add (.reg 3) (.bin .mul (.const 5) (.reg 4))) ;;
       .assign 8 (.bin .add (.reg 7) (.reg 4)) ;;
       .assign 9 (.bin .add (.reg 3) (.bin .mul (.const 9) (.reg 4))) ;;
       .assign 10 (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 10) (.reg 4))) (.const 1)) ;;
       .assign 11 (.bin .add (.reg 10) (.const 2)) ;;
       .assign 12 (.bin .add (.reg 11) (.const 1)) ;;
       .store (.reg 11) (.const 0))
      s0 .normal ⟨m0, r12, pos⟩ c0 ∧ c0 ≤ 55 := by
    have a5 : Runs w p ω (.assign 5 (.bin .add (.reg 3) (.reg 4))) s0 .normal ⟨mem₀, r5, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨p4InAct ws eCap, Expr.eval_add (Expr.eval_reg_of_eq (by simp [s0, startState]))
        (Expr.eval_reg_of_eq (by simp [s0, startState])) (by omega), rfl, rfl, rfl⟩
    have a6 : Runs w p ω (.assign 6 (.bin .add (.reg 5) (.reg 4))) ⟨mem₀, r5, pos⟩ .normal ⟨mem₀, r6, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨p4InTgt ws eCap, by
        have h5r : r5 5 = ws + eCap := by simp [r5, p4InAct]
        have h4r : r5 4 = eCap := by simp [r5, s0, startState]
        have he : (Expr.bin .add (.reg 5) (.reg 4)).eval w ⟨mem₀, r5, pos⟩ = some (ws + eCap + eCap) :=
          Expr.eval_add (Expr.eval_reg_of_eq h5r) (Expr.eval_reg_of_eq h4r) (by omega)
        simpa [p4InTgt, show ws + eCap + eCap = ws + 2 * eCap by omega] using he, rfl, rfl, rfl⟩
    have a7 : Runs w p ω (.assign 7 (.bin .add (.reg 3) (.bin .mul (.const 5) (.reg 4))))
        ⟨mem₀, r6, pos⟩ .normal ⟨mem₀, r7, pos⟩ 6 := by
      have h3r : r6 3 = ws := by simp [r6, r5, s0, startState]
      have h4r : r6 4 = eCap := by simp [r6, r5, s0, startState]
      have hm : (Expr.bin .mul (.const 5) (.reg 4)).eval w ⟨mem₀, r6, pos⟩ = some (5 * eCap) :=
        Expr.eval_mul (Expr.eval_const h5w) (Expr.eval_reg_of_eq h4r) (by omega)
      exact runs_assign_iff.mpr ⟨p4InInsSup ws eCap, Expr.eval_add (Expr.eval_reg_of_eq h3r) hm (by omega), rfl, rfl, rfl⟩
    have a8 : Runs w p ω (.assign 8 (.bin .add (.reg 7) (.reg 4))) ⟨mem₀, r7, pos⟩ .normal ⟨mem₀, r8, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨p4InsSup ws eCap, by
        have h7r : r7 7 = ws + 5 * eCap := by simp [r7, p4InInsSup]
        have h4r : r7 4 = eCap := by simp [r7, r6, r5, s0, startState]
        have he : (Expr.bin .add (.reg 7) (.reg 4)).eval w ⟨mem₀, r7, pos⟩ = some (ws + 5 * eCap + eCap) :=
          Expr.eval_add (Expr.eval_reg_of_eq h7r) (Expr.eval_reg_of_eq h4r) (by omega)
        simpa [p4InsSup, show ws + 5 * eCap + eCap = ws + 6 * eCap by omega] using he, rfl, rfl, rfl⟩
    have a9 : Runs w p ω (.assign 9 (.bin .add (.reg 3) (.bin .mul (.const 9) (.reg 4))))
        ⟨mem₀, r8, pos⟩ .normal ⟨mem₀, r9, pos⟩ 6 := by
      have h3r : r8 3 = ws := by simp [r8, r7, r6, r5, s0, startState]
      have h4r : r8 4 = eCap := by simp [r8, r7, r6, r5, s0, startState]
      have hm : (Expr.bin .mul (.const 9) (.reg 4)).eval w ⟨mem₀, r8, pos⟩ = some (9 * eCap) :=
        Expr.eval_mul (Expr.eval_const h9w) (Expr.eval_reg_of_eq h4r) (by omega)
      exact runs_assign_iff.mpr ⟨p4SeenCopy ws eCap, Expr.eval_add (Expr.eval_reg_of_eq h3r) hm (by omega), rfl, rfl, rfl⟩
    have a10 : Runs w p ω (.assign 10 (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 10) (.reg 4))) (.const 1)))
        ⟨mem₀, r9, pos⟩ .normal ⟨mem₀, r10, pos⟩ 8 := by
      have h3r : r9 3 = ws := by simp [r9, r8, r7, r6, r5, s0, startState]
      have h4r : r9 4 = eCap := by simp [r9, r8, r7, r6, r5, s0, startState]
      have hm : (Expr.bin .mul (.const 10) (.reg 4)).eval w ⟨mem₀, r9, pos⟩ = some (10 * eCap) :=
        Expr.eval_mul (Expr.eval_const h10w) (Expr.eval_reg_of_eq h4r) (by omega)
      have ha : (Expr.bin .add (.reg 3) (.bin .mul (.const 10) (.reg 4))).eval w ⟨mem₀, r9, pos⟩ =
          some (ws + 10 * eCap) := Expr.eval_add (Expr.eval_reg_of_eq h3r) hm (by omega)
      exact runs_assign_iff.mpr ⟨p4InsLen ws eCap, Expr.eval_add ha (Expr.eval_const h1w) (by omega), rfl, rfl, rfl⟩
    have a11 : Runs w p ω (.assign 11 (.bin .add (.reg 10) (.const 2))) ⟨mem₀, r10, pos⟩ .normal ⟨mem₀, r11, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨p4CopyLen ws eCap, by
        have h10r : r10 10 = ws + 10 * eCap + 1 := by simp [r10, p4InsLen]
        have he : (Expr.bin .add (.reg 10) (.const 2)).eval w ⟨mem₀, r10, pos⟩ = some (ws + 10 * eCap + 1 + 2) :=
          Expr.eval_add (Expr.eval_reg_of_eq h10r) (Expr.eval_const h2w) (by omega)
        simpa [p4CopyLen, show ws + 10 * eCap + 1 + 2 = ws + 10 * eCap + 3 by omega] using he, rfl, rfl, rfl⟩
    have a12 : Runs w p ω (.assign 12 (.bin .add (.reg 11) (.const 1))) ⟨mem₀, r11, pos⟩ .normal ⟨mem₀, r12, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨p4CopyBuf ws eCap, by
        have h11r : r11 11 = ws + 10 * eCap + 3 := by simp [r11, p4CopyLen]
        have he : (Expr.bin .add (.reg 11) (.const 1)).eval w ⟨mem₀, r11, pos⟩ = some (ws + 10 * eCap + 3 + 1) :=
          Expr.eval_add (Expr.eval_reg_of_eq h11r) (Expr.eval_const h1w) (by omega)
        simpa [p4CopyBuf, show ws + 10 * eCap + 3 + 1 = ws + 10 * eCap + 4 by omega] using he, rfl, rfl, rfl⟩
    have st0 : Runs w p ω (.store (.reg 11) (.const 0)) ⟨mem₀, r12, pos⟩ .normal ⟨m0, r12, pos⟩ 3 :=
      runs_store_iff.mpr ⟨p4CopyLen ws eCap, 0, Expr.eval_reg_of_eq (by simp [r12, r11]), Expr.eval_const h0w, rfl, rfl, rfl⟩
    exact ⟨_, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a5, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a6,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, a7, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a8,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, a9, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a10,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, a11, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a12, st0, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩
  obtain ⟨c0, hr0, hc0⟩ := hsetup
  set Sinit : Phase4WS := { S₀ with copyBuf := [] }
  have hW_init : Phase4WSAt m0 ws eCap Sinit := by
    have hfr0 : ∀ a, a ≠ p4CopyLen ws eCap → m0 a = mem₀ a := fun a h => by simp [m0, h]
    exact ⟨fun x hx => (hfr0 _ (by p4o)).trans (hW.1 x hx),
      fun x hx => (hfr0 _ (by p4o)).trans (hW.2.1 x hx),
      fun x hx => (hfr0 _ (by p4o)).trans (hW.2.2.1 x hx),
      dedupBufAt_of_agree_cap hW.2.2.2.1
        (fun x hx => hfr0 _ (by p4o))
        (fun j hj => hfr0 _ (by p4o))
        (hfr0 _ (by p4o)),
      dedupBufAt_of_agree_cap hW.2.2.2.2.1
        (fun x hx => hfr0 _ (by p4o))
        (fun j hj => hfr0 _ (by p4o))
        (hfr0 _ (by p4o)),
      dedupBufAt_of_agree_cap hW.2.2.2.2.2.1
        (fun x hx => hfr0 _ (by p4o))
        (fun j hj => hfr0 _ (by p4o))
        (hfr0 _ (by simp [p4ReembLen, p4CopyLen])),
      fun x hx => (hfr0 _ (by p4o)).trans (hW.2.2.2.2.2.2.1 x hx),
      List.nodup_nil, fun _ h => (by cases h), by simp [m0, Sinit], fun _ h => (by cases h)⟩
  let inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = gEList ∧ st.regs 1 = gL.length ∧ st.regs 2 = hEPres ∧
    st.regs 5 = p4InAct ws eCap ∧ st.regs 6 = p4InTgt ws eCap ∧
    st.regs 7 = p4InInsSup ws eCap ∧ st.regs 8 = p4InsSup ws eCap ∧
    st.regs 9 = p4SeenCopy ws eCap ∧ st.regs 10 = p4InsLen ws eCap ∧
    st.regs 11 = p4CopyLen ws eCap ∧ st.regs 12 = p4CopyBuf ws eCap ∧ st.regs 13 = i ∧
    Phase4WSAt st.mem ws eCap ((gL.take i).foldl (p4StepNew HE) Sinit) ∧
    (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st.mem a = mem₀ a)
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 13) (lo := .const 0) (hi := .reg 1)
    (body := .assign 14 (.load (.bin .add (.reg 0) (.reg 13))) ;;
      .store (.bin .add (.reg 5) (.reg 14)) (.const 1) ;;
      .assign 15 (.load (.bin .add (.reg 2) (.reg 14))) ;;
      .store (.bin .add (.reg 6) (.reg 14)) (.reg 15) ;;
      .call 16 fPush [.reg 7, .reg 8, .reg 10, .reg 14] ;;
      .cond (.bin .eq (.reg 15) (.const 0))
        (.cond (.bin .eq (.load (.bin .add (.reg 9) (.reg 14))) (.const 0))
          (.store (.bin .add (.reg 9) (.reg 14)) (.const 1) ;;
           .assign 16 (.load (.reg 11)) ;;
           .store (.bin .add (.reg 12) (.reg 16)) (.reg 14) ;;
           .store (.reg 11) (.bin .add (.reg 16) (.const 1)))
          .nop)
        .nop)
    (P := fun st => inv 0 { st with regs := Function.update st.regs 13 0 })
    (Inv := inv) (fun _ => 115) 0 gL.length (Nat.zero_le _) h1w (fun _ => by omega)
    (fun st hI => ⟨Expr.eval_const h0w, hI⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.1)
    (fun i _ hi st ω' ⟨hr0', hr1', hr2', hr5', hr6', hr7', hr8', hr9', hr10', hr11', hr12', hr13', hWi, hfri⟩ => by
      set e := gL[i]'hi
      have heCap : e < eCap := hGL_cap e (List.getElem_mem hi)
      set Si := (gL.take i).foldl (p4StepNew HE) Sinit
      have hme : st.mem (gEList + i) = e :=
        (hfri (gEList + i) (by rcases hg_disj with h | h <;> omega)).trans (hGL i hi)
      have hmH : st.mem (hEPres + e) = if e ∈ HE then 1 else 0 :=
        (hfri (hEPres + e) (by rcases hh_disj with h | h <;> omega)).trans (hHE e heCap)
      set rA := Function.update st.regs 14 e
      set m1 := Function.update st.mem (p4InAct ws eCap + e) 1
      set vH := if e ∈ HE then 1 else 0
      set rB := Function.update rA 15 vH
      set m2 := Function.update m1 (p4InTgt ws eCap + e) vH
      have h14 : Runs w p ω' (.assign 14 (.load (.bin .add (.reg 0) (.reg 13)))) st .normal ⟨st.mem, rA, st.pos⟩ 5 :=
        runs_assign_iff.mpr ⟨e, Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr0') (Expr.eval_reg_of_eq hr13') (by omega)) hme, rfl, rfl, rfl⟩
      have hs1 : Runs w p ω' (.store (.bin .add (.reg 5) (.reg 14)) (.const 1))
          ⟨st.mem, rA, st.pos⟩ .normal ⟨m1, rA, st.pos⟩ 5 :=
        runs_store_iff.mpr ⟨p4InAct ws eCap + e, 1,
          Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, hr5'])) (Expr.eval_reg_of_eq (by simp [rA]))
            (by p4o), Expr.eval_const h1w, rfl, rfl, rfl⟩
      have hm1_H : m1 (hEPres + e) = vH := by
        dsimp only [m1]; rw [Function.update_of_ne (by p4o)]
        exact hmH
      have h15 : Runs w p ω' (.assign 15 (.load (.bin .add (.reg 2) (.reg 14))))
          ⟨m1, rA, st.pos⟩ .normal ⟨m1, rB, st.pos⟩ 5 :=
        runs_assign_iff.mpr ⟨vH, Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, hr2'])) (Expr.eval_reg_of_eq (by simp [rA])) (by omega))
          hm1_H, rfl, rfl, rfl⟩
      have hs2 : Runs w p ω' (.store (.bin .add (.reg 6) (.reg 14)) (.reg 15))
          ⟨m1, rB, st.pos⟩ .normal ⟨m2, rB, st.pos⟩ 5 :=
        runs_store_iff.mpr ⟨p4InTgt ws eCap + e, vH,
          Expr.eval_add (Expr.eval_reg_of_eq (by simp [rB, rA, hr6'])) (Expr.eval_reg_of_eq (by simp [rB, rA]))
            (by p4o), Expr.eval_reg_of_eq (by simp [rB]), rfl, rfl, rfl⟩
      have hm2_fr : ∀ a, a ≠ p4InAct ws eCap + e → a ≠ p4InTgt ws eCap + e → m2 a = st.mem a :=
        fun a h1 h2 => by simp [m2, m1, h1, h2]
      have hIS_m2 : DedupBufAt m2 (p4InInsSup ws eCap) (p4InsSup ws eCap) (p4InsLen ws eCap) eCap Si.insSup :=
        dedupBufAt_of_agree_cap hWi.2.2.2.2.1
          (fun x hx => hm2_fr _ (by p4o) (by p4o))
          (fun j hj => hm2_fr _ (by p4o) (by p4o))
          (hm2_fr _ (by p4o) (by p4o))
      obtain ⟨stP, cP, hrP, hIS1, hfrP, hcP⟩ := asmFirstPushDedup_runs (p := p) (ω := ω') (pos := st.pos)
        hw16 hIS_m2 heCap (Or.inl (by p4o))
        (Or.inr (by p4o)) (Or.inr (by p4o))
        (by p4o) (by p4o) (by p4o)
      set rC := Function.update rB 16 0
      have heAP : evalArgs w ⟨m2, rB, st.pos⟩ [.reg 7, .reg 8, .reg 10, .reg 14] =
          some [p4InInsSup ws eCap, p4InsSup ws eCap, p4InsLen ws eCap, e] :=
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, hr7'])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, hr8'])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, hr10'])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA])) <| evalArgs_nil _ _
      have hcP_run : Runs w p ω' (.call 16 fPush [.reg 7, .reg 8, .reg 10, .reg 14])
          ⟨m2, rB, st.pos⟩ .normal ⟨stP.mem, rC, stP.pos⟩
          (argsSize [.reg 7, .reg 8, .reg 10, .reg 14] + cP + 1) :=
        runs_call_iff.mpr ⟨_, asmFirstPushDedupStmt, .returned 0, stP, cP, heAP, hfPush, hrP, rfl, rfl, rfl⟩
      have hP_keep_lt5 : ∀ a, a < p4InInsSup ws eCap → stP.mem a = m2 a := fun a ha =>
        hfrP a (Or.inl ha) (Or.inl (by p4o))
          (by p4o)
      have hP_keep_ge7 : ∀ a, p4InReemb ws eCap ≤ a → a ≠ p4InsLen ws eCap → stP.mem a = st.mem a := fun a ha hne =>
        (hfrP a (Or.inr (by p4o))
          (Or.inr (by p4o)) hne).trans
          (hm2_fr a (by p4o) (by p4o))
      set S1 : Phase4WS := { Si with
        inAct := insert e Si.inAct
        inTgt := if e ∈ HE then insert e Si.inTgt else Si.inTgt.erase e
        insSup := pushDedup Si.insSup e }
      have hW1 : Phase4WSAt stP.mem ws eCap S1 := by
        refine ⟨fun x hx => (hP_keep_lt5 _ (by p4o)).trans
            ((hm2_fr _ (by p4o) (by p4o)).trans (hWi.1 x hx)),
          fun x hx => ?_, fun x hx => ?_,
          dedupBufAt_of_agree_cap hWi.2.2.2.1
            (fun x hx => (hP_keep_lt5 _ (by p4o)).trans
              (hm2_fr _ (by p4o) (by p4o)))
            (fun j hj => (hP_keep_lt5 _ (by p4o)).trans
                (hm2_fr _ (by p4o) (by p4o)))
            (hP_keep_ge7 _ (by p4o) (by p4o)),
          hIS1,
          dedupBufAt_of_agree_cap hWi.2.2.2.2.2.1
            (fun x hx => hP_keep_ge7 _ (by simp [p4InReemb]) (by p4o))
            (fun j hj => hP_keep_ge7 _ (by p4o) (by p4o))
            (hP_keep_ge7 _ (by p4o) (by p4o)),
          fun x hx => (hP_keep_ge7 _ (by p4o) (by p4o)).trans (hWi.2.2.2.2.2.2.1 x hx),
          hWi.2.2.2.2.2.2.2.1, hWi.2.2.2.2.2.2.2.2.1,
          (hP_keep_ge7 _ (by p4o) (by p4o)).trans hWi.2.2.2.2.2.2.2.2.2.1,
          fun j hj => (hP_keep_ge7 _ (by p4o) (by p4o)).trans (hWi.2.2.2.2.2.2.2.2.2.2 j hj)⟩
        · rw [hP_keep_lt5 _ (by p4o)]
          dsimp only [m2]; rw [Function.update_of_ne (by p4o)]
          by_cases hxe : x = e
          · subst hxe; simp [m1, S1]
          · simp only [m1, Function.update_of_ne (by omega : p4InAct ws eCap + x ≠ p4InAct ws eCap + e),
              S1, Finset.mem_insert, hxe, false_or]; exact hWi.2.1 x hx
        · rw [hP_keep_lt5 _ (by p4o)]
          by_cases hxe : x = e
          · subst hxe; simp only [m2, Function.update_self, S1, vH]
            by_cases hH : e ∈ HE <;> simp [hH]
          · simp only [m2, Function.update_of_ne (by omega : p4InTgt ws eCap + x ≠ p4InTgt ws eCap + e),
              m1, Function.update_of_ne (show p4InTgt ws eCap + x ≠ p4InAct ws eCap + e by p4o), S1]
            by_cases hH : e ∈ HE <;> simp [hH, hxe, hWi.2.2.1 x hx]
      have hP_fr : ∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → stP.mem a = mem₀ a := fun a ha => by
        have h1 : stP.mem a = st.mem a := by
          rcases ha with hlt | hge
          · rw [hP_keep_lt5 a (by p4o)]
            exact hm2_fr a (by p4o) (by p4o)
          · exact hP_keep_ge7 a (by p4o) (by p4o)
        exact h1.trans (hfri a ha)
      have htk : (gL.take (i + 1)).foldl (p4StepNew HE) Sinit = p4StepNew HE Si e := by
        rw [List.take_succ_eq_append_getElem hi, List.foldl_append]; rfl
      have hcond_step : ∃ stC cC,
          Runs w p ω'
            (.cond (.bin .eq (.reg 15) (.const 0))
              (.cond (.bin .eq (.load (.bin .add (.reg 9) (.reg 14))) (.const 0))
                (.store (.bin .add (.reg 9) (.reg 14)) (.const 1) ;;
                 .assign 16 (.load (.reg 11)) ;;
                 .store (.bin .add (.reg 12) (.reg 16)) (.reg 14) ;;
                 .store (.reg 11) (.bin .add (.reg 16) (.const 1)))
                .nop)
              .nop)
            ⟨stP.mem, rC, stP.pos⟩ .normal stC cC ∧
          (∀ r, r ≠ 16 → stC.regs r = rC r) ∧
          Phase4WSAt stC.mem ws eCap (p4StepNew HE Si e) ∧
          (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → stC.mem a = mem₀ a) ∧
          cC ≤ 36 := by
        by_cases hH : e ∈ HE
        · have he0 : (Expr.bin .eq (.reg 15) (.const 0)).eval w ⟨stP.mem, rC, stP.pos⟩ = some 0 := by
            simp [Expr.eval, rC, rB, vH, hH, BinOp.eval, h0w]
          refine ⟨⟨stP.mem, rC, stP.pos⟩, _,
            runs_cond_iff.mpr ⟨0, 1, he0, by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩,
            fun _ _ => rfl, by simpa [p4StepNew, hH, S1] using hW1, hP_fr, by simp [Expr.size]⟩
        · have he0 : (Expr.bin .eq (.reg 15) (.const 0)).eval w ⟨stP.mem, rC, stP.pos⟩ = some 1 := by
            simp [Expr.eval, rC, rB, vH, hH, BinOp.eval, h0w, h1w]
          obtain ⟨stC, cC, hrC, hregsC, hWC, hfrC, _, _, hcC⟩ :=
            p4PushCopy_runs (st := ⟨stP.mem, rC, stP.pos⟩) (S := S1) (ω := ω')
              hw16 hws_w heCap (by simp [rC, rB, rA, hr9']) (by simp [rC, rB, rA, hr11'])
              (by simp [rC, rB, rA, hr12']) (by simp [rC, rB, rA]) hW1
          refine ⟨stC, _,
            runs_cond_iff.mpr ⟨1, _, he0, by simpa using hrC, rfl⟩,
            hregsC, by simpa [p4StepNew, hH, S1] using hWC,
            fun a ha => (hfrC a ha).trans (hP_fr a ha), by simp [Expr.size]; omega⟩
      obtain ⟨stC, cC, hrC, hregsC, hWC, hfrC, hcC⟩ := hcond_step
      refine ⟨.normal, stC, _,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, h14,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs1,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h15,
              runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs2,
                runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcP_run, hrC, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
        ⟨⟨by simp only [Function.update_of_ne (show (0:ℕ) ≠ 13 by decide)]; rw [hregsC 0 (by decide)]; simp [rC, rB, rA, hr0'],
          by simp only [Function.update_of_ne (show (1:ℕ) ≠ 13 by decide)]; rw [hregsC 1 (by decide)]; simp [rC, rB, rA, hr1'],
          by simp only [Function.update_of_ne (show (2:ℕ) ≠ 13 by decide)]; rw [hregsC 2 (by decide)]; simp [rC, rB, rA, hr2'],
          by simp only [Function.update_of_ne (show (5:ℕ) ≠ 13 by decide)]; rw [hregsC 5 (by decide)]; simp [rC, rB, rA, hr5'],
          by simp only [Function.update_of_ne (show (6:ℕ) ≠ 13 by decide)]; rw [hregsC 6 (by decide)]; simp [rC, rB, rA, hr6'],
          by simp only [Function.update_of_ne (show (7:ℕ) ≠ 13 by decide)]; rw [hregsC 7 (by decide)]; simp [rC, rB, rA, hr7'],
          by simp only [Function.update_of_ne (show (8:ℕ) ≠ 13 by decide)]; rw [hregsC 8 (by decide)]; simp [rC, rB, rA, hr8'],
          by simp only [Function.update_of_ne (show (9:ℕ) ≠ 13 by decide)]; rw [hregsC 9 (by decide)]; simp [rC, rB, rA, hr9'],
          by simp only [Function.update_of_ne (show (10:ℕ) ≠ 13 by decide)]; rw [hregsC 10 (by decide)]; simp [rC, rB, rA, hr10'],
          by simp only [Function.update_of_ne (show (11:ℕ) ≠ 13 by decide)]; rw [hregsC 11 (by decide)]; simp [rC, rB, rA, hr11'],
          by simp only [Function.update_of_ne (show (12:ℕ) ≠ 13 by decide)]; rw [hregsC 12 (by decide)]; simp [rC, rB, rA, hr12'],
          by simp, htk ▸ hWC, hfrC⟩,
         by rw [hregsC 13 (by decide)]; simp [rC, rB, rA, hr13']⟩,
        by show _ ≤ 115; simp only [argsSize, Expr.size]; omega⟩)
  obtain ⟨o, st1, c1, hr1, hpost1, hc1⟩ := hloop ⟨m0, r12, pos⟩ ω
    ⟨by simp [r12, r11, r10, r9, r8, r7, r6, r5, s0, startState],
     by simp [r12, r11, r10, r9, r8, r7, r6, r5, s0, startState],
     by simp [r12, r11, r10, r9, r8, r7, r6, r5, s0, startState],
     by simp [r12, r11, r10, r9, r8, r7, r6, r5], by simp [r12, r11, r10, r9, r8, r7, r6],
     by simp [r12, r11, r10, r9, r8, r7], by simp [r12, r11, r10, r9, r8],
     by simp [r12, r11, r10, r9], by simp [r12, r11, r10], by simp [r12, r11],
     by simp [r12], by simp, by simpa using hW_init,
     fun a ha => by dsimp only [m0]; rw [Function.update_of_ne (by p4o)]⟩
  cases o with
  | returned _ => cases hpost1
  | normal =>
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hWf, hfrf⟩ := hpost1
  rw [List.take_length] at hWf
  have hret : Runs w p ω (.ret (.const 0)) st1 (.returned 0) st1 2 :=
    runs_ret_iff.mpr ⟨0, Expr.eval_const h0w, rfl, rfl, rfl⟩
  have hrc : rangeCost (fun _ => 115) 0 gL.length = 115 * gL.length := by
    simp [rangeCost, Nat.mul_comm]
  dsimp only at hc1; simp only [hrc, Nat.sub_zero, Expr.size] at hc1
  rcases (runs_seq_iff.mp hr0).resolve_left (by simp) with ⟨_, _, _, a5, hr0_1, rfl⟩
  rcases (runs_seq_iff.mp hr0_1).resolve_left (by simp) with ⟨_, _, _, a6, hr0_2, rfl⟩
  rcases (runs_seq_iff.mp hr0_2).resolve_left (by simp) with ⟨_, _, _, a7, hr0_3, rfl⟩
  rcases (runs_seq_iff.mp hr0_3).resolve_left (by simp) with ⟨_, _, _, a8, hr0_4, rfl⟩
  rcases (runs_seq_iff.mp hr0_4).resolve_left (by simp) with ⟨_, _, _, a9, hr0_5, rfl⟩
  rcases (runs_seq_iff.mp hr0_5).resolve_left (by simp) with ⟨_, _, _, a10, hr0_6, rfl⟩
  rcases (runs_seq_iff.mp hr0_6).resolve_left (by simp) with ⟨_, _, _, a11, hr0_7, rfl⟩
  rcases (runs_seq_iff.mp hr0_7).resolve_left (by simp) with ⟨_, _, _, a12, st0, rfl⟩
  exact ⟨st1, _,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, a5, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a6,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, a7, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a8,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, a9, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a10,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, a11, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a12,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, st0,
              runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr1, hret, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    hWf, hfrf, by omega⟩

end

end MinCostFlow.SparseCore.Program
