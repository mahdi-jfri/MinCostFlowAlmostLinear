module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSlotScanProof

import WordRAM.Tactic

/-!
# Verification of the per-slot `R` workspace scanner (`AssemblyFirstStepSlotScanR`)

Proves `asmFirstScanSlotR_runs`: the scanner of `AssemblyFirstStepSlotScanD.lean` reads `R` of an
updated slot, adds each edge to `reemb`, and (when `isOld ≠ 0` and `e ∈ GE \ HE`) pushes `e` into
`copyBuf`, in `≤ 135 * rL.length + 65` steps. It leaves memory untouched outside
`[ws, ws + p4WsSize eCap)`. The scanner of a newly active slot is in
`AssemblyFirstStepSlotScanNew.lean`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

/-- Unfolds the places of the Phase 4 workspace and closes the goal by `omega`. -/
local macro "p4o" : tactic => `(tactic| ((try simp only [p4WsSize, p4InDtot, p4InAct, p4InTgt,
  p4InDelSup, p4DelSup, p4InInsSup, p4InsSup, p4InReemb, p4Reemb, p4SeenCopy, p4DelLen, p4InsLen,
  p4ReembLen, p4CopyLen, p4CopyBuf] at *) <;> omega))

public section

/-! ## 1. `asmFirstScanSlotR_runs` -/

set_option maxHeartbeats 600000 in
theorem asmFirstScanSlotR_runs {w fPush gEPres hEPres rPtr isOldN ws eCap pos : ℕ} {p : Program}
    (hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt)
    {GE HE : Finset ℕ} {rL : List ℕ} {S₀ : Phase4WS} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hW : Phase4WSAt mem₀ ws eCap S₀)
    (hGE : ∀ e < eCap, mem₀ (gEPres + e) = if e ∈ GE then 1 else 0)
    (hHE : ∀ e < eCap, mem₀ (hEPres + e) = if e ∈ HE then 1 else 0)
    (hRL : ListAt mem₀ rPtr rL) (hRL_cap : ∀ e ∈ rL, e < eCap)
    (hg_disj : gEPres + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ gEPres)
    (hh_disj : hEPres + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ hEPres)
    (hr_disj : rPtr + rL.length ≤ ws ∨ ws + p4WsSize eCap ≤ rPtr)
    (hg_w : gEPres + eCap < 2 ^ w) (hh_w : hEPres + eCap < 2 ^ w)
    (hr_w : rPtr + rL.length < 2 ^ w) (hws_w : ws + p4WsSize eCap < 2 ^ w) :
    ∃ st' cost,
      Runs w p ω (asmFirstScanSlotRStmt fPush)
        (startState [gEPres, hEPres, rPtr, rL.length, isOldN, ws, eCap] mem₀ pos) (.returned 0) st' cost ∧
      Phase4WSAt st'.mem ws eCap (rL.foldl (p4StepR GE HE (decide (isOldN ≠ 0))) S₀) ∧
      (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st'.mem a = mem₀ a) ∧
      cost ≤ 135 * rL.length + 65 := by
  classical
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h7w : 7 < 2 ^ w := by omega
  have h10w : 10 < 2 ^ w := by omega
  have hws_un : ws + 11 * eCap + 4 < 2 ^ w := by unfold p4WsSize at hws_w; omega
  set s0 := startState [gEPres, hEPres, rPtr, rL.length, isOldN, ws, eCap] mem₀ pos
  set r7 := Function.update s0.regs 7 (p4InReemb ws eCap)
  set r8 := Function.update r7 8 (p4Reemb ws eCap)
  set r9 := Function.update r8 9 (p4SeenCopy ws eCap)
  set r10 := Function.update r9 10 (p4ReembLen ws eCap)
  set r11 := Function.update r10 11 (p4CopyLen ws eCap)
  set r12 := Function.update r11 12 (p4CopyBuf ws eCap)
  have hsetup : ∃ c0, Runs w p ω
      (.assign 7 (.bin .add (.reg 5) (.bin .mul (.const 7) (.reg 6))) ;;
       .assign 8 (.bin .add (.reg 7) (.reg 6)) ;;
       .assign 9 (.bin .add (.reg 8) (.reg 6)) ;;
       .assign 10 (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 10) (.reg 6))) (.const 2)) ;;
       .assign 11 (.bin .add (.reg 10) (.const 1)) ;;
       .assign 12 (.bin .add (.reg 11) (.const 1)))
      s0 .normal ⟨mem₀, r12, pos⟩ c0 ∧ c0 ≤ 42 := by
    have a7 : Runs w p ω (.assign 7 (.bin .add (.reg 5) (.bin .mul (.const 7) (.reg 6)))) s0 .normal ⟨mem₀, r7, pos⟩ 6 := by
      have hm : (Expr.bin .mul (.const 7) (.reg 6)).eval w s0 = some (7 * eCap) :=
        Expr.eval_mul (Expr.eval_const h7w) (Expr.eval_reg_of_eq (by simp [s0, startState])) (by omega)
      exact runs_assign_iff.mpr ⟨p4InReemb ws eCap,
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [s0, startState])) hm (by omega), rfl, rfl, rfl⟩
    have a8 : Runs w p ω (.assign 8 (.bin .add (.reg 7) (.reg 6))) ⟨mem₀, r7, pos⟩ .normal ⟨mem₀, r8, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨p4Reemb ws eCap, by
        have h7r : r7 7 = ws + 7 * eCap := by simp [r7, p4InReemb]
        have h6r : r7 6 = eCap := by simp [r7, s0, startState]
        have he : (Expr.bin .add (.reg 7) (.reg 6)).eval w ⟨mem₀, r7, pos⟩ = some (ws + 7 * eCap + eCap) :=
          Expr.eval_add (Expr.eval_reg_of_eq h7r) (Expr.eval_reg_of_eq h6r) (by omega)
        simpa [p4Reemb, show ws + 7 * eCap + eCap = ws + 8 * eCap by omega] using he, rfl, rfl, rfl⟩
    have a9 : Runs w p ω (.assign 9 (.bin .add (.reg 8) (.reg 6))) ⟨mem₀, r8, pos⟩ .normal ⟨mem₀, r9, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨p4SeenCopy ws eCap, by
        have h8r : r8 8 = ws + 8 * eCap := by simp [r8, p4Reemb]
        have h6r : r8 6 = eCap := by simp [r8, r7, s0, startState]
        have he : (Expr.bin .add (.reg 8) (.reg 6)).eval w ⟨mem₀, r8, pos⟩ = some (ws + 8 * eCap + eCap) :=
          Expr.eval_add (Expr.eval_reg_of_eq h8r) (Expr.eval_reg_of_eq h6r) (by omega)
        simpa [p4SeenCopy, show ws + 8 * eCap + eCap = ws + 9 * eCap by omega] using he, rfl, rfl, rfl⟩
    have a10 : Runs w p ω (.assign 10 (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 10) (.reg 6))) (.const 2)))
        ⟨mem₀, r9, pos⟩ .normal ⟨mem₀, r10, pos⟩ 8 := by
      have h5r : r9 5 = ws := by simp [r9, r8, r7, s0, startState]
      have h6r : r9 6 = eCap := by simp [r9, r8, r7, s0, startState]
      have hm : (Expr.bin .mul (.const 10) (.reg 6)).eval w ⟨mem₀, r9, pos⟩ = some (10 * eCap) :=
        Expr.eval_mul (Expr.eval_const h10w) (Expr.eval_reg_of_eq h6r) (by omega)
      have ha : (Expr.bin .add (.reg 5) (.bin .mul (.const 10) (.reg 6))).eval w ⟨mem₀, r9, pos⟩ =
          some (ws + 10 * eCap) := Expr.eval_add (Expr.eval_reg_of_eq h5r) hm (by omega)
      exact runs_assign_iff.mpr ⟨p4ReembLen ws eCap, Expr.eval_add ha (Expr.eval_const h2w) (by omega), rfl, rfl, rfl⟩
    have a11 : Runs w p ω (.assign 11 (.bin .add (.reg 10) (.const 1))) ⟨mem₀, r10, pos⟩ .normal ⟨mem₀, r11, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨p4CopyLen ws eCap, by
        have h10r : r10 10 = ws + 10 * eCap + 2 := by simp [r10, p4ReembLen]
        have he : (Expr.bin .add (.reg 10) (.const 1)).eval w ⟨mem₀, r10, pos⟩ = some (ws + 10 * eCap + 2 + 1) :=
          Expr.eval_add (Expr.eval_reg_of_eq h10r) (Expr.eval_const h1w) (by omega)
        simpa [p4CopyLen, show ws + 10 * eCap + 2 + 1 = ws + 10 * eCap + 3 by omega] using he, rfl, rfl, rfl⟩
    have a12 : Runs w p ω (.assign 12 (.bin .add (.reg 11) (.const 1))) ⟨mem₀, r11, pos⟩ .normal ⟨mem₀, r12, pos⟩ 4 :=
      runs_assign_iff.mpr ⟨p4CopyBuf ws eCap, by
        have h11r : r11 11 = ws + 10 * eCap + 3 := by simp [r11, p4CopyLen]
        have he : (Expr.bin .add (.reg 11) (.const 1)).eval w ⟨mem₀, r11, pos⟩ = some (ws + 10 * eCap + 3 + 1) :=
          Expr.eval_add (Expr.eval_reg_of_eq h11r) (Expr.eval_const h1w) (by omega)
        simpa [p4CopyBuf, show ws + 10 * eCap + 3 + 1 = ws + 10 * eCap + 4 by omega] using he, rfl, rfl, rfl⟩
    exact ⟨_, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a7, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a8,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, a9, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a10,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, a11, a12, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩
  obtain ⟨c0, hr0, hc0⟩ := hsetup
  let isOldB := decide (isOldN ≠ 0)
  let inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = gEPres ∧ st.regs 1 = hEPres ∧ st.regs 2 = rPtr ∧ st.regs 3 = rL.length ∧
    st.regs 4 = isOldN ∧ st.regs 7 = p4InReemb ws eCap ∧ st.regs 8 = p4Reemb ws eCap ∧
    st.regs 9 = p4SeenCopy ws eCap ∧ st.regs 10 = p4ReembLen ws eCap ∧
    st.regs 11 = p4CopyLen ws eCap ∧ st.regs 12 = p4CopyBuf ws eCap ∧ st.regs 13 = i ∧
    Phase4WSAt st.mem ws eCap ((rL.take i).foldl (p4StepR GE HE isOldB) S₀) ∧
    (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st.mem a = mem₀ a)
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 13) (lo := .const 0) (hi := .reg 3)
    (body := .assign 14 (.load (.bin .add (.reg 2) (.reg 13))) ;;
      .call 15 fPush [.reg 7, .reg 8, .reg 10, .reg 14] ;;
      .cond (.reg 4)
        (.cond (.load (.bin .add (.reg 0) (.reg 14)))
          (.cond (.bin .eq (.load (.bin .add (.reg 1) (.reg 14))) (.const 0))
            (.cond (.bin .eq (.load (.bin .add (.reg 9) (.reg 14))) (.const 0))
              (.store (.bin .add (.reg 9) (.reg 14)) (.const 1) ;;
               .assign 16 (.load (.reg 11)) ;;
               .store (.bin .add (.reg 12) (.reg 16)) (.reg 14) ;;
               .store (.reg 11) (.bin .add (.reg 16) (.const 1)))
              .nop)
            .nop)
          .nop)
        .nop)
    (P := fun st => inv 0 { st with regs := Function.update st.regs 13 0 })
    (Inv := inv) (fun _ => 115) 0 rL.length (Nat.zero_le _) h1w (fun _ => by omega)
    (fun st hI => ⟨Expr.eval_const h0w, hI⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.2.1)
    (fun i _ hi st ω' ⟨hr0', hr1', hr2', hr3', hr4', hr7', hr8', hr9', hr10', hr11', hr12', hr13', hWi, hfri⟩ => by
      set e := rL[i]'hi
      have heCap : e < eCap := hRL_cap e (List.getElem_mem hi)
      set Si := (rL.take i).foldl (p4StepR GE HE isOldB) S₀
      have hme : st.mem (rPtr + i) = e :=
        (hfri (rPtr + i) (by rcases hr_disj with h | h <;> omega)).trans (hRL i hi)
      set rA := Function.update st.regs 14 e
      have h14 : Runs w p ω' (.assign 14 (.load (.bin .add (.reg 2) (.reg 13)))) st .normal ⟨st.mem, rA, st.pos⟩ 5 :=
        runs_assign_iff.mpr ⟨e, Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr2') (Expr.eval_reg_of_eq hr13') (by omega)) hme, rfl, rfl, rfl⟩
      obtain ⟨stP, cP, hrP, hR1, hfrP, hcP⟩ := asmFirstPushDedup_runs (p := p) (ω := ω') (pos := st.pos)
        hw16 hWi.2.2.2.2.2.1 heCap (Or.inl (by p4o))
        (Or.inr (by p4o)) (Or.inr (by p4o))
        (by p4o) (by p4o) (by p4o)
      set rB := Function.update rA 15 0
      have heAP : evalArgs w ⟨st.mem, rA, st.pos⟩ [.reg 7, .reg 8, .reg 10, .reg 14] =
          some [p4InReemb ws eCap, p4Reemb ws eCap, p4ReembLen ws eCap, e] :=
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA, hr7'])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA, hr8'])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA, hr10'])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA])) <| evalArgs_nil _ _
      have hcP_run : Runs w p ω' (.call 15 fPush [.reg 7, .reg 8, .reg 10, .reg 14])
          ⟨st.mem, rA, st.pos⟩ .normal ⟨stP.mem, rB, stP.pos⟩
          (argsSize [.reg 7, .reg 8, .reg 10, .reg 14] + cP + 1) :=
        runs_call_iff.mpr ⟨_, asmFirstPushDedupStmt, .returned 0, stP, cP, heAP, hfPush, hrP, rfl, rfl, rfl⟩
      set S1 : Phase4WS := { Si with reemb := pushDedup Si.reemb e }
      have hP_keep_lt7 : ∀ a, a < p4InReemb ws eCap → stP.mem a = st.mem a := fun a ha =>
        hfrP a (Or.inl ha) (Or.inl (by p4o))
          (by p4o)
      have hP_keep_ge9 : ∀ a, p4SeenCopy ws eCap ≤ a → a ≠ p4ReembLen ws eCap → stP.mem a = st.mem a := fun a ha hne =>
        hfrP a (Or.inr (by p4o))
          (Or.inr (by p4o)) hne
      have hW1 : Phase4WSAt stP.mem ws eCap S1 :=
        ⟨fun x hx => (hP_keep_lt7 _ (by p4o)).trans (hWi.1 x hx),
         fun x hx => (hP_keep_lt7 _ (by p4o)).trans (hWi.2.1 x hx),
         fun x hx => (hP_keep_lt7 _ (by p4o)).trans (hWi.2.2.1 x hx),
         dedupBufAt_of_agree hWi.2.2.2.1
           (fun x hx => hP_keep_lt7 _ (by p4o))
           (fun j (hj : j < Si.delSup.length) => have := dedupBuf_length_le hWi.2.2.2.1; hP_keep_lt7 _ (by p4o))
           (hP_keep_ge9 _ (by p4o) (by p4o)),
         dedupBufAt_of_agree hWi.2.2.2.2.1
           (fun x hx => hP_keep_lt7 _ (by p4o))
           (fun j (hj : j < Si.insSup.length) => have := dedupBuf_length_le hWi.2.2.2.2.1; hP_keep_lt7 _ (by p4o))
           (hP_keep_ge9 _ (by p4o) (by p4o)),
         hR1,
         fun x hx => (hP_keep_ge9 _ (by simp [p4SeenCopy]) (by p4o)).trans (hWi.2.2.2.2.2.2.1 x hx),
         hWi.2.2.2.2.2.2.2.1, hWi.2.2.2.2.2.2.2.2.1,
         (hP_keep_ge9 _ (by p4o) (by p4o)).trans hWi.2.2.2.2.2.2.2.2.2.1,
         fun j hj => (hP_keep_ge9 _ (by p4o) (by p4o)).trans (hWi.2.2.2.2.2.2.2.2.2.2 j hj)⟩
      have hP_fr : ∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → stP.mem a = mem₀ a := fun a ha => by
        have h1 : stP.mem a = st.mem a := by
          rcases ha with hlt | hge
          · exact hP_keep_lt7 a (by p4o)
          · exact hP_keep_ge9 a (by p4o) (by p4o)
        exact h1.trans (hfri a ha)
      have htk : (rL.take (i + 1)).foldl (p4StepR GE HE isOldB) S₀ = p4StepR GE HE isOldB Si e := by
        rw [List.take_succ_eq_append_getElem hi, List.foldl_append]; rfl
      have hcond_step : ∃ stC cC,
          Runs w p ω'
            (.cond (.reg 4)
              (.cond (.load (.bin .add (.reg 0) (.reg 14)))
                (.cond (.bin .eq (.load (.bin .add (.reg 1) (.reg 14))) (.const 0))
                  (.cond (.bin .eq (.load (.bin .add (.reg 9) (.reg 14))) (.const 0))
                    (.store (.bin .add (.reg 9) (.reg 14)) (.const 1) ;;
                     .assign 16 (.load (.reg 11)) ;;
                     .store (.bin .add (.reg 12) (.reg 16)) (.reg 14) ;;
                     .store (.reg 11) (.bin .add (.reg 16) (.const 1)))
                    .nop)
                  .nop)
                .nop)
              .nop)
            ⟨stP.mem, rB, stP.pos⟩ .normal stC cC ∧
          (∀ r, r ≠ 16 → stC.regs r = rB r) ∧
          Phase4WSAt stC.mem ws eCap (p4StepR GE HE isOldB Si e) ∧
          (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → stC.mem a = mem₀ a) ∧
          cC ≤ 55 := by
        by_cases ho : isOldN = 0
        · refine ⟨⟨stP.mem, rB, stP.pos⟩, _,
            runs_cond_iff.mpr ⟨0, 1, Expr.eval_reg_of_eq (by simp [rB, rA, hr4', ho]),
              by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩,
            fun _ _ => rfl, by simpa [p4StepR, isOldB, ho, S1] using hW1, hP_fr, by simp [Expr.size]⟩
        · have hmG : stP.mem (gEPres + e) = if e ∈ GE then 1 else 0 :=
            (hP_fr _ (by rcases hg_disj with h | h <;> omega)).trans (hGE e heCap)
          have heG : (Expr.load (.bin .add (.reg 0) (.reg 14))).eval w ⟨stP.mem, rB, stP.pos⟩ =
              some (if e ∈ GE then 1 else 0) :=
            Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rB, rA, hr0']))
              (Expr.eval_reg_of_eq (by simp [rB, rA])) (by omega)) hmG
          by_cases hG : e ∈ GE
          · have hmH : stP.mem (hEPres + e) = if e ∈ HE then 1 else 0 :=
              (hP_fr _ (by rcases hh_disj with h | h <;> omega)).trans (hHE e heCap)
            have heH : (Expr.load (.bin .add (.reg 1) (.reg 14))).eval w ⟨stP.mem, rB, stP.pos⟩ =
                some (if e ∈ HE then 1 else 0) :=
              Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rB, rA, hr1']))
                (Expr.eval_reg_of_eq (by simp [rB, rA])) (by omega)) hmH
            by_cases hH : e ∈ HE
            · have heH0 : (Expr.bin .eq (.load (.bin .add (.reg 1) (.reg 14))) (.const 0)).eval w
                  ⟨stP.mem, rB, stP.pos⟩ = some 0 := by
                simpa [hH] using Expr.eval_eq_op heH (Expr.eval_const (st := ⟨stP.mem, rB, stP.pos⟩) h0w) h1w
              refine ⟨⟨stP.mem, rB, stP.pos⟩, _,
                runs_cond_iff.mpr ⟨isOldN, _, Expr.eval_reg_of_eq (by simp [rB, rA, hr4']), by
                  simpa [ho] using runs_cond_iff.mpr ⟨1, _, by simpa [hG] using heG, by
                    simpa using runs_cond_iff.mpr ⟨0, 1, heH0, by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩,
                fun _ _ => rfl, by simpa [p4StepR, isOldB, ho, hG, hH, S1] using hW1, hP_fr, by simp [Expr.size]⟩
            · have heH0 : (Expr.bin .eq (.load (.bin .add (.reg 1) (.reg 14))) (.const 0)).eval w
                  ⟨stP.mem, rB, stP.pos⟩ = some 1 := by
                simpa [hH] using Expr.eval_eq_op heH (Expr.eval_const (st := ⟨stP.mem, rB, stP.pos⟩) h0w) h1w
              obtain ⟨stC, cC, hrC, hregsC, hWC, hfrC, _, _, hcC⟩ :=
                p4PushCopy_runs (st := ⟨stP.mem, rB, stP.pos⟩) (S := S1) (ω := ω')
                  hw16 hws_w heCap (by simp [rB, rA, hr9']) (by simp [rB, rA, hr11'])
                  (by simp [rB, rA, hr12']) (by simp [rB, rA]) hW1
              refine ⟨stC, _,
                runs_cond_iff.mpr ⟨isOldN, _, Expr.eval_reg_of_eq (by simp [rB, rA, hr4']), by
                  simpa [ho] using runs_cond_iff.mpr ⟨1, _, by simpa [hG] using heG, by
                    simpa using runs_cond_iff.mpr ⟨1, _, heH0, by simpa using hrC, rfl⟩, rfl⟩, rfl⟩,
                hregsC, by simpa [p4StepR, isOldB, ho, hG, hH, S1] using hWC,
                fun a ha => (hfrC a ha).trans (hP_fr a ha), by simp [Expr.size]; omega⟩
          · refine ⟨⟨stP.mem, rB, stP.pos⟩, _,
              runs_cond_iff.mpr ⟨isOldN, _, Expr.eval_reg_of_eq (by simp [rB, rA, hr4']), by
                simpa [ho] using runs_cond_iff.mpr ⟨0, 1, by simpa [hG] using heG,
                  by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩, rfl⟩,
              fun _ _ => rfl, by simpa [p4StepR, isOldB, ho, hG, S1] using hW1, hP_fr, by simp [Expr.size]⟩
      obtain ⟨stC, cC, hrC, hregsC, hWC, hfrC, hcC⟩ := hcond_step
      refine ⟨.normal, stC, _,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, h14,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcP_run, hrC, rfl⟩), rfl⟩),
        ⟨⟨by simp only [Function.update_of_ne (show (0:ℕ) ≠ 13 by decide)]; rw [hregsC 0 (by decide)]; simp [rB, rA, hr0'],
          by simp only [Function.update_of_ne (show (1:ℕ) ≠ 13 by decide)]; rw [hregsC 1 (by decide)]; simp [rB, rA, hr1'],
          by simp only [Function.update_of_ne (show (2:ℕ) ≠ 13 by decide)]; rw [hregsC 2 (by decide)]; simp [rB, rA, hr2'],
          by simp only [Function.update_of_ne (show (3:ℕ) ≠ 13 by decide)]; rw [hregsC 3 (by decide)]; simp [rB, rA, hr3'],
          by simp only [Function.update_of_ne (show (4:ℕ) ≠ 13 by decide)]; rw [hregsC 4 (by decide)]; simp [rB, rA, hr4'],
          by simp only [Function.update_of_ne (show (7:ℕ) ≠ 13 by decide)]; rw [hregsC 7 (by decide)]; simp [rB, rA, hr7'],
          by simp only [Function.update_of_ne (show (8:ℕ) ≠ 13 by decide)]; rw [hregsC 8 (by decide)]; simp [rB, rA, hr8'],
          by simp only [Function.update_of_ne (show (9:ℕ) ≠ 13 by decide)]; rw [hregsC 9 (by decide)]; simp [rB, rA, hr9'],
          by simp only [Function.update_of_ne (show (10:ℕ) ≠ 13 by decide)]; rw [hregsC 10 (by decide)]; simp [rB, rA, hr10'],
          by simp only [Function.update_of_ne (show (11:ℕ) ≠ 13 by decide)]; rw [hregsC 11 (by decide)]; simp [rB, rA, hr11'],
          by simp only [Function.update_of_ne (show (12:ℕ) ≠ 13 by decide)]; rw [hregsC 12 (by decide)]; simp [rB, rA, hr12'],
          by simp, htk ▸ hWC, hfrC⟩,
         by rw [hregsC 13 (by decide)]; simp [rB, rA, hr13']⟩,
        by show _ ≤ 115; simp only [argsSize, Expr.size]; omega⟩)
  obtain ⟨o, st1, c1, hr1, hpost1, hc1⟩ := hloop ⟨mem₀, r12, pos⟩ ω
    ⟨by simp [r12, r11, r10, r9, r8, r7, s0, startState],
     by simp [r12, r11, r10, r9, r8, r7, s0, startState],
     by simp [r12, r11, r10, r9, r8, r7, s0, startState],
     by simp [r12, r11, r10, r9, r8, r7, s0, startState],
     by simp [r12, r11, r10, r9, r8, r7, s0, startState],
     by simp [r12, r11, r10, r9, r8, r7], by simp [r12, r11, r10, r9, r8],
     by simp [r12, r11, r10, r9], by simp [r12, r11, r10], by simp [r12, r11],
     by simp [r12], by simp, by simpa using hW, fun _ _ => rfl⟩
  cases o with
  | returned _ => cases hpost1
  | normal =>
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hWf, hfrf⟩ := hpost1
  rw [List.take_length] at hWf
  have hret : Runs w p ω (.ret (.const 0)) st1 (.returned 0) st1 2 :=
    runs_ret_iff.mpr ⟨0, Expr.eval_const h0w, rfl, rfl, rfl⟩
  have hrc : rangeCost (fun _ => 115) 0 rL.length = 115 * rL.length := by
    simp [rangeCost, Nat.mul_comm]
  dsimp only at hc1; simp only [hrc, Nat.sub_zero, Expr.size] at hc1
  rcases (runs_seq_iff.mp hr0).resolve_left (by simp) with ⟨_, _, _, a7, hr0_1, rfl⟩
  rcases (runs_seq_iff.mp hr0_1).resolve_left (by simp) with ⟨_, _, _, a8, hr0_2, rfl⟩
  rcases (runs_seq_iff.mp hr0_2).resolve_left (by simp) with ⟨_, _, _, a9, hr0_3, rfl⟩
  rcases (runs_seq_iff.mp hr0_3).resolve_left (by simp) with ⟨_, _, _, a10, hr0_4, rfl⟩
  rcases (runs_seq_iff.mp hr0_4).resolve_left (by simp) with ⟨_, _, _, a11, a12, rfl⟩
  exact ⟨st1, _,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, a7, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a8,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, a9, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a10,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, a11, runs_seq_iff.mpr (Or.inr ⟨_, _, _, a12,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr1, hret, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    hWf, hfrf, by omega⟩

end

end MinCostFlow.SparseCore.Program
