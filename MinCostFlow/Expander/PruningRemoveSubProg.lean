module

public import MinCostFlow.Expander.PruningStepBase

/-!
# Push-Active/Peel Helpers and Remove-One Statements
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM
open MinCostFlow.Cited

/-! ## 2. `removeOneFromRStmt` -/

/-- Word-RAM statement implementing `removeOneFromR cfg a s` (without altering bucket links):
expects `prU = a`, sets `outR[a] := 0`, and iterates over CSR incident half-edges of `a`,
updating `ex`, `degR`, `active`, `inActive`, and `peelQ`. Preserves `prU`, `prI`, `prPicked`,
`prSuf`, `prDelta`, and all `PruneStepRegs`. -/
lemma eval_bin_two_mul_div_two (a b : ℕ) (hb : b < 2) :
    (2 * a + b) / 2 = a ∧ (2 * a + b) % 2 = b := by
  omega

lemma stk_push_getD {L : List ℕ} {w i : ℕ} (hi : i < (w :: L).length) :
    Function.update (fun j => L.getD (L.length - 1 - j) 0) L.length w i =
      (w :: L).getD ((w :: L).length - 1 - i) 0 := by
  simp only [List.length_cons] at hi ⊢
  by_cases hil : i = L.length
  · subst hil
    simp [Function.update_self]
  · have hilt : i < L.length := by omega
    rw [Function.update_of_ne hil]
    have hsub : L.length + 1 - 1 - i = (L.length - 1 - i) + 1 := by omega
    rw [hsub]
    simp

def pushActIfNewStmt (condReg : ℕ) : Stmt :=
  .cond (.bin .lt (.const 0) (.reg condReg))
    (.cond (.bin .eq (.reg prTmp1) (.const 0))
      (seqStmts [
        .store (.bin .add (.reg prInAct) (.reg prW)) (.const 1),
        .store (.bin .add (.reg prActStk) (.reg prActTop)) (.reg prW),
        .assign prActTop (.bin .add (.reg prActTop) (.const 1))
      ])
      .nop)
    .nop

lemma pushActIfNewStmt_noRand (condReg : ℕ) : (pushActIfNewStmt condReg).NoRand := by
  refine ⟨⟨?_, by simp [Stmt.NoRand]⟩, by simp [Stmt.NoRand]⟩
  apply seqStmts_noRand
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;> simp [Stmt.NoRand]

lemma pushActIfNew_triple {w : ℕ} {p : Program}
    (condReg workAddr n m H u condVal : ℕ) (active : List ℕ) (inAct : ℕ → Bool)
    (st0 : State)
    (hwb : workAddr + pruneWorkSpace n m H < 2 ^ w) (hu_n : u < n)
    (hrIA : st0.regs prInAct = wInAct workAddr n m H)
    (hrAS : st0.regs prActStk = wActStk workAddr n m H)
    (hrW : st0.regs prW = u)
    (hrTmp1 : st0.regs prTmp1 = if inAct u then 1 else 0)
    (hrCond : st0.regs condReg = condVal)
    (hrAT : st0.regs prActTop = active.length)
    (hlen : (if 0 < condVal ∧ inAct u = false then u :: active else active).length ≤ n)
    (hIA : ∀ x < n, st0.mem (wInAct workAddr n m H + x) = if inAct x then 1 else 0)
    (hAS : ∀ i < active.length,
      st0.mem (wActStk workAddr n m H + i) = active.getD (active.length - 1 - i) 0) :
    let active' := if 0 < condVal ∧ inAct u = false then u :: active else active
    let inAct' := fun x =>
      if 0 < condVal ∧ inAct u = false then (if x = u then true else inAct x) else inAct x
    Triple w p (fun st => st = st0) (pushActIfNewStmt condReg)
      (normalPost fun st' =>
        (∀ r, r ≠ prActTop → st'.regs r = st0.regs r) ∧
        st'.regs prActTop = active'.length ∧
        st'.pos = st0.pos ∧
        MemFrame st0.mem st'.mem (wInAct workAddr n m H) (wPeelStk workAddr n m H) ∧
        (∀ x < n, st'.mem (wInAct workAddr n m H + x) = if inAct' x then 1 else 0) ∧
        (∀ i < active'.length,
          st'.mem (wActStk workAddr n m H + i) = active'.getD (active'.length - 1 - i) 0))
      (fun _ => 24) := by
  intro active' inAct'
  have h0lt : 0 < 2 ^ w := by unfold pruneWorkSpace at hwb; omega
  have h1lt : 1 < 2 ^ w := by unfold pruneWorkSpace at hwb; omega
  have hu_w : u < 2 ^ w := by unfold pruneWorkSpace at hwb; omega
  have hia_addr : wInAct workAddr n m H + u < 2 ^ w := by
    unfold pruneWorkSpace at hwb; dsimp [wInAct]; omega
  have hinner : Triple w p (fun sx => sx = st0 ∧ 0 < condVal)
      (.cond (.bin .eq (.reg prTmp1) (.const 0))
        (seqStmts [
          .store (.bin .add (.reg prInAct) (.reg prW)) (.const 1),
          .store (.bin .add (.reg prActStk) (.reg prActTop)) (.reg prW),
          .assign prActTop (.bin .add (.reg prActTop) (.const 1))
        ])
        .nop)
      (normalPost fun st' =>
        (∀ r, r ≠ prActTop → st'.regs r = st0.regs r) ∧
        st'.regs prActTop = active'.length ∧
        st'.pos = st0.pos ∧
        MemFrame st0.mem st'.mem (wInAct workAddr n m H) (wPeelStk workAddr n m H) ∧
        (∀ x < n, st'.mem (wInAct workAddr n m H + x) = if inAct' x then 1 else 0) ∧
        (∀ i < active'.length,
          st'.mem (wActStk workAddr n m H + i) = active'.getD (active'.length - 1 - i) 0))
      (fun _ => 20) := by
    apply (Triple.cond_const
      (P := fun sx => sx = st0 ∧ 0 < condVal)
      (e := .bin .eq (.reg prTmp1) (.const 0))
      (val := fun sx => if sx.regs prTmp1 = 0 then 1 else 0)
      (c_t := 16) (c_f := 1)
      (fun sx ⟨hsx, _⟩ => by
        subst sx; simp only [Expr.eval, hrTmp1, h0lt, WordRAM.BinOp.eval]
        cases inAct u <;> simp [h1lt, h0lt])
      ?_ ?_).mono_cost (T' := fun _ => 20) (fun _ _ => by simp only [Expr.size]; omega)
    · intro sx ω ⟨⟨hsx, hc_pos⟩, hne⟩
      subst sx
      have hia_f : inAct u = false := by
        cases hfa : inAct u <;> simp [hrTmp1, hfa] at hne ⊢
      have hc : 0 < condVal ∧ inAct u = false := ⟨hc_pos, hia_f⟩
      have hact_new : active' = u :: active := by simp [active', hc]
      have hat_len_lt : active.length < n := by
        have hl := hlen; simp [hc] at hl; omega
      have hat_addr : wActStk workAddr n m H + active.length < 2 ^ w := by
        unfold pruneWorkSpace at hwb; dsimp [wActStk]; omega
      have hat1_lt : active.length + 1 < 2 ^ w := by
        unfold pruneWorkSpace at hwb; omega
      refine runs_start_le (T := 16) ?_
      dsimp only [seqStmts]
      apply runs_seq_store_le (x := wInAct workAddr n m H + u) (v := 1)
      · exact eval_add_regs hrIA hrW hia_addr
      · simp [Expr.eval, h1lt]
      apply runs_seq_store_le (x := wActStk workAddr n m H + active.length) (v := u)
      · exact eval_add_regs hrAS hrAT hat_addr
      · exact eval_reg hrW hu_w
      apply runs_assign_le (v := active.length + 1)
      · simp [Expr.eval, hrAT, h1lt, WordRAM.BinOp.eval, hat1_lt]
      · refine ⟨fun r hne' => by simp [Function.update_of_ne hne'], ?_, rfl, ?_, ?_, ?_⟩
        · simp [hact_new]
        · exact memFrame_trans
            (memFrame_update_in (by dsimp [wInAct]; omega) (by dsimp [wInAct, wPeelStk]; omega))
            (memFrame_update_in (by dsimp [wInAct, wActStk]; omega) (by dsimp [wActStk, wPeelStk]; omega))
        · intro x hx
          dsimp only [inAct']
          simp only [hc, and_self, ↓reduceIte]
          by_cases hxu : x = u
          · subst hxu
            rw [Function.update_of_ne (by dsimp [wInAct, wActStk]; omega), Function.update_self]
            simp
          · rw [Function.update_of_ne (by dsimp [wInAct, wActStk]; omega),
              Function.update_of_ne (by omega)]
            simp [hxu, hIA x hx]
        · intro i hi
          dsimp only
          rw [hact_new] at hi ⊢
          rw [← stk_push_getD hi]
          have hi' : i ≤ active.length := by simpa [List.length_cons] using Nat.lt_succ_iff.mp hi
          by_cases hil : i = active.length
          · subst hil; simp
          · have hilt : i < active.length := by omega
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by dsimp [wInAct, wActStk]; omega),
              Function.update_of_ne (by omega)]
            exact hAS i hilt
      · simp only [Expr.size]; omega
    · apply Triple.nop
      intro sx ⟨⟨hsx, _⟩, heq⟩
      subst sx
      have hia_t : inAct u = true := by
        cases hfa : inAct u
        · simp [hrTmp1, hfa] at heq
        · rfl
      have hcf : ¬(0 < condVal ∧ inAct u = false) := by simp [hia_t]
      refine ⟨fun _ _ => rfl, ?_, rfl, memFrame_refl _ _ _, ?_, ?_⟩
      · simp [active', hcf, hrAT]
      · intro x hx; dsimp only [inAct']; simp [hcf, hIA x hx]
      · intro i hi; simp only [active', hcf, ↓reduceIte] at hi ⊢; exact hAS i hi
  apply (Triple.cond_const
    (P := fun sx => sx = st0)
    (e := .bin .lt (.const 0) (.reg condReg))
    (val := fun sx => if 0 < sx.regs condReg then 1 else 0)
    (c_t := 20) (c_f := 1)
    (fun sx hsx => by
      subst sx; simp only [Expr.eval, hrCond, h0lt, WordRAM.BinOp.eval]
      by_cases hcmp : 0 < condVal <;> simp [hcmp, h1lt, h0lt])
    (hinner.weaken_pre fun sx ⟨hsx, hne⟩ => by
      have hpos : 0 < condVal := by
        by_contra h0; subst sx; simp [hrCond, h0] at hne
      exact ⟨hsx, hpos⟩)
    ?_).mono_cost (T' := fun _ => 24) (fun _ _ => by simp only [Expr.size]; omega)
  apply Triple.nop
  intro sx ⟨hsx, heq⟩
  subst sx
  have hc0 : ¬(0 < condVal) := by
    intro hlt; simp [hrCond, hlt] at heq
  have hcf : ¬(0 < condVal ∧ inAct u = false) := by simp [hc0]
  refine ⟨fun _ _ => rfl, ?_, rfl, memFrame_refl _ _ _, ?_, ?_⟩
  · simp [active', hcf, hrAT]
  · intro x hx; dsimp only [inAct']; simp [hcf, hIA x hx]
  · intro i hi; simp only [active', hcf, ↓reduceIte] at hi ⊢; exact hAS i hi

def pushPeelIfThetaStmt : Stmt :=
  .cond (.bin .eq (.reg prTmp2) (.reg prTheta))
    (.cond (.bin .lt (.const 0) (.reg prTheta))
      (seqStmts [
        .store (.bin .add (.reg prPeelStk) (.reg prPeelTop)) (.reg prW),
        .assign prPeelTop (.bin .add (.reg prPeelTop) (.const 1))
      ])
      .nop)
    .nop

lemma pushPeelIfThetaStmt_noRand : pushPeelIfThetaStmt.NoRand := by
  refine ⟨⟨?_, by simp [Stmt.NoRand]⟩, by simp [Stmt.NoRand]⟩
  apply seqStmts_noRand
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;> simp [Stmt.NoRand]

lemma pushPeelIfTheta_triple {w : ℕ} {p : Program}
    (workAddr n m H u degVal theta : ℕ) (peel : List ℕ) (st0 : State)
    (hwb : workAddr + pruneWorkSpace n m H < 2 ^ w)
    (hrPS_reg : st0.regs prPeelStk = wPeelStk workAddr n m H)
    (hrW : st0.regs prW = u)
    (hrTmp2 : st0.regs prTmp2 = degVal)
    (hrTheta : st0.regs prTheta = theta)
    (hrPT : st0.regs prPeelTop = peel.length)
    (hlen : (if degVal = theta ∧ 0 < theta then u :: peel else peel).length ≤ n)
    (hu_w : u < 2 ^ w)
    (hPS : ∀ i < peel.length,
      st0.mem (wPeelStk workAddr n m H + i) = peel.getD (peel.length - 1 - i) 0) :
    let peel' := if degVal = theta ∧ 0 < theta then u :: peel else peel
    Triple w p (fun st => st = st0) pushPeelIfThetaStmt
      (normalPost fun st' =>
        (∀ r, r ≠ prPeelTop → st'.regs r = st0.regs r) ∧
        st'.regs prPeelTop = peel'.length ∧
        st'.pos = st0.pos ∧
        MemFrame st0.mem st'.mem (wPeelStk workAddr n m H) (wLvlNext workAddr n m H) ∧
        (∀ i < peel'.length,
          st'.mem (wPeelStk workAddr n m H + i) = peel'.getD (peel'.length - 1 - i) 0))
      (fun _ => 18) := by
  intro peel'
  have h0lt : 0 < 2 ^ w := by unfold pruneWorkSpace at hwb; omega
  have h1lt : 1 < 2 ^ w := by unfold pruneWorkSpace at hwb; omega
  have hinner : Triple w p (fun sx => sx = st0 ∧ degVal = theta)
      (.cond (.bin .lt (.const 0) (.reg prTheta))
        (seqStmts [
          .store (.bin .add (.reg prPeelStk) (.reg prPeelTop)) (.reg prW),
          .assign prPeelTop (.bin .add (.reg prPeelTop) (.const 1))
        ])
        .nop)
      (normalPost fun st' =>
        (∀ r, r ≠ prPeelTop → st'.regs r = st0.regs r) ∧
        st'.regs prPeelTop = peel'.length ∧
        st'.pos = st0.pos ∧
        MemFrame st0.mem st'.mem (wPeelStk workAddr n m H) (wLvlNext workAddr n m H) ∧
        (∀ i < peel'.length,
          st'.mem (wPeelStk workAddr n m H + i) = peel'.getD (peel'.length - 1 - i) 0))
      (fun _ => 14) := by
    apply (Triple.cond_const
      (P := fun sx => sx = st0 ∧ degVal = theta)
      (e := .bin .lt (.const 0) (.reg prTheta))
      (val := fun sx => if 0 < sx.regs prTheta then 1 else 0)
      (c_t := 10) (c_f := 1)
      (fun sx ⟨hsx, _⟩ => by
        subst sx; simp only [Expr.eval, hrTheta, h0lt, WordRAM.BinOp.eval]
        by_cases hcmp : 0 < theta <;> simp [hcmp, h1lt, h0lt])
      ?_ ?_).mono_cost (T' := fun _ => 14) (fun _ _ => by simp only [Expr.size]; omega)
    · intro sx ω ⟨⟨hsx, hdeq⟩, hne⟩
      subst sx
      have hθpos : 0 < theta := by
        by_contra h0; simp [hrTheta, h0] at hne
      have hc : degVal = theta ∧ 0 < theta := ⟨hdeq, hθpos⟩
      have hp_new : peel' = u :: peel := by simp [peel', hc]
      have hpt_len_lt : peel.length < n := by
        have hl := hlen; simp [hc] at hl; omega
      have hpt_addr : wPeelStk workAddr n m H + peel.length < 2 ^ w := by
        unfold pruneWorkSpace at hwb; dsimp [wPeelStk]; omega
      have hpt1_lt : peel.length + 1 < 2 ^ w := by
        unfold pruneWorkSpace at hwb; omega
      refine runs_start_le (T := 10) ?_
      dsimp only [seqStmts]
      apply runs_seq_store_le (x := wPeelStk workAddr n m H + peel.length) (v := u)
      · exact eval_add_regs hrPS_reg hrPT hpt_addr
      · exact eval_reg hrW hu_w
      apply runs_assign_le (v := peel.length + 1)
      · simp [Expr.eval, hrPT, h1lt, WordRAM.BinOp.eval, hpt1_lt]
      · refine ⟨fun r hne' => by simp [Function.update_of_ne hne'], ?_, rfl,
          memFrame_update_in (by dsimp [wHArr, wCur, wAbs, wEx, wDegR, wInAct, wActStk, wPeelStk]; omega) (by dsimp [wPeelStk, wLvlNext]; omega), ?_⟩
        · simp [hp_new]
        · intro i hi
          dsimp only
          rw [hp_new] at hi ⊢
          rw [← stk_push_getD hi]
          have hi' : i ≤ peel.length := by simpa [List.length_cons] using Nat.lt_succ_iff.mp hi
          by_cases hil : i = peel.length
          · subst hil; simp
          · have hilt : i < peel.length := by omega
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hPS i hilt
      · simp only [Expr.size]; omega
    · apply Triple.nop
      intro sx ⟨⟨hsx, _⟩, heq⟩
      subst sx
      have hθ0 : ¬(0 < theta) := by
        intro hpos; simp [hrTheta, hpos] at heq
      have hcf : ¬(degVal = theta ∧ 0 < theta) := by simp [hθ0]
      refine ⟨fun _ _ => rfl, ?_, rfl, memFrame_refl _ _ _, ?_⟩
      · simp [peel', hcf, hrPT]
      · intro i hi; simp only [peel', hcf, ↓reduceIte] at hi ⊢; exact hPS i hi
  apply (Triple.cond_const
    (P := fun sx => sx = st0)
    (e := .bin .eq (.reg prTmp2) (.reg prTheta))
    (val := fun sx => if sx.regs prTmp2 = sx.regs prTheta then 1 else 0)
    (c_t := 14) (c_f := 1)
    (fun sx hsx => by
      subst sx; simp only [Expr.eval, hrTmp2, hrTheta, WordRAM.BinOp.eval]
      by_cases hcmp : degVal = theta <;> simp [hcmp, h1lt, h0lt])
    (hinner.weaken_pre fun sx ⟨hsx, hne⟩ => by
      have hdeq : degVal = theta := by
        by_contra hdne; subst sx; simp [hrTmp2, hrTheta, hdne] at hne
      exact ⟨hsx, hdeq⟩)
    ?_).mono_cost (T' := fun _ => 18) (fun _ _ => by simp only [Expr.size]; omega)
  apply Triple.nop
  intro sx ⟨hsx, heq⟩
  subst sx
  have hdne : degVal ≠ theta := by
    intro hdeq; simp [hrTmp2, hrTheta, hdeq] at heq
  have hcf : ¬(degVal = theta ∧ 0 < theta) := by simp [hdne]
  refine ⟨fun _ _ => rfl, ?_, rfl, memFrame_refl _ _ _, ?_⟩
  · simp [peel', hcf, hrPT]
  · intro i hi; simp only [peel', hcf, ↓reduceIte] at hi ⊢; exact hPS i hi

def removeOneBranchStmt : Stmt :=
  .cond (.bin .lt (.const 0) (.reg prTmp1))
    (seqStmts [
      .assign prTmp2 (.load (.bin .add (.reg prCsrAdjH) (.reg prJ))),
      .assign prIdx (.bin .div (.reg prTmp2) (.const 2)),
      .assign prDir (.bin .mod (.reg prTmp2) (.const 2)),
      .assign prTmp1 (.load (.bin .add (.reg prFlowEnc) (.reg prIdx))),
      .cond (.bin .eq (.reg prDir) (.const 0))
        (.assign prRc (.bin .sub (.bin .mul (.const 2) (.reg prCcap)) (.reg prTmp1)))
        (.assign prRc (.reg prTmp1)),
      .assign prTmp1 (.bin .add (.reg prEx) (.reg prW)),
      .assign prTmp2 (.load (.reg prTmp1)),
      .store (.reg prTmp1) (.bin .add (.reg prTmp2) (.reg prRc)),
      .assign prTmp1 (.load (.bin .add (.reg prInAct) (.reg prW))),
      pushActIfNewStmt prRc,
      .assign prTmp1 (.bin .add (.reg prDegR) (.reg prW)),
      .assign prTmp2 (.load (.reg prTmp1)),
      pushPeelIfThetaStmt,
      .store (.reg prTmp1) (.bin .sub (.reg prTmp2) (.const 1))
    ])
    .nop

lemma removeOneBranchStmt_noRand : removeOneBranchStmt.NoRand := by
  refine ⟨?_, by simp [Stmt.NoRand]⟩
  apply seqStmts_noRand
  intro u hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [Stmt.NoRand]
  · simp [Stmt.NoRand]
  · simp [Stmt.NoRand]
  · simp [Stmt.NoRand]
  · simp [Stmt.NoRand]
  · simp [Stmt.NoRand]
  · simp [Stmt.NoRand]
  · simp [Stmt.NoRand]
  · simp [Stmt.NoRand]
  · exact pushActIfNewStmt_noRand prRc
  · simp [Stmt.NoRand]
  · simp [Stmt.NoRand]
  · exact pushPeelIfThetaStmt_noRand
  · simp [Stmt.NoRand]

def removeOneFromRStmt : Stmt :=
  seqStmts [
    .store (.bin .add (.reg prOutR) (.reg prU)) (.const 0),
    .assign prStart (.load (.bin .add (.reg prCsr) (.reg prU))),
    .assign prTmp1 (.bin .add (.reg prU) (.const 1)),
    .assign prEnd (.load (.bin .add (.reg prCsr) (.reg prTmp1))),
    .assign prJ (.reg prStart),
    .loop (.bin .lt (.reg prJ) (.reg prEnd))
      (seqStmts [
        .assign prW (.load (.bin .add (.reg prCsrAdjV) (.reg prJ))),
        .assign prTmp1 (.load (.bin .add (.reg prOutR) (.reg prW))),
        removeOneBranchStmt,
        .assign prJ (.bin .add (.reg prJ) (.const 1))
      ])
  ]

lemma removeOneFromRStmt_noRand : removeOneFromRStmt.NoRand := by
  apply seqStmts_noRand
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [Stmt.NoRand]
  · simp [Stmt.NoRand]
  · simp [Stmt.NoRand]
  · simp [Stmt.NoRand]
  · simp [Stmt.NoRand]
  · dsimp only [Stmt.NoRand]
    refine ⟨by simp, by simp, removeOneBranchStmt_noRand, by simp⟩

lemma incEdgesAux_eq_csrIncAux' (u k : ℕ) :
    ∀ L : List (ℕ × ℕ), incEdgesAux u k L = csrIncAux u k L
  | [] => rfl
  | (a, b) :: rest => by
      dsimp only [incEdgesAux, csrIncAux]
      have ih := incEdgesAux_eq_csrIncAux' u (k + 1) rest
      by_cases hab : a = b
      · simp [hab, ih]
      · simp only [hab, ↓reduceIte]
        by_cases hau : a = u
        · simp [hau, ih]
        · by_cases hbu : b = u
          · simp [hau, hbu, ih]
          · simp [hau, hbu, ih]

lemma nodup_length_le_range {L : List ℕ} {n : ℕ}
    (hnd : L.Nodup) (hlt : ∀ x ∈ L, x < n) : L.length ≤ n := by
  have hsub : L.toFinset ⊆ Finset.range n := by
    intro x hx
    exact Finset.mem_range.mpr (hlt x (List.mem_toFinset.mp hx))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range, List.toFinset_card_of_nodup hnd] at hcard
  exact hcard


end MinCostFlow.Expander
